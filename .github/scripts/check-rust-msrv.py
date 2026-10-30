#!/usr/bin/env python3
# Copyright (C) 2026 Canonical Ltd.
# SPDX-License-Identifier: GPL-3.0-or-later

"""Check Firefox MSRV and preview a nightly snap compiler-update PR.

Requires Python 3.11+, PyYAML and dpkg. Output is a JSON report; exit status 1
means evidence is unknown, not that Ubuntu packages are missing. No credentials
are needed for public reads. GITHUB_TOKEN may authenticate GitHub API requests.
Only --write in canonical's Actions context enables proposal delivery.
"""

import sys

sys.dont_write_bytecode = True

import argparse
import ast
import difflib
import hashlib
import json
import math
import os
import re
import subprocess
import tomllib
from datetime import datetime, timezone
from email.utils import parsedate_to_datetime
from http.client import HTTPException
from urllib import request
from urllib.error import HTTPError
from urllib.parse import parse_qsl, urlencode, urlsplit

import yaml


FIREFOX = 'https://api.github.com/repos/mozilla-firefox/firefox'
SNAP = 'https://api.github.com/repos/canonical/firefox-snap'
RAW = 'https://raw.githubusercontent.com'
BOOTSTRAP = 'python/mozboot/mozboot/util.py'
ARCHIVE = 'https://api.launchpad.net/devel/ubuntu/+archive/primary'
SERIES = 'https://api.launchpad.net/devel/ubuntu/noble'
ARCHITECTURES = ('amd64', 'arm64')
PROPOSAL_MARKER = '\n<!-- firefox-snap-msrv-proposal: '
BOT = 'github-actions[bot]'


class Unknown(Exception):
    """Evidence does not support a safe conclusion."""


def require(condition, message):
    if not condition:
        raise Unknown(message)


def revision(value):
    require(isinstance(value, str) and re.fullmatch(r'[0-9a-f]{40}', value),
            'Invalid immutable source revision')
    return value


def version(value):
    require(isinstance(value, str) and re.fullmatch(r'(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)', value),
            'Unrecognized full stable Rust version: ' + str(value))
    return tuple(map(int, value.split('.')))


class HTTP:
    def __init__(self, timeout, write=False):
        self.opener = request.build_opener(SameOriginRedirect())
        self.timeout = timeout
        self.cache = {}
        self.headers = {}
        self.observations = []
        self.write = write

    def text(self, url, refresh=False):
        if refresh:
            self.cache.pop(url, None)
        if url not in self.cache:
            parts = urlsplit(url)
            require(parts.scheme == 'https' and parts.netloc in {
                'api.github.com', 'raw.githubusercontent.com', 'ftp.mozilla.org', 'api.launchpad.net'},
                'Evidence URL is outside the permitted HTTPS hosts')
            require(len(self.cache) < 500, 'Evidence request budget exhausted; history is incomplete')
            headers = {'User-Agent': 'firefox-snap-msrv-monitor', 'Cache-Control': 'no-cache'}
            if parts.netloc == 'api.github.com' and os.environ.get('GITHUB_TOKEN'):
                headers['Authorization'] = 'Bearer ' + os.environ['GITHUB_TOKEN']
            with self.opener.open(request.Request(url, headers=headers), timeout=self.timeout) as response:
                body = response.read(8 * 1024 * 1024 + 1)
                require(len(body) <= 8 * 1024 * 1024, 'HTTP response exceeds the evidence size limit')
                now = datetime.now(timezone.utc)
                if parts.netloc == 'api.github.com' or url.startswith(ARCHIVE + '?') or '/latest-mozilla-central/' in url:
                    date = response.headers.get('Date')
                    require(date, 'Mutable evidence has no HTTP Date: ' + url)
                    age = float(response.headers.get('Age', '0'))
                    elapsed = (now - parsedate_to_datetime(date)).total_seconds()
                    require(math.isfinite(age) and age >= 0 and -300 <= elapsed and max(0, elapsed) + age <= 3600,
                            'Mutable evidence is stale or has an invalid timestamp: ' + url)
                self.cache[url] = body.decode('utf-8')
                self.headers[url] = response.headers
                self.observations.append({'url': url, 'observed_at': now.isoformat(),
                    'response_date': response.headers.get('Date'), 'etag': response.headers.get('ETag'),
                    'sha256': hashlib.sha256(body).hexdigest()})
        return self.cache[url]

    def json(self, url, refresh=False):
        return json.loads(self.text(url, refresh=refresh))

    def propose(self, endpoint, data):
        # No arbitrary destination, ref update, force push, merge, or Issue API.
        require(self.write, 'Proposal delivery requires explicit --write')
        write_credentials()
        require(endpoint in ('git/blobs', 'git/trees', 'git/commits', 'git/refs', 'pulls'),
                'Unsupported proposal write endpoint')
        if endpoint == 'git/refs':
            require(re.fullmatch(r'refs/heads/automation/rust-msrv-[0-9]+\.[0-9]+\.[0-9]+', data['ref']),
                    'Refusing to write a non-proposal branch')
        if endpoint == 'pulls':
            require(data['base'] == 'nightly' and re.fullmatch(
                r'automation/rust-msrv-[0-9]+\.[0-9]+\.[0-9]+', data['head']), 'Unexpected PR target')
        headers = {'User-Agent': 'firefox-snap-msrv-monitor', 'Accept': 'application/vnd.github+json',
                   'Content-Type': 'application/json', 'Authorization': 'Bearer ' + os.environ['GITHUB_TOKEN']}
        req = request.Request(SNAP + '/' + endpoint, data=json.dumps(data).encode(), headers=headers, method='POST')
        with self.opener.open(req, timeout=self.timeout) as response:
            body = response.read(8 * 1024 * 1024 + 1)
            require(len(body) <= 8 * 1024 * 1024, 'Proposal response exceeds size limit; reconcile before retrying')
            return json.loads(body)

    def pagination_page(self, first_url, url, visited):
        require(url not in visited and len(visited) < 100, 'Incomplete or cyclic evidence pagination')
        visited.add(url)
        require(urlsplit(url)._replace(query='') == urlsplit(first_url)._replace(query=''),
                'Evidence pagination escaped its endpoint')
        scope = dict(parse_qsl(urlsplit(first_url).query))
        query = dict(parse_qsl(urlsplit(url).query))
        require(all(query.get(key) == value for key, value in scope.items() if key != 'ws.size'),
                'Evidence pagination changed the original query')
        return self.json(url)

    def publications(self, first_url):
        url, count, total, visited = first_url, 0, None, set()
        while url:
            page = self.pagination_page(first_url, url, visited)
            require(isinstance(page, dict) and isinstance(page.get('entries'), list), 'Malformed archive collection')
            require(type(page.get('start')) is int and page['start'] == count, 'Incomplete archive page offset')
            require(type(page.get('total_size')) is int and page['total_size'] >= 0, 'Invalid archive collection size')
            if total is None:
                total = page['total_size']
            require(total == page['total_size'], 'Archive collection changed during pagination')
            count += len(page['entries'])
            require(count <= total, 'Archive collection exceeds its declared size')
            yield from page['entries']
            url = page.get('next_collection_link')
            require(url is None or isinstance(url, str), 'Invalid archive pagination link')
            require(bool(url) == (count < total), 'Archive pagination ended before complete evidence')

    def history(self, first_url):
        url, visited = first_url, set()
        while url:
            entries = self.pagination_page(first_url, url, visited)
            require(isinstance(entries, list), 'Malformed source history')
            yield from entries
            links = re.findall(r'<([^>]+)>;\s*rel="([^"]+)"', self.headers[url].get('Link', ''))
            following = [link for link, rel in links if 'next' in rel.split()]
            require(len(following) <= 1, 'Ambiguous source history pagination')
            url = following[0] if following else None


class SameOriginRedirect(request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        before, after = urlsplit(req.full_url), urlsplit(newurl)
        require((before.scheme, before.netloc) == (after.scheme, after.netloc),
                'Evidence redirect changed origin; refusing to forward credentials')
        return super().redirect_request(req, fp, code, msg, headers, newurl)


def bootstrap_version(text):
    tree = ast.parse(text)
    bindings = [node for node in ast.walk(tree) if isinstance(node, ast.Name)
                and node.id == 'MINIMUM_RUST_VERSION' and isinstance(node.ctx, (ast.Store, ast.Del))]
    assignments = [node for node in tree.body if isinstance(node, ast.Assign)
                   and any(isinstance(target, ast.Name) and target.id == 'MINIMUM_RUST_VERSION'
                           for target in node.targets)]
    require(len(assignments) == 1 and len(bindings) == 1,
            'Expected one unambiguous top-level MINIMUM_RUST_VERSION declaration')
    value = ast.literal_eval(assignments[0].value)
    version(value)
    return value


def declarations(http, sha):
    base = RAW + '/mozilla-firefox/firefox/' + sha + '/'
    minimum = bootstrap_version(http.text(base + BOOTSTRAP))
    cargo = tomllib.loads(http.text(base + 'Cargo.toml'))['workspace']['package']['rust-version']
    require(minimum == cargo, 'Firefox MSRV declarations disagree at ' + sha)
    return minimum


class RecipeLoader(yaml.SafeLoader):
    """Reject duplicate keys instead of silently choosing a recipe setting."""


def recipe_mapping(loader, node):
    pairs = loader.construct_pairs(node, deep=True)
    require(len({key for key, _ in pairs}) == len(pairs), 'Duplicate recipe mapping keys')
    return dict(pairs)


RecipeLoader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, recipe_mapping)


def triggering_commit(http, head, minimum):
    url = FIREFOX + '/commits?' + urlencode({'sha': head, 'path': BOOTSTRAP, 'per_page': 100})
    for entry in http.history(url):
        sha = revision(entry['sha'])
        current = bootstrap_version(http.text(RAW + '/mozilla-firefox/firefox/' + sha + '/' + BOOTSTRAP))
        if current != minimum:
            continue
        details = http.json(FIREFOX + '/commits/' + sha)
        require(len(details['parents']) == 1, 'Ambiguous MSRV history; expected a single parent')
        parent = revision(details['parents'][0]['sha'])
        previous = bootstrap_version(http.text(RAW + '/mozilla-firefox/firefox/' + parent + '/' + BOOTSTRAP))
        if previous != minimum:
            require(declarations(http, sha) == minimum, 'Trigger does not declare the active MSRV')
            require(declarations(http, parent) == previous, 'Parent declarations disagree')
            return {'revision': sha, 'parent_revision': parent, 'previous_msrv': previous,
                    'url': 'https://github.com/mozilla-firefox/firefox/commit/' + sha}
    raise Unknown('Could not establish the commit introducing the active Firefox requirement')


def recipe_baseline(recipe):
    require(isinstance(recipe, dict), 'Expected a snap recipe mapping')
    require(recipe['base'] == 'core24', 'Only the agreed core24/Noble recipe is supported')
    require(recipe.get('build-base', 'core24') == 'core24', 'Unexpected snap build release')
    require(isinstance(recipe.get('parts'), dict)
            and all(isinstance(part, dict) for part in recipe['parts'].values()),
            'Expected recipe parts to be mappings')
    families = set()
    binaries = set()

    def packages(value):
        if isinstance(value, dict):
            for child in value.values():
                packages(child)
        elif isinstance(value, list):
            for child in value:
                packages(child)
        elif isinstance(value, str):
            match = re.fullmatch(r'(rustc|cargo)-([0-9]+\.[0-9]+)(?::[a-z0-9-]+)?', value)
            require(not re.match(r'^(?:rustc|cargo)(?:$|[-:])', value) or match,
                    'Expected explicitly versioned Rust/Cargo recipe packages')
            if match:
                binaries.add(match[1])
                families.add(match[2])

    for part in recipe['parts'].values():
        packages(part.get('build-packages', []))
    require(binaries == {'rustc', 'cargo'}, 'Expected both versioned Rust and Cargo selections')
    selectors = re.findall(r'^[ \t]*rustv=([0-9]+\.[0-9]+)(?:[ \t]+#.*)?[ \t]*$',
                           recipe['parts']['firefox']['override-build'], re.M)
    require(len(selectors) == 1, 'Expected one Rust helper version selector')
    families.update(selectors)
    # Comments are not compiler selections. Keep the executable invocation
    # unambiguous without treating an explanatory old-version comment as one.
    dump_build = recipe['parts']['dump-syms']['override-build']
    dump_build = '\n'.join(line.split(' #', 1)[0] for line in dump_build.splitlines()
                           if not line.lstrip().startswith('#'))
    invocations = re.findall(r'\bcargo-([0-9]+\.[0-9]+)\b', dump_build)
    require(len(invocations) == 1, 'Expected one versioned dump-syms Cargo invocation')
    families.update(invocations)
    require(len(families) == 1, 'Recipe Rust/Cargo selections disagree or are absent')
    family = families.pop()
    version(family + '.0')
    return family


def archive_scope(recipe):
    scope = {arch: {pocket: ['main', 'restricted', 'universe', 'multiverse']
                    for pocket in ('Release', 'Security', 'Updates')} for arch in ARCHITECTURES}
    require(isinstance(recipe.get('package-repositories', []), list), 'Expected a recipe repository list')
    for repository in recipe.get('package-repositories', []):
        require(isinstance(repository, dict) and repository.get('type') == 'apt'
                and repository.get('url') in ('http://ports.ubuntu.com/', 'https://ports.ubuntu.com/')
                and repository.get('architectures') == ['arm64']
                and set(repository.get('components', [])) <= {'main', 'multiverse', 'universe'}
                and set(repository.get('suites', [])) <= {'noble', 'noble-security', 'noble-updates', 'noble-backports'},
                'Recipe archive configuration is outside the agreed boundary')
        if 'noble-backports' in repository.get('suites', []):
            components = set(scope['arm64'].get('Backports', [])) | set(repository.get('components', []))
            scope['arm64']['Backports'] = sorted(components)
    return scope


def ubuntu_version(value):
    match = re.fullmatch(r'(?:[0-9]+:)?([0-9]+\.[0-9]+\.[0-9]+)(?:\+dfsg[0-9A-Za-z.+~]*)?-[0-9A-Za-z.+~]+', value)
    require(match, 'Unrecognized Ubuntu Rust package version: ' + value)
    return match[1]


def newer_package(left, right):
    result = subprocess.run(['dpkg', '--compare-versions', left, 'gt', right],
                            capture_output=True, check=False)
    require(result.returncode in (0, 1), 'Cannot compare Ubuntu package revisions')
    return result.returncode == 0


def archive_availability(http, report, minimum, baseline, scope):
    archive = {'series': 'noble', 'architectures': list(ARCHITECTURES),
               'allowed_pockets': {arch: list(scope[arch]) for arch in ARCHITECTURES},
               'allowed_components': scope, 'queries': [], 'publications': {},
               'suitable_publications': {}}
    report['archive'] = archive
    packages = archive['publications']
    suitable = archive['suitable_publications']
    for arch in ARCHITECTURES:
        packages[arch] = {}
        suitable[arch] = {}
        for binary in ('rustc', 'cargo'):
            url = ARCHIVE + '?' + urlencode({'ws.op': 'getPublishedBinaries',
                'binary_name': binary + '-', 'exact_match': 'false', 'status': 'Published',
                'distro_arch_series': SERIES + '/' + arch, 'ws.size': 100})
            archive['queries'].append(url)
            packages[arch][binary] = {}
            suitable[arch][binary] = {}
            for entry in http.publications(url):
                match = re.fullmatch(binary + r'-([0-9]+\.[0-9]+)', entry['binary_package_name'])
                if not match:
                    continue
                if (entry['archive_link'] != ARCHIVE or entry['distro_arch_series_link'] != SERIES + '/' + arch
                        or entry['status'] != 'Published' or entry['pocket'] not in scope[arch]
                        or entry['component_name'] not in scope[arch][entry['pocket']]):
                    continue
                family = match[1]
                require(entry['source_package_name'] == 'rustc-' + family,
                        'Unexpected Rust/Cargo source-package mapping')
                require(entry['source_package_version'] == entry['binary_package_version'],
                        'Rust/Cargo source and binary versions disagree')
                upstream = ubuntu_version(entry['binary_package_version'])
                require(version(upstream)[:2] == version(family + '.0')[:2], 'Package family/version disagree')
                require(entry['date_published'], 'Publication lacks a timestamp')
                published = datetime.fromisoformat(entry['date_published'])
                require(published.tzinfo is not None
                        and (published - datetime.now(timezone.utc)).total_seconds() <= 300,
                        'Invalid publication timestamp')
                publication = {
                    'name': entry['binary_package_name'], 'version': entry['binary_package_version'],
                    'upstream_version': upstream, 'source_package': entry['source_package_name'],
                    'pocket': entry['pocket'], 'published_at': entry['date_published'],
                    'url': entry['self_link']}
                indexes = [packages[arch][binary]]
                if version(upstream) >= version(minimum):
                    indexes.append(suitable[arch][binary])
                for index in indexes:
                    previous = index.get(family)
                    if previous is None or newer_package(publication['version'], previous['version']):
                        index[family] = publication
    eligible = set(suitable['amd64']['rustc'])
    for arch in ARCHITECTURES:
        for binary in ('rustc', 'cargo'):
            eligible.intersection_update(suitable[arch][binary])
    if baseline in eligible:
        report['outcome'] = 'no-update-needed'
        report['summary'] = 'Published patches of the selected snap compiler family satisfy the requirement.'
    elif eligible:
        family = max(eligible, key=lambda value: version(value + '.0'))
        archive['selected'] = {'family': family, 'packages': {
            arch: {binary: suitable[arch][binary][family] for binary in ('rustc', 'cargo')}
            for arch in ARCHITECTURES}}
        report['outcome'] = 'compiler-available'
        report['summary'] = 'A higher suitable compiler family is published for both required architectures.'
    else:
        report['outcome'] = 'publication-gap'
        report['summary'] = 'No suitable published Rust/Cargo family covers both required architectures.'


def observe(http, report):
    head = revision(http.json(FIREFOX + '/branches/main')['commit']['sha'])
    minimum = declarations(http, head)
    report['source'] = {'repository': 'mozilla-firefox/firefox', 'branch': 'main',
                        'revision': head, 'msrv': minimum,
                        'declaration_urls': [RAW + '/mozilla-firefox/firefox/' + head + '/' + path
                                             for path in (BOOTSTRAP, 'Cargo.toml')]}
    report['source']['trigger'] = triggering_commit(http, head, minimum)
    snap_head = revision(http.json(SNAP + '/branches/nightly')['commit']['sha'])
    recipe_url = RAW + '/canonical/firefox-snap/' + snap_head + '/snapcraft.yaml'
    recipe = yaml.load(http.text(recipe_url), Loader=RecipeLoader)
    family = recipe_baseline(recipe)
    scope = archive_scope(recipe)
    report['snap'] = {'repository': 'canonical/firefox-snap', 'branch': 'nightly',
                      'revision': snap_head, 'recipe_url': recipe_url,
                      'compiler_family': family, 'compiler_version_lower_bound': family + '.0'}
    nightly_url = ('https://ftp.mozilla.org/pub/firefox/nightly/latest-mozilla-central/firefox-'
                   + recipe['version'] + '.en-US.linux-x86_64.txt')
    lines = http.text(nightly_url).strip().splitlines()
    require(len(lines) == 2 and re.fullmatch(r'[0-9]{14}', lines[0]), 'Invalid published-nightly metadata')
    require(lines[1].startswith('https://hg.mozilla.org/mozilla-central/rev/'), 'Unexpected nightly source repository')
    report['published_nightly'] = {'build_id': lines[0], 'revision': revision(lines[1].rsplit('/', 1)[1]),
                                    'revision_system': 'mercurial', 'metadata_url': nightly_url,
                                    'note': 'Published source context, not proof this central requirement has reached the snap.'}
    if version(family + '.0') >= version(minimum):
        report['outcome'] = 'no-update-needed'
        report['summary'] = 'The snap compiler baseline already satisfies the active Firefox requirement.'
    else:
        archive_availability(http, report, minimum, family, scope)


def write_credentials():
    require(os.environ.get('GITHUB_ACTIONS') == 'true'
            and os.environ.get('GITHUB_REPOSITORY') == 'canonical/firefox-snap',
            '--write requires canonical/firefox-snap GitHub Actions; local previews are read-only')
    require(os.environ.get('GITHUB_TOKEN', '').startswith('ghs_'),
            '--write requires the job-scoped GITHUB_TOKEN, not a personal token or repository-token fallback')


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def update_recipe(text, old, new):
    """Edit source spans, never round-trip/reformat YAML or replace globally."""
    require(not any(isinstance(token, (yaml.tokens.AnchorToken, yaml.tokens.AliasToken))
                    for token in yaml.scan(text)), 'Recipe anchors/aliases require manual review')
    root = yaml.compose(text, Loader=RecipeLoader)
    edits = []

    def field(node, key):
        require(isinstance(node, yaml.MappingNode), 'Unexpected recipe mapping structure')
        values = [value for name, value in node.value if name.value == key]
        require(len(values) == 1, 'Expected one recipe field: ' + key)
        return values[0]

    def packages(node, allowed):
        if isinstance(node, yaml.MappingNode):
            for _, value in node.value:
                packages(value, allowed)
        elif isinstance(node, yaml.SequenceNode):
            for value in node.value:
                packages(value, allowed)
        elif isinstance(node, yaml.ScalarNode):
            match = re.fullmatch(r'(rustc|cargo)-' + re.escape(old) + r'(?::[a-z0-9-]+)?', node.value)
            if match:
                require(match[1] in allowed, 'Unexpected compiler package in recipe part')
                raw = text[node.start_mark.index:node.end_mark.index]
                token = re.fullmatch(r'''(['"]?)(?:rustc|cargo)-(''' + re.escape(old)
                                     + r''')(?::[a-z0-9-]+)?\1''', raw)
                require(token, 'Unexpected compiler package spelling')
                edits.append((node.start_mark.index + token.start(2),
                              node.start_mark.index + token.end(2), new))

    parts = field(root, 'parts')
    for name, allowed in (('dump-syms', {'cargo'}), ('firefox', {'rustc', 'cargo'})):
        part = field(parts, name)
        before = len(edits)
        packages(field(part, 'build-packages'), allowed)
        require(len(edits) > before, 'Missing compiler packages in ' + name)
        build = field(part, 'override-build')
        require(isinstance(build, yaml.ScalarNode) and build.style == '|',
                'Expected a literal build script in ' + name)
        raw = text[build.start_mark.index:build.end_mark.index]
        if name == 'dump-syms':
            pattern = (r'^[ \t]*cargo-(' + re.escape(old)
                       + r')(?=[ \t]+build[ \t]+--release(?:[ \t]+#.*)?[ \t]*$)')
        else:
            pattern = r'^[ \t]*rustv=(' + re.escape(old) + r')(?=(?:[ \t]+#.*)?[ \t]*$)'
            for helper in ('rustc-${rustv}', 'rust-${rustv}-clang', 'rust-${rustv}-lld',
                           'rust-${rustv}-llvm-dwp', 'cargo-${rustv}'):
                require(raw.count('/usr/bin/' + helper) == 1, 'Unexpected compiler/helper aliases')
        matches = list(re.finditer(pattern, raw, re.M))
        require(len(matches) == 1, 'Expected one compiler invocation/selector in ' + name)
        match = matches[0]
        edits.append((build.start_mark.index + match.start(1), build.start_mark.index + match.end(1), new))
    updated = text
    for start, end, value in sorted(edits, reverse=True):
        updated = updated[:start] + value + updated[end:]
    require(recipe_baseline(yaml.load(updated, Loader=RecipeLoader)) == new,
            'Recipe contains uncoordinated compiler selections')
    return updated


def proposal_content(report, original, updated):
    minimum = report['source']['msrv']
    old, new = report['snap']['compiler_family'], report['archive']['selected']['family']
    title = 'Update nightly Rust from ' + old + ' to ' + new + ' for Firefox MSRV ' + minimum
    lines = ['## Summary', '', '```diff', '- nightly snap compiler: ' + old,
             '+ nightly snap compiler: ' + new, '```', '',
             'Coordinate dump-syms Cargo, Firefox Rust/Cargo packages and compiler/helper aliases.', '',
             '## Evidence', '',
             '- **Before:** snap compiler baseline ' + old + ' does not establish Firefox MSRV ' + minimum + '.',
             '  Snap recipe: ' + report['snap']['recipe_url'],
             '- **After:** official Ubuntu Noble Rust/Cargo binary publications cover amd64 and arm64.',
             '- Triggering Firefox commit: ' + report['source']['trigger']['url'],
             '- Pinned central declarations: ' + ' ; '.join(report['source']['declaration_urls']),
             '- Observed at: ' + report['observed_at'],
             '- Published-nightly source context: ' + report['published_nightly']['metadata_url'],
             '  Mercurial revision: ' + report['published_nightly']['revision'] + '.',
             '  Preparatory central work; this is not proof of a failure in a published snap.', '']
    for arch, binaries in report['archive']['selected']['packages'].items():
        for binary, publication in binaries.items():
            url = publication['url']
            require(isinstance(url, str) and re.fullmatch(re.escape(ARCHIVE) + r'/\+binarypub/[A-Za-z0-9]+', url),
                    'Unexpected binary-publication evidence URL')
            lines.append('- ' + arch + ' ' + binary + ': `' + publication['version'] + '` ('
                         + publication['pocket'] + '), published ' + publication['published_at'] + ': ' + url)
    lines.extend(['', '**No package installation or Firefox build tests were performed.**', '',
                  '## Merge Danger', '', '**Door:** two-way', '',
                  'A reviewed recipe change can be reverted; this PR does not merge or publish a snap.', '',
                  '**Blast Radius:** nightly', '',
                  'Package publication is not proof of installation or build compatibility.', ''])
    public = '\n'.join(lines)
    metadata = {'schema': 1, 'need': 'canonical/firefox-snap:nightly:rust-' + minimum,
                'base': report['snap']['revision'], 'original_sha256': digest(original),
                'recipe_sha256': digest(updated), 'title': title, 'body_sha256': digest(public),
                'evidence': {key: report[key] for key in ('observed_at', 'source', 'snap', 'published_nightly')},
                'archive': report['archive']['selected']}
    return title, public, metadata


def proposal_body(public, metadata):
    return public + PROPOSAL_MARKER + json.dumps(metadata, sort_keys=True) + ' -->'


def reconcile_proposal(http, proposal):
    # Scan all states (not search's eventually consistent index), retaining closed
    # work and checking markers as well as deterministic branch identity.
    url = SNAP + '/pulls?' + urlencode({'state': 'all', 'per_page': 100})
    matches = []
    for pull in http.history(url):
        require(isinstance(pull, dict) and isinstance(pull.get('head'), dict)
                and isinstance(pull['head'].get('ref'), str), 'Malformed PR collection entry')
        body = pull.get('body') or ''
        metadata = None
        if PROPOSAL_MARKER in body:
            try:
                metadata = json.loads(body.split(PROPOSAL_MARKER, 1)[1].split(' -->', 1)[0])
            except (ValueError, TypeError):
                require(pull['head']['ref'] == proposal['branch'],
                        'Corrupt proposal metadata; manual recovery required')
            require(metadata is None or isinstance(metadata, dict), 'Malformed proposal metadata')
        if (pull['head']['ref'] == proposal['branch']
                or metadata and metadata.get('need') == proposal['need']):
            matches.append(pull)
    require(len(matches) <= 1, 'Multiple matching PRs; manual recovery required')
    if not matches:
        return False
    pull = matches[0]
    require(type(pull['number']) is int and pull['number'] > 0, 'Invalid proposal PR number')
    pull = http.json(SNAP + '/pulls/' + str(pull['number']), refresh=True)
    require(pull['html_url'] == 'https://github.com/canonical/firefox-snap/pull/' + str(pull['number']),
            'Invalid existing PR identity')
    proposal['url'] = pull['html_url']
    proposal['number'] = pull['number']
    proposal['status'] = 'held'
    proposal['reason'] = 'Existing work is closed, modified or no longer matches; no automatic edits or recreation.'
    try:
        public, encoded = pull['body'].split(PROPOSAL_MARKER)
        metadata = json.loads(encoded.removesuffix(' -->'))
        intact = (metadata['schema'] == 1 and metadata['need'] == proposal['need']
                  and pull['user']['login'] == BOT and pull['head']['repo']['full_name'] == 'canonical/firefox-snap'
                  and pull['base']['repo']['full_name'] == 'canonical/firefox-snap' and pull['base']['ref'] == 'nightly'
                  and pull['head']['ref'] == proposal['branch'] and pull['head']['sha'] == metadata['head']
                  and pull['title'] == metadata['title'] and digest(public) == metadata['body_sha256']
                  and metadata['archive']['family'] == proposal['compiler_family'])
        if intact and pull['state'] == 'open':
            proposal['status'] = 'existing'
            proposal['reason'] = 'Reuse intact existing proposal; no branch or PR updates.'
            proposal['retained_metadata'] = metadata
            proposal.update(body=pull['body'], title=pull['title'], head=pull['head']['sha'])
    except (ValueError, TypeError, KeyError, AttributeError):
        pass  # Human-owned or damaged work is not ours to overwrite.
    return True


def prepare_proposal(http, report, write):
    # Re-observe the snap if another updater changed it during archive lookup.
    # Immutable source evidence and still-fresh archive responses remain pinned.
    current = revision(http.json(SNAP + '/branches/nightly', refresh=True)['commit']['sha'])
    if current != report['snap']['revision']:
        report.pop('archive', None)
        observe(http, report)
        if report['outcome'] != 'compiler-available':
            return
    original = http.text(report['snap']['recipe_url'])
    updated = update_recipe(original, report['snap']['compiler_family'], report['archive']['selected']['family'])
    title, public, metadata = proposal_content(report, original, updated)
    proposal = {'need': metadata['need'], 'branch': 'automation/rust-msrv-' + report['source']['msrv'],
                'compiler_family': report['archive']['selected']['family'],
                'base': 'nightly', 'repository': 'canonical/firefox-snap', 'title': title,
                'body': proposal_body(public, metadata), 'status': 'preview',
                'diff': ''.join(difflib.unified_diff(original.splitlines(keepends=True), updated.splitlines(keepends=True),
                                                   fromfile='a/snapcraft.yaml', tofile='b/snapcraft.yaml'))}
    report['proposal'] = proposal
    if reconcile_proposal(http, proposal):
        return
    ref_url = SNAP + '/git/ref/heads/' + proposal['branch']
    try:
        http.json(ref_url)
    except HTTPError as error:
        if error.code != 404:
            raise
        error.close()
    else:
        raise Unknown('Proposal branch exists without an identifiable PR; manual recovery required')
    base = report['snap']['revision']
    commit = http.json(SNAP + '/git/commits/' + base)
    tree = revision(commit['tree']['sha'])
    entries = http.json(SNAP + '/git/trees/' + tree)
    require(entries['truncated'] is False, 'Incomplete snap base tree')
    recipes = [entry for entry in entries['tree'] if entry['path'] == 'snapcraft.yaml']
    original_bytes = original.encode()
    original_blob = hashlib.sha1(b'blob ' + str(len(original_bytes)).encode() + b'\0' + original_bytes).hexdigest()
    require(len(recipes) == 1 and recipes[0]['type'] == 'blob' and recipes[0]['mode'] == '100644'
            and recipes[0]['sha'] == original_blob, 'Unexpected recipe mode or base blob; manual review required')
    if not write:
        return
    blob = revision(http.propose('git/blobs', {'content': updated, 'encoding': 'utf-8'})['sha'])
    tree = revision(http.propose('git/trees', {'base_tree': tree, 'tree': [
        {'path': 'snapcraft.yaml', 'mode': '100644', 'type': 'blob', 'sha': blob}]})['sha'])
    # Omit author/committer so GitHub supplies the authenticated identity. Verify
    # it BEFORE publishing a ref; another App's token must not trigger the importer.
    commit = http.propose('git/commits', {'message': title, 'tree': tree, 'parents': [base]})
    require(commit['author']['name'] == BOT and commit['committer']['name'] == BOT,
            'Authenticated commit is not github-actions[bot]; refusing to publish a branch')
    head = revision(commit['sha'])
    metadata['head'] = head
    proposal['body'] = proposal_body(public, metadata)
    proposal['head'] = head
    require(revision(http.json(SNAP + '/branches/nightly', refresh=True)['commit']['sha']) == base,
            'Nightly changed during proposal preparation; rerun against the new base')
    # Creation is atomic and never replaces an existing ref. Ambiguous failures
    # stop here; the next invocation reconciles PRs/refs instead of retrying POST.
    http.propose('git/refs', {'ref': 'refs/heads/' + proposal['branch'], 'sha': head})
    proposal['status'] = 'branch-created'
    require(http.json(ref_url, refresh=True)['object']['sha'] == head,
            'Proposal branch changed before PR creation; manual reconciliation required')
    pull = http.propose('pulls', {'title': title, 'body': proposal['body'], 'base': 'nightly',
                                 'head': proposal['branch'], 'maintainer_can_modify': False})
    require(type(pull['number']) is int and pull['number'] > 0
            and pull['html_url'] == 'https://github.com/canonical/firefox-snap/pull/' + str(pull['number'])
            and pull['head']['sha'] == head and pull['base']['ref'] == 'nightly',
            'PR response is not durably identifiable; reconcile before retrying')
    proposal.update(status='created', number=pull['number'], url=pull['html_url'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=float, default=30, help='HTTP timeout in seconds (default: 30)')
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--dry-run', action='store_true', help='Read-only preview (the default)')
    mode.add_argument('--write', action='store_true', help='Propose a PR using canonical\'s Actions job token')
    args = parser.parse_args()
    if not math.isfinite(args.timeout) or args.timeout <= 0:
        parser.error('HTTP timeout must be finite and positive')
    report = {'outcome': 'unknown', 'observed_at': datetime.now(timezone.utc).isoformat(),
              'inspection': 'Read-only metadata; no installation or build tests performed.'}
    http = HTTP(args.timeout, write=args.write)
    try:
        if args.write:
            write_credentials()
        observe(http, report)
        if report['outcome'] == 'compiler-available':
            prepare_proposal(http, report, args.write)
    except (Unknown, OSError, HTTPException, ValueError, TypeError, KeyError, SyntaxError, yaml.YAMLError) as error:
        report['outcome'] = 'unknown'
        report['summary'] = 'Check or delivery stopped safely; inspect the error and retained evidence before retrying.'
        report['error'] = str(error)
    report['observations'] = http.observations
    print(json.dumps(report, indent=2))
    return 1 if report['outcome'] == 'unknown' else 0


if __name__ == '__main__':
    sys.exit(main())
