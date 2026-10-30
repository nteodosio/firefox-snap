"""Exercise the complete monitor command with recorded, disposable HTTP I/O."""

import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import runpy
import sys
import unittest
from datetime import datetime, timezone
from email.message import Message
from email.utils import format_datetime
from http.client import IncompleteRead
from unittest import mock
from urllib.error import HTTPError
from urllib.parse import parse_qsl, urlencode, urlsplit, urlunsplit

import yaml  # Load before running the command under the no-write guard.


COMMAND_RUNNING = False


def reject_writes(event, args):
    if not COMMAND_RUNNING:
        return
    if event == 'open':
        path, mode, flags = args
        if not isinstance(path, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC):
            raise AssertionError('Monitor attempted a filesystem write: ' + str(path))
    elif event in ('os.mkdir', 'os.remove', 'os.rename', 'os.rmdir', 'os.chmod',
                   'os.chown', 'os.link', 'os.symlink', 'os.truncate'):
        raise AssertionError('Monitor attempted a filesystem mutation: ' + event)
    elif event == 'subprocess.Popen':
        require_args = args[1]
        if require_args[:2] != ['dpkg', '--compare-versions']:
            raise AssertionError('Monitor attempted a command other than version comparison')


sys.addaudithook(reject_writes)


SCRIPT = Path(__file__).resolve().parents[1] / 'check-rust-msrv.py'
FIREFOX = 'https://api.github.com/repos/mozilla-firefox/firefox'
SNAP = 'https://api.github.com/repos/canonical/firefox-snap'
RAW = 'https://raw.githubusercontent.com'
BOOTSTRAP = 'python/mozboot/mozboot/util.py'
HEAD, TRIGGER, PARENT, SNAP_HEAD, NIGHTLY = [c * 40 for c in 'abcde']
ARCHIVE = 'https://api.launchpad.net/devel/ubuntu/+archive/primary'
SERIES = 'https://api.launchpad.net/devel/ubuntu/noble'


def archive_url(arch, binary):
    return ARCHIVE + '?' + urlencode({'ws.op': 'getPublishedBinaries',
        'binary_name': binary + '-', 'exact_match': 'false', 'status': 'Published',
        'distro_arch_series': SERIES + '/' + arch, 'ws.size': 100})


def canonical_url(url):
    parts = urlsplit(url)
    return urlunsplit(parts._replace(query=urlencode(sorted(parse_qsl(parts.query)))))


class Response(io.BytesIO):
    def __init__(self, body, headers=None):
        super().__init__(body)
        self.headers = Message()
        self.headers['Date'] = format_datetime(datetime.now(timezone.utc), usegmt=True)
        for key, value in (headers or {}).items():
            self.headers.replace_header(key, value) if key in self.headers else self.headers.add_header(key, value)


class RecordedHTTP:
    def __init__(self):
        self.responses = {}
        self.requests = []
        self.authorization = []
        self.writes = []
        self.allow_writes = False
        self.commit_identity = 'github-actions[bot]'
        self.sequences = {}

    def sequence(self, url, *bodies):
        self.sequences[canonical_url(url)] = list(bodies)

    def add(self, url, body, headers=None):
        if not isinstance(body, str):
            body = json.dumps(body)
        self.responses[canonical_url(url)] = (body.encode(), headers)

    def open(self, request, *args, **kwargs):
        if isinstance(request, str):
            method, url = 'GET', request
        else:
            method, url = request.get_method(), request.full_url
        self.requests.append(url)
        self.authorization.append((url, request.get_header('Authorization') if not isinstance(request, str) else None))
        if method != 'GET':
            if not self.allow_writes:
                raise AssertionError('The read-only monitor attempted ' + method)
            return self.propose(method, url, json.loads(request.data))
        key = canonical_url(url)
        if key in self.sequences:
            bodies = self.sequences[key]
            body = bodies.pop(0) if len(bodies) > 1 else bodies[0]
            return Response(json.dumps(body).encode())
        if key not in self.responses:
            if url.startswith(SNAP + '/git/ref/heads/automation/rust-msrv-'):
                raise HTTPError(url, 404, 'Not Found', {}, None)
            raise AssertionError('Unrecorded HTTP request: ' + url)
        body, headers = self.responses[key]
        if isinstance(body, Exception):
            raise body
        return Response(body, headers)

    def propose(self, method, url, data):
        if method != 'POST' or url not in [SNAP + '/' + endpoint for endpoint in (
                'git/blobs', 'git/trees', 'git/commits', 'git/refs', 'pulls')]:
            raise AssertionError('Unexpected proposal write: ' + method + ' ' + url)
        self.writes.append((url, data))
        if canonical_url(url) in self.responses:
            body, headers = self.responses[canonical_url(url)]
            if isinstance(body, Exception):
                raise body
            return Response(body, headers)
        sha = hashlib.sha1(json.dumps(data, sort_keys=True).encode()).hexdigest()
        result = {'sha': sha}
        if url.endswith('/git/commits'):
            result.update(author={'name': self.commit_identity}, committer={'name': self.commit_identity})
        elif url.endswith('/git/refs'):
            ref_url = SNAP + '/git/ref/' + data['ref'].removeprefix('refs/')
            if canonical_url(ref_url) in self.responses:
                raise HTTPError(url, 422, 'Reference already exists', {}, None)
            result = {'ref': data['ref'], 'object': {'sha': data['sha'], 'type': 'commit'}}
            self.add(ref_url, result)
        elif url.endswith('/pulls'):
            head = json.loads(self.responses[canonical_url(SNAP + '/git/ref/heads/' + data['head'])][0])['object']['sha']
            result = {'number': 41, 'html_url': 'https://github.com/canonical/firefox-snap/pull/41',
                      'state': 'open', 'title': data['title'], 'body': data['body'],
                      'user': {'login': 'github-actions[bot]'},
                      'head': {'ref': data['head'], 'sha': head, 'repo': {'full_name': 'canonical/firefox-snap'}},
                      'base': {'ref': data['base'], 'repo': {'full_name': 'canonical/firefox-snap'}}}
            self.add(SNAP + '/pulls?' + urlencode({'state': 'all', 'per_page': 100}), [result])
            self.add(SNAP + '/pulls/41', result)
        return Response(json.dumps(result).encode())


class MonitorCommandTests(unittest.TestCase):
    def setUp(self):
        self.http = RecordedHTTP()
        self.publications = {arch: {binary: [] for binary in ('rustc', 'cargo')}
                             for arch in ('amd64', 'arm64')}
        self.recipe = (Path(__file__).parent / 'fixtures/nightly-snapcraft.yaml').read_text().replace('1.91', '1.95')
        self.http.add(SNAP + '/branches/nightly', {'commit': {'sha': SNAP_HEAD}})
        self.http.add(SNAP + '/pulls?' + urlencode({'state': 'all', 'per_page': 100}), [])
        self.http.add(SNAP + '/git/commits/' + SNAP_HEAD, {'tree': {'sha': 'f' * 40}})
        self.http.add(FIREFOX + '/branches/main', {'commit': {'sha': HEAD}})
        self.declarations(HEAD, '1.94.0')
        self.declarations(TRIGGER, '1.94.0')
        self.declarations(PARENT, '1.90.0')
        history = FIREFOX + '/commits?' + urlencode({'sha': HEAD, 'path': BOOTSTRAP, 'per_page': 100})
        self.http.add(history, [{'sha': TRIGGER}])
        self.http.add(FIREFOX + '/commits/' + TRIGGER, {'sha': TRIGGER, 'parents': [{'sha': PARENT}]})
        self.http.add('https://ftp.mozilla.org/pub/firefox/nightly/latest-mozilla-central/firefox-161.0a1.en-US.linux-x86_64.txt',
                      '20261027091753\nhttps://hg.mozilla.org/mozilla-central/rev/' + NIGHTLY + '\n')

    def publish(self, family, package_version, arches=('amd64', 'arm64'), binaries=('rustc', 'cargo'), **fields):
        for arch in arches:
            for binary in binaries:
                records = self.publications[arch][binary]
                record = {'self_link': ARCHIVE + '/+binarypub/' + arch + binary + str(len(records)),
                          'binary_package_name': binary + '-' + family,
                          'binary_package_version': package_version,
                          'source_package_name': 'rustc-' + family,
                          'source_package_version': package_version,
                          'distro_arch_series_link': SERIES + '/' + arch,
                          'archive_link': ARCHIVE, 'status': 'Published', 'pocket': 'Updates',
                          'component_name': 'universe', 'date_published': '2026-06-04T19:33:00+00:00'}
                record.update(fields)
                records.append(record)

    def declarations(self, revision, version):
        base = RAW + '/mozilla-firefox/firefox/' + revision + '/'
        self.http.add(base + BOOTSTRAP, 'MINIMUM_RUST_VERSION = "' + version + '"\n')
        self.http.add(base + 'Cargo.toml', '[workspace.package]\nrust-version = "' + version + '"\n')

    def base_tree(self, tree_sha, recipe, **fields):
        raw = recipe.encode()
        entry = {'path': 'snapcraft.yaml', 'mode': '100644', 'type': 'blob',
                 'sha': hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()}
        entry.update(fields)
        self.http.add(SNAP + '/git/trees/' + tree_sha, {'truncated': False, 'tree': [entry]})

    def command(self, *args, environment=None):
        global COMMAND_RUNNING
        self.http.add(RAW + '/canonical/firefox-snap/' + SNAP_HEAD + '/snapcraft.yaml', self.recipe)
        if canonical_url(SNAP + '/git/trees/' + 'f' * 40) not in self.http.responses:
            self.base_tree('f' * 40, self.recipe)
        for arch, binaries in self.publications.items():
            for binary, records in binaries.items():
                url = archive_url(arch, binary)
                if canonical_url(url) not in self.http.responses:
                    self.http.add(url, {'start': 0, 'total_size': len(records), 'entries': records})
        output = io.StringIO()
        env = {'GITHUB_TOKEN': 'fixture-token', 'GITHUB_ACTIONS': 'false', 'GITHUB_REPOSITORY': ''}
        self.http.allow_writes = '--write' in args
        if self.http.allow_writes:
            env.update(GITHUB_TOKEN='ghs_fixture_job_token', GITHUB_ACTIONS='true', GITHUB_REPOSITORY='canonical/firefox-snap')
        env.update(environment or {})
        with mock.patch.object(sys, 'argv', [str(SCRIPT), *args]), \
             mock.patch.object(sys, 'dont_write_bytecode', True), \
             mock.patch.dict(os.environ, env), \
             mock.patch('urllib.request.OpenerDirector.open', side_effect=self.http.open), \
             contextlib.redirect_stdout(output):
            COMMAND_RUNNING = True
            try:
                runpy.run_path(str(SCRIPT), run_name='__main__')
            except SystemExit as error:
                status = error.code
            else:
                status = 0
            finally:
                COMMAND_RUNNING = False
        return status, json.loads(output.getvalue())

    def test_sufficient_baseline_reports_no_update_with_pinned_evidence(self):
        status, report = self.command()
        self.assertEqual(status, 0)
        self.assertEqual(report['outcome'], 'no-update-needed')
        self.assertEqual(report['source']['msrv'], '1.94.0')
        self.assertEqual(report['source']['revision'], HEAD)
        self.assertEqual(report['source']['trigger']['revision'], TRIGGER)
        self.assertEqual(report['snap']['revision'], SNAP_HEAD)
        self.assertEqual(report['snap']['compiler_family'], '1.95')
        self.assertEqual(report['published_nightly']['revision'], NIGHTLY)
        self.assertIn('observed_at', report)

    def test_existing_shortfall_selects_highest_family_covering_both_architectures(self):
        self.recipe = self.recipe.replace('1.95', '1.91')
        self.publish('1.94', '1.94.1+dfsg-1ubuntu1')
        self.publish('1.95', '1.95.0+dfsg-0ubuntu0.24.04.9')
        self.publish('1.95', '1.95.0+dfsg-0ubuntu0.24.04.10')
        self.publish('1.96', '1.96.0+dfsg-1ubuntu1', arches=('amd64',))
        status, report = self.command()
        self.assertEqual(status, 0)
        self.assertEqual(report['outcome'], 'compiler-available')
        selected = report['archive']['selected']
        self.assertEqual(selected['family'], '1.95')
        for arch in ('amd64', 'arm64'):
            self.assertEqual(selected['packages'][arch]['rustc']['version'],
                             '1.95.0+dfsg-0ubuntu0.24.04.10')

    def test_candidate_on_a_later_publication_page_is_not_reported_missing(self):
        self.recipe = self.recipe.replace('1.95', '1.91')
        self.publish('1.93', '1.93.0+dfsg-1ubuntu1', arches=('amd64',), binaries=('rustc',))
        self.publish('1.95', '1.95.0+dfsg-1ubuntu1')
        url = archive_url('amd64', 'rustc')
        following = url + '&ws.start=1'
        records = self.publications['amd64']['rustc']
        self.http.add(url, {'start': 0, 'total_size': 2, 'entries': records[:1],
                            'next_collection_link': following})
        self.http.add(following, {'start': 1, 'total_size': 2, 'entries': records[1:]})
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (0, 'compiler-available'))
        self.assertEqual(report['archive']['selected']['family'], '1.95')

    def test_trigger_history_is_pinned_and_paginated_past_unrelated_source_edits(self):
        history = FIREFOX + '/commits?' + urlencode({'sha': HEAD, 'path': BOOTSTRAP, 'per_page': 100})
        following = history + '&page=2'
        self.http.add(history, [{'sha': HEAD}], {'Link': '<' + following + '>; rel="next"'})
        self.http.add(FIREFOX + '/commits/' + HEAD, {'sha': HEAD, 'parents': [{'sha': TRIGGER}]})
        self.http.add(following, [{'sha': TRIGGER}])
        status, report = self.command()
        self.assertEqual(status, 0)
        self.assertEqual(report['source']['trigger']['revision'], TRIGGER)
        self.assertEqual(report['source']['trigger']['previous_msrv'], '1.90.0')

    def test_stale_archive_response_is_unknown_not_availability_or_absence(self):
        self.recipe = self.recipe.replace('1.95', '1.91')
        self.http.add(archive_url('amd64', 'rustc'),
                      {'start': 0, 'total_size': 0, 'entries': []},
                      {'Date': 'Sat, 01 Jan 2000 00:00:00 GMT'})
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertIn('stale', report['error'].lower())

    def test_removed_arm64_backports_source_cannot_qualify_a_compiler(self):
        self.recipe = self.recipe.replace('1.95', '1.91').replace(', noble-backports', '')
        self.publish('1.95', '1.95.0+dfsg-1ubuntu1', arches=('amd64',))
        self.publish('1.95', '1.95.0+dfsg-1ubuntu1', arches=('arm64',), pocket='Backports')
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (0, 'publication-gap'))

    def test_unversioned_recipe_compiler_is_not_a_known_baseline(self):
        self.recipe = self.recipe.replace('rustc-1.95', 'rustc')
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertIn('versioned', report['error'].lower())

    def test_duplicate_recipe_keys_are_uncertainty_not_a_sufficient_baseline(self):
        self.recipe = 'base: core26\n' + self.recipe
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertIn('duplicate', report['error'].lower())

    def test_optional_github_token_is_never_sent_to_other_evidence_hosts(self):
        self.recipe = self.recipe.replace('1.95', '1.91')
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (0, 'publication-gap'))
        for url, authorization in self.http.authorization:
            self.assertEqual(authorization, 'Bearer fixture-token' if url.startswith('https://api.github.com/') else None)
        self.assertNotIn('fixture-token', json.dumps(report))

    def test_invalid_publication_timestamp_cannot_prove_availability(self):
        self.recipe = self.recipe.replace('1.95', '1.91')
        self.publish('1.95', '1.95.0+dfsg-1ubuntu1', date_published='not-a-timestamp')
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (1, 'unknown'))

    def test_publication_gap_includes_observed_older_compilers_for_each_architecture(self):
        self.recipe = self.recipe.replace('1.95', '1.91')
        self.publish('1.91', '1.91.1+dfsg~24.04-0ubuntu0.24.04.3')
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (0, 'publication-gap'))
        for arch in ('amd64', 'arm64'):
            observed = report['archive']['publications'][arch]
            self.assertEqual(observed['rustc']['1.91']['upstream_version'], '1.91.1')
            self.assertEqual(observed['cargo']['1.91']['pocket'], 'Updates')

    def test_available_patch_in_the_selected_family_requires_no_recipe_bump(self):
        self.declarations(HEAD, '1.95.1')
        self.declarations(TRIGGER, '1.95.1')
        self.publish('1.95', '1.95.2+dfsg-1ubuntu1')
        self.publish('1.96', '1.96.0+dfsg-1ubuntu1')
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (0, 'no-update-needed'))
        self.assertNotIn('selected', report['archive'])

    def test_family_name_does_not_hide_an_insufficient_patch_release(self):
        self.declarations(HEAD, '1.95.2')
        self.declarations(TRIGGER, '1.95.2')
        self.publish('1.95', '1.95.1+dfsg~24.04-0ubuntu0.24.04.10')
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (0, 'publication-gap'))

    def test_missing_cargo_on_one_architecture_is_a_publication_gap(self):
        self.recipe = self.recipe.replace('1.95', '1.91')
        self.publish('1.95', '1.95.0+dfsg-1ubuntu1', binaries=('rustc',))
        self.publish('1.95', '1.95.0+dfsg-1ubuntu1', binaries=('cargo',), arches=('amd64',))
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (0, 'publication-gap'))
        self.assertEqual(report['archive']['publications']['arm64']['cargo'], {})

    def test_numeric_family_ordering_selects_1100_over_199(self):
        self.recipe = self.recipe.replace('1.95', '1.91')
        self.publish('1.99', '1.99.0+dfsg-1ubuntu1')
        self.publish('1.100', '1.100.0+dfsg-1ubuntu1')
        status, report = self.command()
        self.assertEqual(status, 0)
        self.assertEqual(report['archive']['selected']['family'], '1.100')

    def test_disagreeing_pinned_declarations_are_unknown(self):
        self.http.add(RAW + '/mozilla-firefox/firefox/' + HEAD + '/Cargo.toml',
                      '[workspace.package]\nrust-version = "1.93.0"\n')
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertIn('disagree', report['error'])

    def test_downloaded_python_is_parsed_not_executed(self):
        self.http.add(RAW + '/mozilla-firefox/firefox/' + HEAD + '/' + BOOTSTRAP,
                      'MINIMUM_RUST_VERSION = "1.94.0"\nraise RuntimeError("never execute me")\n')
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (0, 'no-update-needed'))

    def test_truncated_archive_pagination_is_unknown_not_a_missing_package(self):
        self.recipe = self.recipe.replace('1.95', '1.91')
        self.http.add(archive_url('amd64', 'rustc'), {'start': 0, 'total_size': 1, 'entries': []})
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertIn('pagination', report['error'].lower())

    def test_rate_limit_is_unknown_not_a_publication_gap(self):
        self.recipe = self.recipe.replace('1.95', '1.91')
        url = archive_url('amd64', 'rustc')
        self.http.responses[canonical_url(url)] = (HTTPError(url, 429, 'rate limited', {}, None), None)
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertIn('429', report['error'])

    def test_prerelease_package_version_is_unknown_not_a_stable_candidate(self):
        self.recipe = self.recipe.replace('1.95', '1.91')
        self.publish('1.95', '1.95.0~beta1-1ubuntu1')
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertIn('Unrecognized', report['error'])

    def test_proposed_ppa_other_series_and_amd64_backports_are_not_candidates(self):
        self.recipe = self.recipe.replace('1.95', '1.91')
        self.publish('1.95', '1.95.0+dfsg-1ubuntu1', pocket='Proposed')
        self.publish('1.96', '1.96.0+dfsg-1ubuntu1', archive_link='https://api.launchpad.net/devel/~test/+archive/ubuntu/ppa')
        self.publish('1.97', '1.97.0+dfsg-1ubuntu1', distro_arch_series_link='https://api.launchpad.net/devel/ubuntu/resolute/amd64')
        self.publish('1.98', '1.98.0+dfsg-1ubuntu1', pocket='Backports')
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (0, 'publication-gap'))

    def test_recorded_recipe_can_be_observed_without_executing_build_steps(self):
        self.recipe = (Path(__file__).parent / 'fixtures/nightly-snapcraft.yaml').read_text()
        self.publish('1.95', '1.95.0+dfsg-1ubuntu1')
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (0, 'compiler-available'))
        self.assertEqual(report['snap']['compiler_family'], '1.91')

    def test_null_recipe_part_returns_unknown_and_preserves_collected_evidence(self):
        self.recipe += '  extra-part: null\n'
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertEqual(report['source']['revision'], HEAD)
        self.assertTrue(report['observations'])

    def test_arm64_backports_respects_its_configured_components(self):
        self.recipe = self.recipe.replace('1.95', '1.91').replace('[main, multiverse, universe]', '[main]')
        self.publish('1.95', '1.95.0+dfsg-1ubuntu1', arches=('amd64',))
        self.publish('1.95', '1.95.0+dfsg-1ubuntu1', arches=('arm64',), pocket='Backports')
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (0, 'publication-gap'))

    def test_debian_epoch_does_not_mask_a_suitable_upstream_patch(self):
        self.recipe = self.recipe.replace('1.95', '1.91')
        self.declarations(HEAD, '1.95.1')
        self.declarations(TRIGGER, '1.95.1')
        self.publish('1.95', '1.95.2+dfsg-1ubuntu1')
        self.publish('1.95', '1:1.95.0+dfsg-1ubuntu1')
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (0, 'compiler-available'))
        for arch in ('amd64', 'arm64'):
            self.assertEqual(report['archive']['selected']['packages'][arch]['rustc']['upstream_version'], '1.95.2')

    def test_annotated_reassignment_cannot_hide_a_changed_msrv(self):
        self.http.add(RAW + '/mozilla-firefox/firefox/' + HEAD + '/' + BOOTSTRAP,
                      'MINIMUM_RUST_VERSION = "1.94.0"\nMINIMUM_RUST_VERSION: str = "1.96.0"\n')
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (1, 'unknown'))

    def test_interrupted_response_returns_unknown_instead_of_a_traceback(self):
        self.http.responses[canonical_url(FIREFOX + '/branches/main')] = (IncompleteRead(b'partial', 10), None)
        status, report = self.command()
        self.assertEqual((status, report['outcome']), (1, 'unknown'))

    def available(self):
        self.recipe = self.recipe.replace('1.95', '1.91')
        self.publish('1.95', '1.95.0+dfsg-1ubuntu1')

    def existing_pull(self):
        return json.loads(self.http.responses[canonical_url(SNAP + '/pulls/41')][0])

    def record_pull(self, pull):
        self.http.add(SNAP + '/pulls?' + urlencode({'state': 'all', 'per_page': 100}), [pull])
        self.http.add(SNAP + '/pulls/41', pull)

    def test_preview_coordinates_all_selections_without_reformatting_or_writes(self):
        self.available()
        self.recipe = self.recipe.replace('- cargo-1.91:arm64', "- 'cargo-1.91:arm64' # keep qualifier")
        self.recipe = self.recipe.replace('rustv=1.91', 'rustv=1.91 # compiler/helper selector')
        self.recipe = self.recipe.replace('      cargo-1.91 build --release',
                                          '      # cargo-1.91 was the previous invocation\n'
                                          '      cargo-1.91 build --release # keep cargo-1.91 comment')
        self.recipe += '  unrelated:\n    source: crate-1.91\n    plugin: nil\n'
        status, report = self.command('--dry-run')
        self.assertEqual((status, report['outcome']), (0, 'compiler-available'))
        proposal = report['proposal']
        self.assertEqual(proposal['status'], 'preview')
        self.assertEqual(proposal['need'], 'canonical/firefox-snap:nightly:rust-1.94.0')
        self.assertEqual(proposal['base'], 'nightly')
        diff = proposal['diff']
        self.assertIn("+          - 'cargo-1.95:arm64' # keep qualifier", diff)
        self.assertIn('+      rustv=1.95 # compiler/helper selector', diff)
        self.assertIn('+      cargo-1.95 build --release # keep cargo-1.91 comment', diff)
        self.assertIn('+          - rustc-1.95:arm64', diff)
        changed = [line for line in diff.splitlines() if line.startswith(('+', '-')) and not line.startswith(('+++', '---'))]
        self.assertEqual(len(changed), 22)  # Nine package selections, invocation, selector.
        self.assertFalse(any('clang-' in line or 'crate-' in line or 'version:' in line for line in changed))
        self.assertEqual(self.http.writes, [])
        body = proposal['body']
        for expected in ('1.94.0', 'from 1.91 to 1.95', TRIGGER, HEAD, SNAP_HEAD, NIGHTLY,
                         'amd64', 'arm64', '1.95.0+dfsg-1ubuntu1', 'No package installation',
                         'Preparatory', 'published', '## Evidence', '## Merge Danger'):
            self.assertIn(expected, body if expected != 'from 1.91 to 1.95' else proposal['title'])

    def test_write_creates_only_a_nightly_proposal_and_durable_evidence(self):
        self.available()
        original = self.recipe
        status, report = self.command('--write')
        self.assertEqual((status, report['proposal']['status']), (0, 'created'))
        writes = {url.rsplit('/', 1)[1]: data for url, data in self.http.writes}
        self.assertEqual(writes['blobs']['content'], original.replace('1.91', '1.95'))
        self.assertEqual(writes['trees']['tree'], [{'path': 'snapcraft.yaml', 'mode': '100644', 'type': 'blob',
                                                   'sha': writes['trees']['tree'][0]['sha']}])
        self.assertEqual(writes['commits']['parents'], [SNAP_HEAD])
        self.assertNotIn('author', writes['commits'])
        self.assertEqual(writes['refs']['ref'], 'refs/heads/automation/rust-msrv-1.94.0')
        self.assertEqual(writes['pulls']['base'], 'nightly')
        self.assertFalse(writes['pulls']['maintainer_can_modify'])
        body = writes['pulls']['body']
        metadata = json.loads(body.split('\n<!-- firefox-snap-msrv-proposal: ')[1].removesuffix(' -->'))
        self.assertEqual(metadata['head'], writes['refs']['sha'])
        self.assertEqual(metadata['evidence']['source']['trigger']['revision'], TRIGGER)
        self.assertEqual(metadata['archive']['packages']['arm64']['cargo']['version'], '1.95.0+dfsg-1ubuntu1')
        self.assertEqual(metadata['recipe_sha256'], hashlib.sha256(writes['blobs']['content'].encode()).hexdigest())
        self.assertNotIn('ghs_fixture_job_token', json.dumps(report))
        for url, auth in self.http.authorization:
            self.assertEqual(auth, 'Bearer ghs_fixture_job_token' if url.startswith('https://api.github.com/') else None)

    def test_repeat_reuses_existing_pr_without_any_updates_or_duplicate_creation(self):
        self.available()
        self.assertEqual(self.command('--write')[0], 0)
        previous = list(self.http.writes)
        status, report = self.command('--write')
        self.assertEqual((status, report['proposal']['status']), (0, 'existing'))
        self.assertEqual(report['proposal']['url'], 'https://github.com/canonical/firefox-snap/pull/41')
        self.assertEqual(self.http.writes, previous)

    def test_closed_human_edited_or_retargeted_prs_are_held_not_recreated(self):
        self.available()
        self.command('--write')
        original = self.existing_pull()
        previous = list(self.http.writes)
        for change in ('closed', 'title', 'body', 'head', 'base', 'author', 'damaged-marker'):
            with self.subTest(change=change):
                pull = json.loads(json.dumps(original))
                if change == 'closed':
                    pull['state'] = 'closed'
                elif change == 'title':
                    pull['title'] += ' (human review)'
                elif change == 'body':
                    pull['body'] = 'Human introduction\n' + pull['body']
                elif change == 'head':
                    pull['head']['sha'] = '9' * 40
                elif change == 'base':
                    pull['base']['ref'] = 'stable'
                elif change == 'author':
                    pull['user']['login'] = 'maintainer'
                else:
                    pull['body'] = '<!-- firefox-snap-msrv-proposal: broken -->'
                self.record_pull(pull)
                status, report = self.command('--write')
                self.assertEqual((status, report['proposal']['status']), (0, 'held'))
                self.assertEqual(self.http.writes, previous)

    def test_changed_available_family_does_not_overwrite_pending_proposal(self):
        self.available()
        self.command('--write')
        previous = list(self.http.writes)
        self.publish('1.96', '1.96.0+dfsg-1ubuntu1')
        for arch in ('amd64', 'arm64'):
            for binary in ('rustc', 'cargo'):
                self.http.responses.pop(canonical_url(archive_url(arch, binary)))
        status, report = self.command('--write')
        self.assertEqual((status, report['proposal']['status']), (0, 'held'))
        self.assertEqual(self.http.writes, previous)

    def test_write_requires_actions_canonical_repository_and_job_token(self):
        self.available()
        for env in ({'GITHUB_ACTIONS': 'false'}, {'GITHUB_REPOSITORY': 'nteodosio/firefox-snap'},
                    {'GITHUB_TOKEN': ''}, {'GITHUB_TOKEN': 'ghp_personal'}, {'GITHUB_TOKEN': 'github_pat_finegrained'}):
            with self.subTest(environment=env):
                status, report = self.command('--write', environment=env)
                self.assertEqual((status, report['outcome']), (1, 'unknown'))
                self.assertEqual(self.http.writes, [])

    def test_no_fallback_to_other_repository_or_personal_credentials(self):
        self.available()
        status, report = self.command('--write', environment={
            'GITHUB_TOKEN': '', 'GH_TOKEN': 'ghp_other', 'REPOSITORY_TOKEN': 'ghs_other_app'})
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertEqual(self.http.writes, [])
        self.assertNotIn('ghp_other', json.dumps(report))

    def test_other_app_identity_cannot_publish_a_branch(self):
        self.available()
        self.http.commit_identity = 'another-app[bot]'
        status, report = self.command('--write')
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertIn('github-actions[bot]', report['error'])
        self.assertFalse(any(url.endswith(('/git/refs', '/pulls')) for url, _ in self.http.writes))

    def test_sufficient_baseline_or_unknown_evidence_never_creates_proposal(self):
        status, report = self.command('--write')
        self.assertEqual((status, report['outcome']), (0, 'no-update-needed'))
        self.assertNotIn('proposal', report)
        self.declarations(HEAD, '1.96.0')
        status, report = self.command('--write')
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertNotIn('proposal', report)
        self.assertEqual(self.http.writes, [])

    def test_refetch_preserves_new_base_and_independent_firefox_update(self):
        self.available()
        current = '7' * 40
        self.http.sequence(SNAP + '/branches/nightly', {'commit': {'sha': SNAP_HEAD}}, {'commit': {'sha': current}})
        updated_base = self.recipe.replace('161.0a1', '162.0a1').replace('- clang-19', '- clang-20')
        self.http.add(RAW + '/canonical/firefox-snap/' + current + '/snapcraft.yaml', updated_base)
        self.http.add(SNAP + '/git/commits/' + current, {'tree': {'sha': '8' * 40}})
        self.base_tree('8' * 40, updated_base)
        self.http.add('https://ftp.mozilla.org/pub/firefox/nightly/latest-mozilla-central/firefox-162.0a1.en-US.linux-x86_64.txt',
                      '20261027091753\nhttps://hg.mozilla.org/mozilla-central/rev/' + NIGHTLY + '\n')
        status, report = self.command('--write')
        self.assertEqual((status, report['proposal']['status']), (0, 'created'))
        self.assertEqual(report['snap']['revision'], current)
        writes = dict(self.http.writes)
        self.assertEqual(writes[SNAP + '/git/blobs']['content'], updated_base.replace('1.91', '1.95'))
        self.assertEqual(writes[SNAP + '/git/commits']['parents'], [current])

    def test_refetch_can_discover_that_another_updater_already_satisfied_the_need(self):
        self.available()
        current = '7' * 40
        self.http.sequence(SNAP + '/branches/nightly', {'commit': {'sha': SNAP_HEAD}}, {'commit': {'sha': current}})
        self.http.add(RAW + '/canonical/firefox-snap/' + current + '/snapcraft.yaml', self.recipe.replace('1.91', '1.95'))
        status, report = self.command('--write')
        self.assertEqual((status, report['outcome']), (0, 'no-update-needed'))
        self.assertNotIn('proposal', report)
        self.assertEqual(self.http.writes, [])

    def test_base_race_stops_before_publishing_a_branch(self):
        self.available()
        self.http.sequence(SNAP + '/branches/nightly', {'commit': {'sha': SNAP_HEAD}},
                           {'commit': {'sha': SNAP_HEAD}}, {'commit': {'sha': '7' * 40}})
        status, report = self.command('--write')
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertIn('Nightly changed', report['error'])
        self.assertFalse(any(url.endswith(('/git/refs', '/pulls')) for url, _ in self.http.writes))

    def test_unexpected_recipe_structure_or_aliases_are_never_guessed(self):
        self.available()
        original = self.recipe
        for recipe in (original.replace('cargo-1.91 build --release', 'cargo-1.91 build --locked'),
                       original.replace('/usr/bin/rust-${rustv}-clang', '/custom/rust-${rustv}-clang'),
                       original.replace('  firefox:\n', '  firefox: &firefox\n'),
                       original + '  extra:\n    build-packages: [cargo-1.91]\n'):
            with self.subTest(recipe=recipe):
                self.recipe = recipe
                status, report = self.command('--write')
                self.assertEqual((status, report['outcome']), (1, 'unknown'))
                self.assertEqual(self.http.writes, [])

    def test_orphan_proposal_ref_requires_recovery_not_an_overwrite(self):
        self.available()
        self.http.add(SNAP + '/git/ref/heads/automation/rust-msrv-1.94.0',
                      {'object': {'sha': '9' * 40}, 'ref': 'refs/heads/automation/rust-msrv-1.94.0'})
        status, report = self.command('--write')
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertIn('manual recovery', report['error'])
        self.assertEqual(self.http.writes, [])

    def test_ambiguous_pr_delivery_does_not_retry_or_replace_the_branch(self):
        self.available()
        self.http.responses[canonical_url(SNAP + '/pulls')] = (TimeoutError('ambiguous PR creation'), None)
        status, report = self.command('--write')
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertEqual(report['proposal']['status'], 'branch-created')
        previous = list(self.http.writes)
        status, report = self.command('--write')
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertEqual(self.http.writes, previous)

    def test_pr_list_pagination_finds_closed_work_before_creating_anything(self):
        self.available()
        self.command('--write')
        pull = self.existing_pull()
        pull['state'] = 'closed'
        self.http.add(SNAP + '/pulls/41', pull)
        first = SNAP + '/pulls?' + urlencode({'state': 'all', 'per_page': 100})
        following = first + '&page=2'
        self.http.add(first, [], {'Link': '<' + following + '>; rel="next"'})
        self.http.add(following, [pull])
        previous = list(self.http.writes)
        status, report = self.command('--write')
        self.assertEqual((status, report['proposal']['status']), (0, 'held'))
        self.assertEqual(self.http.writes, previous)

    def test_multiple_matching_prs_stop_delivery_for_manual_recovery(self):
        self.available()
        self.command('--write')
        pull = self.existing_pull()
        other = json.loads(json.dumps(pull))
        other['number'] = 42
        self.http.add(SNAP + '/pulls?' + urlencode({'state': 'all', 'per_page': 100}), [pull, other])
        previous = list(self.http.writes)
        status, report = self.command('--write')
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertIn('Multiple matching', report['error'])
        self.assertEqual(self.http.writes, previous)

    def test_preview_with_write_credentials_and_existing_work_still_cannot_write(self):
        self.available()
        self.command('--write')
        previous = list(self.http.writes)
        status, report = self.command('--dry-run', environment={
            'GITHUB_TOKEN': 'ghs_fixture_job_token', 'GITHUB_ACTIONS': 'true', 'GITHUB_REPOSITORY': 'canonical/firefox-snap'})
        self.assertEqual((status, report['proposal']['status']), (0, 'existing'))
        self.assertEqual(self.http.writes, previous)

    def test_unexpected_base_mode_or_blob_never_produces_a_write(self):
        self.available()
        for fields in ({'mode': '100755'}, {'mode': '120000', 'type': 'blob'}, {'sha': '0' * 40}):
            with self.subTest(fields=fields):
                self.base_tree('f' * 40, self.recipe, **fields)
                status, report = self.command('--write')
                self.assertEqual((status, report['outcome']), (1, 'unknown'))
                self.assertIn('base blob', report['error'])
                self.assertEqual(self.http.writes, [])

    def test_malformed_pr_collection_cannot_be_treated_as_no_existing_work(self):
        self.available()
        for entries in ([None], [{'head': None}], [{'head': {'ref': 42}}]):
            with self.subTest(entries=entries):
                self.http.add(SNAP + '/pulls?' + urlencode({'state': 'all', 'per_page': 100}), entries)
                status, report = self.command('--write')
                self.assertEqual((status, report['outcome']), (1, 'unknown'))
                self.assertEqual(self.http.writes, [])

    def test_stale_pr_inventory_cannot_justify_new_delivery(self):
        self.available()
        self.http.add(SNAP + '/pulls?' + urlencode({'state': 'all', 'per_page': 100}), [],
                      {'Date': 'Sat, 01 Jan 2000 00:00:00 GMT'})
        status, report = self.command('--write')
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertIn('stale', report['error'])
        self.assertEqual(self.http.writes, [])

    def test_human_change_after_ref_creation_stops_pr_creation(self):
        self.available()
        ref_url = SNAP + '/git/ref/heads/automation/rust-msrv-1.94.0'
        # A writer changes the branch between atomic creation and the next read.
        original_propose = self.http.propose

        def concurrent_writer(method, url, data):
            result = original_propose(method, url, data)
            if url.endswith('/git/refs'):
                self.http.add(ref_url, {'object': {'sha': '9' * 40}})
            return result

        with mock.patch.object(self.http, 'propose', side_effect=concurrent_writer):
            status, report = self.command('--write')
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertEqual(report['proposal']['status'], 'branch-created')
        self.assertFalse(any(url.endswith('/pulls') for url, _ in self.http.writes))

    def test_competing_ref_creation_cannot_replace_the_other_writer(self):
        self.available()
        self.http.responses[canonical_url(SNAP + '/git/refs')] = (
            HTTPError(SNAP + '/git/refs', 422, 'Reference already exists', {}, None), None)
        status, report = self.command('--write')
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertIn('422', report['error'])
        self.assertFalse(any(url.endswith('/pulls') for url, _ in self.http.writes))

    def test_shell_assignment_hash_without_whitespace_is_not_a_comment(self):
        self.available()
        self.recipe = self.recipe.replace('rustv=1.91', 'rustv=1.91#not-a-comment')
        status, report = self.command('--write')
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertEqual(self.http.writes, [])

    def test_upstream_history_http_error_retains_source_evidence_without_delivery(self):
        self.available()
        history = FIREFOX + '/commits?' + urlencode({'sha': HEAD, 'path': BOOTSTRAP, 'per_page': 100})
        self.http.responses[canonical_url(history)] = (HTTPError(history, 422, 'Unprocessable Entity', {}, None), None)
        status, report = self.command('--write')
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        self.assertEqual(report['source']['revision'], HEAD)
        self.assertIn('422', report['error'])
        self.assertNotIn('proposal', report)
        self.assertEqual(self.http.writes, [])

    def test_successful_but_ambiguous_creation_is_found_before_retrying_delivery(self):
        self.available()
        original_propose = self.http.propose

        def ambiguous_response(method, url, data):
            result = original_propose(method, url, data)
            if url.endswith('/pulls'):
                result.close()
                raise TimeoutError('PR created but response lost')
            return result

        with mock.patch.object(self.http, 'propose', side_effect=ambiguous_response):
            status, report = self.command('--write')
        self.assertEqual((status, report['outcome']), (1, 'unknown'))
        previous = list(self.http.writes)
        status, report = self.command('--write')
        self.assertEqual((status, report['proposal']['status']), (0, 'existing'))
        self.assertEqual(report['proposal']['number'], 41)
        self.assertEqual(self.http.writes, previous)


if __name__ == '__main__':
    unittest.main()
