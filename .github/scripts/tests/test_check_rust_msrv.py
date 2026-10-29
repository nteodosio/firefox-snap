"""Exercise the complete read-only monitor command with recorded HTTP I/O."""

import contextlib
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

    def add(self, url, body, headers=None):
        if not isinstance(body, str):
            body = json.dumps(body)
        self.responses[canonical_url(url)] = (body.encode(), headers)

    def open(self, request, *args, **kwargs):
        if isinstance(request, str):
            method, url = 'GET', request
        else:
            method, url = request.get_method(), request.full_url
        if method != 'GET':
            raise AssertionError('The read-only monitor attempted ' + method)
        self.requests.append(url)
        self.authorization.append((url, request.get_header('Authorization') if not isinstance(request, str) else None))
        key = canonical_url(url)
        if key not in self.responses:
            raise AssertionError('Unrecorded HTTP request: ' + url)
        body, headers = self.responses[key]
        if isinstance(body, Exception):
            raise body
        return Response(body, headers)


class MonitorCommandTests(unittest.TestCase):
    def setUp(self):
        self.http = RecordedHTTP()
        self.publications = {arch: {binary: [] for binary in ('rustc', 'cargo')}
                             for arch in ('amd64', 'arm64')}
        self.recipe = (Path(__file__).parent / 'fixtures/nightly-snapcraft.yaml').read_text().replace('1.91', '1.95')
        self.http.add(SNAP + '/branches/nightly', {'commit': {'sha': SNAP_HEAD}})
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

    def command(self):
        global COMMAND_RUNNING
        self.http.add(RAW + '/canonical/firefox-snap/' + SNAP_HEAD + '/snapcraft.yaml', self.recipe)
        for arch, binaries in self.publications.items():
            for binary, records in binaries.items():
                url = archive_url(arch, binary)
                if canonical_url(url) not in self.http.responses:
                    self.http.add(url, {'start': 0, 'total_size': len(records), 'entries': records})
        output = io.StringIO()
        with mock.patch.object(sys, 'argv', [str(SCRIPT)]), \
             mock.patch.object(sys, 'dont_write_bytecode', True), \
             mock.patch.dict(os.environ, {'GITHUB_TOKEN': 'fixture-token'}), \
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


if __name__ == '__main__':
    unittest.main()
