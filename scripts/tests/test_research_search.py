from __future__ import annotations

import contextlib
import io
import json
import sqlite3
import sys
import tempfile
import unittest
from collections import Counter
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import formal_tools as ft
from lean_search_index import DeclRow, LeanSearchIndex, MarkerRow, SourceFile


class SearchQualityTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.index = LeanSearchIndex(Path(self.tmp.name) / 'index.db', busy_timeout_ms=20)
        self.addCleanup(self.index.close)
        self.rows = {}

    def add(self, module, declarations, markers=()):
        self.rows[module] = ([DeclRow(name, 'theorem', module, i + 1, doc)
                              for i, (name, doc) in enumerate(declarations)],
                             [MarkerRow(i + 1, m) for i, m in enumerate(markers)])

    def refresh(self):
        sources = [SourceFile(m, m, 1, 1) for m in self.rows]
        self.index.refresh(sources, lambda s: self.rows[s.relpath])

    def names(self, query, **options):
        return {h.name for h in self.index.search_declarations(query, limit=100, **options)}

    def test_all_terms_required_and_any_is_explicit(self):
        self.add('M', [('spectralGap', ''), ('spectral', ''), ('gap', '')])
        self.refresh()
        self.assertEqual(self.names('spectral gap'), {'spectralGap'})
        self.assertEqual(self.names('spectral gap', any_terms=True), {'spectralGap', 'spectral', 'gap'})
        self.assertEqual(self.names('spectral absent'), set())

    def test_required_phrase_cannot_be_bypassed_by_other_term(self):
        self.add('M', [('target', 'critical line zero'), ('wrong', 'zero critical off line'),
                       ('phraseOnly', 'critical line')])
        self.refresh()
        self.assertEqual(self.names('"critical line" zero'), {'target'})

    def test_exact_disables_prefixes_without_changing_and(self):
        self.add('M', [('sumGap', ''), ('summableGap', '')])
        self.refresh()
        self.assertEqual(self.names('sum gap'), {'sumGap', 'summableGap'})
        self.assertEqual(self.names('sum gap', exact=True), {'sumGap'})

    def test_module_camel_components_find_generic_side_lemma(self):
        self.add('Area.IntegerCarryTransport', [('mul', '')])
        self.add('Area.IntegerTransport', [('other', '')])
        self.refresh()
        self.assertEqual(self.names('integer carry transport'), {'mul'})

    def test_unicode_identifier_queries_do_not_expand_sharp_s_to_ascii(self):
        self.add('M', [('Straße', ''), ('Böttcher', ''), ('ξ', ''), ('Λ_pos', ''),
                       ('deckMap₁_leftInverse', '')])
        self.refresh()
        for name in ('Straße', 'Böttcher', 'ξ', 'Λ_pos', 'deckMap₁_leftInverse'):
            with self.subTest(name=name):
                self.assertIn(name, self.names(name))

    def test_module_cap_pages_and_exploration_reach_past_dominant_family(self):
        for i in range(25):
            self.add(f'Area.PrimeSpectralPacket{i}', [(f'gap{i}_{j}', 'spectral gap') for j in range(8)])
        self.add('Geometry.ExoticCoercivity', [('sideLemma', 'a spectral comparison proves a gap')])
        self.add('Geometry.Unrelated', [('noise', 'nothing relevant')])
        self.refresh()
        first = self.index.search('spectral gap', limit=10, per_module=2, explore=5)
        self.assertEqual(first.total, 201)
        self.assertEqual(first.modules, 26)
        self.assertEqual(first.eligible, 51)
        self.assertTrue(all(n <= 2 for n in Counter(h.module for h in first.declarations).values()))
        direct = {(h.module, h.name) for h in first.declarations}
        extra = {(h.module, h.name) for h in first.exploration}
        self.assertFalse(direct & extra)
        self.assertIn(('Geometry.ExoticCoercivity', 'sideLemma'), direct | extra)
        self.assertNotIn('noise', {h.name for h in first.exploration})
        second = self.index.search('spectral gap', limit=10, per_module=2, offset=10, explore=0)
        self.assertFalse(direct & {(h.module, h.name) for h in second.declarations})
        self.assertEqual(first, self.index.search('spectral gap', limit=10, per_module=2, explore=5))

    def test_filters_are_literal_and_apply_to_exploration(self):
        for m in ('Area.A_B', 'Area.AXB', 'Other.C'):
            self.add(m, [('gap', '')])
        self.refresh()
        self.assertEqual({h.module for h in self.index.search('gap', module='A_B').declarations}, {'Area.A_B'})
        result = self.index.search('gap', module='Area', exclude_modules=['A_B'], limit=0)
        self.assertEqual([h.module for h in result.exploration], ['Area.AXB'])
        self.assertEqual(self.index.search('gap', module='%').total, 0)

    def test_marker_matching_obeys_same_query_and_module_filters(self):
        self.add('Area.One', [], ['TODO spectral gap', 'TODO spectral only'])
        self.add('Other.Two', [], ['TODO spectral gap'])
        self.refresh()
        hits = self.index.search_markers('spectral gap', module='Area')
        self.assertEqual([(h.relpath, h.text) for h in hits], [('Area.One', 'TODO spectral gap')])

    def test_migration_under_writer_lock_preserves_database(self):
        self.add('M', [('alpha', '')])
        self.refresh()
        con = sqlite3.connect(self.index.db_path)
        self.addCleanup(con.close)
        con.execute("UPDATE meta SET value='old' WHERE key='schema_fingerprint'")
        con.commit()
        self.index.close()
        con.execute('BEGIN IMMEDIATE')
        with self.assertRaises(sqlite3.OperationalError):
            self.index.search('alpha')
        con.rollback()
        self.assertEqual(con.execute('SELECT name FROM decl').fetchall(), [('alpha',)])
        self.assertEqual(con.execute('PRAGMA integrity_check').fetchone(), ('ok',))


class ResearchCommandTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.sources = []
        self.write('IntegerCarryTransport', '/-- ' + 'context ' * 40 + 'exotic tail terminology. -/\n'
                   'private theorem mul : True := trivial\n'
                   '-- TODO carry gap\n')
        self.write('Other', 'theorem carry : True := trivial\n-- TODO gap alone\n')

    def write(self, name, body):
        p = self.root / (name + '.lean')
        p.write_text(body)
        s = p.stat()
        self.sources.append(SourceFile(p.name, str(p), s.st_size, s.st_mtime_ns))

    def run_cli(self, *args):
        out, err = io.StringIO(), io.StringIO()
        with patch.object(ft, 'SEARCH_DB', self.root / 'search.db'), \
             patch.object(ft, 'ROOT', self.root), \
             patch.object(ft, 'search_sources', return_value=self.sources), \
             contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = ft.main(['research', *args])
        return code, out.getvalue(), err.getvalue()

    def test_full_docstring_and_generic_declaration_are_searchable(self):
        code, out, _ = self.run_cli('exotic tail terminology', '--json')
        self.assertEqual(code, 0)
        result = json.loads(out)
        self.assertEqual([h['name'] for h in result['declarations']], ['mul'])
        self.assertEqual(result['declarations'][0]['line'], 2)
        self.assertEqual(result['declarations'][0]['kind'], 'private theorem')

    def test_fts_and_scan_find_same_candidates_for_supported_queries(self):
        # Same extractor includes private declarations and full docs; scan never
        # silently reverts to OR or the old 500-marker pre-filter.
        for query, flags in [('integer carry', []), ('carry absent', []),
                             ('carry absent', ['--any']), ('"exotic tail" terminology', []),
                             ('car', ['--exact']), ('carry', ['--module', 'Integer']),
                             ('the integer carry of a number', [])]:
            with self.subTest(query=query, flags=flags):
                a = self.run_cli(query, *flags, '--json')
                b = self.run_cli(query, *flags, '--json', '--scan')
                self.assertEqual((a[0], b[0]), (0, 0))
                a, b = json.loads(a[1]), json.loads(b[1])
                for key in ('declarations', 'markers'):
                    identity = lambda r: {(h['relpath'], h['line']) for h in r[key]}
                    self.assertEqual(identity(a), identity(b))

    def test_scan_does_not_cut_markers_off_before_matching(self):
        self.write('Late', '\n'.join(['-- TODO unrelated'] * 510 + ['-- TODO needle marker']))
        code, out, _ = self.run_cli('needle marker', '--scan', '--json')
        self.assertEqual(code, 0)
        self.assertEqual([m['line'] for m in json.loads(out)['markers']], [511])

    def test_invalid_queries_fail_without_search_or_traceback(self):
        for args in [('foo OR bar',), ('"unclosed',), ('...',), ('foo', '--limit', '-1'),
                     ('foo', '--offset', '-1'), ('foo', '--explore', '-1')]:
            with self.subTest(args=args):
                code, out, err = self.run_cli(*args)
                self.assertEqual(code, 2)
                self.assertFalse(out)
                self.assertTrue(err)

    def test_empty_no_refresh_is_not_reported_as_no_matches(self):
        code, out, err = self.run_cli('carry', '--no-refresh')
        self.assertEqual(code, 2)
        self.assertFalse(out)
        self.assertIn('rerun without --no-refresh', err)

    def test_plain_comment_does_not_pull_unrelated_code_into_docstring(self):
        self.write('CommentBoundary', '/-- Unrelated exotic description. -/\n'
                   'theorem oldLemma : True := trivial\n'
                   '/- A plain implementation comment. -/\n'
                   'theorem nextLemma : True := trivial\n')
        code, out, _ = self.run_cli('exotic', '--module', 'CommentBoundary', '--json')
        self.assertEqual(code, 0)
        self.assertEqual([h['name'] for h in json.loads(out)['declarations']], ['oldLemma'])

    def test_nested_doc_comment_preserves_whole_adjacent_block(self):
        self.write('NestedDoc', '/-- Outer intro.\n/- nested -/\nRare tail words. -/\n'
                   'theorem leaf : True := trivial\n')
        code, out, _ = self.run_cli('rare tail', '--json')
        self.assertEqual(code, 0)
        self.assertEqual([h['name'] for h in json.loads(out)['declarations']], ['leaf'])

    def test_unavailable_index_falls_back_and_reports_backend(self):
        with patch.object(LeanSearchIndex, 'refresh', side_effect=ft.SearchIndexUnavailable('missing FTS5')):
            code, out, err = self.run_cli('integer carry', '--json')
        self.assertEqual(code, 0)
        self.assertIn('scanning instead', err)
        self.assertTrue(json.loads(out)['backend'].startswith('scan'))
        self.assertEqual([d['name'] for d in json.loads(out)['declarations']], ['mul'])


if __name__ == '__main__':
    unittest.main()
