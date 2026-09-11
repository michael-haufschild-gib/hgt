from __future__ import annotations

import json
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from lean_research_corpus import Corpus, chunks, inventory, mask_comments_strings, source_declarations, EvidenceChanged


class ExtractionTests(unittest.TestCase):
    def test_comment_only_mask_retains_string_literals_and_line_positions(self):
        source = '"/-- literal \\" --/"\n/- comment /- nested -/ -/\nby rfl -- note'
        result = mask_comments_strings(source, mask_strings=False)
        self.assertEqual(result.splitlines()[0], source.splitlines()[0])
        self.assertEqual(result.count('\n'), source.count('\n'))
        self.assertNotIn('nested', result)
        self.assertIn('by rfl', result)

    def test_comments_strings_and_nested_comments_cannot_invent_declarations(self):
        text = '/- theorem fake : False := /- nested -/ sorry -/\n' \
               'def s := "theorem fake2 : False := sorry"\n' \
               'namespace A\n/-- words -/\ntheorem real (x : Nat := 2) : x = x := by rfl\nend A\n'
        rows = source_declarations(text, 'M', 'M.lean')
        self.assertEqual([r['name'] for r in rows], ['s', 'A.real'])
        self.assertIn('(x : Nat := 2)', rows[1]['statement'])
        self.assertEqual(rows[1]['proof'], 'by rfl')
        self.assertEqual(rows[1]['doc'], 'words')
        self.assertEqual(mask_comments_strings(text).count('\n'), text.count('\n'))

    def test_namespace_sections_same_names_and_anonymous_instances(self):
        text = 'namespace A\nsection S\ntheorem same : True := trivial\nend S\nend A\n' \
               'namespace B\ntheorem same : True := trivial\ninstance : Inhabited Nat := ⟨0⟩\nend B\n'
        rows = source_declarations(text, 'M', 'M.lean')
        self.assertEqual([r['name'] for r in rows[:2]], ['A.same', 'B.same'])
        self.assertTrue(rows[2]['name'].startswith('B.<anonymous@'))
        self.assertEqual(len({r['id'] for r in rows}), 3)

    def test_chunks_cover_all_source_without_unbounded_chunks(self):
        source = ''.join('line_%05d := %s\n' % (i, 'ξ' * 25) for i in range(1600))
        parts = list(chunks(source))
        self.assertTrue(all(len(p[0]) <= 5000 for p in parts))
        for line in source.splitlines():
            self.assertTrue(any(line in part for part, _, _ in parts))
        self.assertTrue(parts[-1][0].endswith(source[-30:]))

    def test_chunk_line_numbers_use_only_linear_scanning(self):
        class CountedText(str):
            scanned = 0

            def count(self, value, start=0, end=None):
                end = len(self) if end is None else end
                self.scanned += max(0, min(end, len(self)) - start)
                return super().count(value, start, end)

        source = CountedText(''.join('%05d%s\n' % (i, 'α' * 127) for i in range(2000)))
        parts = list(chunks(source, line=17))
        self.assertLessEqual(source.scanned, 3 * len(source))
        plain = str(source)
        start = 0
        for part, first, last in parts:
            start = plain.index(part, start)
            self.assertEqual(first, 17 + plain.count('\n', 0, start))
            self.assertEqual(last, first + part.count('\n'))
            start += 1


class CorpusTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.db = Corpus(self.root / 'cache')
        self.addCleanup(self.db.close)

    def write(self, path, text):
        p = self.root / path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
        return p

    def test_inventory_includes_dependencies_and_prose_and_full_outcomes(self):
        self.write('formal/GaloisForLFunctions/A.lean', 'theorem a : True := trivial')
        self.write('formal/.lake/packages/mathlib/Mathlib/A.lean', 'theorem b : True := trivial')
        self.write('formal/.lake/packages/mathlib/.lake/build/junk.lean', 'bad')
        self.write('docs/drafts/pipeline/1-in-progress/test.md', '# Plan\nconditional result')
        stats = self.db.refresh(self.root)
        self.assertEqual(stats['coverage']['files'], 3)
        self.assertEqual(stats['coverage']['outcomes'], {'indexed': 3})
        self.assertEqual(stats['coverage']['declarations'], 2)
        self.assertEqual(len(self.db.search('conditional', views=('prose',))), 1)

    def test_full_proof_is_searchable_and_statements_keep_hypotheses(self):
        self.write('formal/A.lean', 'namespace A\ntheorem rare (n : Nat) (h : n > 0) : n = n := by\n  -- amplification mechanism\n  rfl\nend A\n')
        self.db.refresh(self.root)
        hit = self.db.search('amplification', views=('proof',))[0]
        declaration = self.db.declaration(hit['decl_id'])
        self.assertIn('(h : n > 0)', declaration['statement'])
        self.assertEqual(declaration['compiler_status'], 'source_only')
        self.assertIsNone(declaration['axioms'])

    def test_edit_delete_and_failed_decode_are_not_silently_current(self):
        p = self.write('formal/A.lean', 'theorem alpha : True := trivial')
        self.db.refresh(self.root)
        gen = self.db.generation
        self.assertEqual(self.db.refresh(self.root)['changed'], 0)
        self.assertEqual(self.db.generation, gen)
        p.write_text('theorem beta : True := trivial')
        self.db.refresh(self.root)
        self.assertFalse(self.db.search('alpha'))
        self.assertTrue(self.db.search('beta'))
        p.write_bytes(b'\xff')
        self.assertEqual(self.db.refresh(self.root)['failed'], 1)
        hit = self.db.search('beta')[0]
        self.assertEqual(self.db.declaration(hit['decl_id'])['file_status'], 'failed')
        p.unlink()
        self.assertEqual(self.db.refresh(self.root)['removed'], 1)
        self.assertFalse(self.db.search('beta'))

    def test_deadline_preserves_old_records_and_reports_pending_inventory(self):
        p = self.write('formal/A.lean', 'theorem alpha : True := trivial')
        self.db.refresh(self.root)
        self.write('formal/B.lean', 'theorem beta : True := trivial')
        stats = self.db.refresh(self.root, deadline=time.monotonic() - 1)
        self.assertFalse(stats['complete'])
        self.assertEqual(stats['coverage']['pending_files'], 1)
        self.assertTrue(self.db.search('alpha'))

    def test_compiler_rows_preserve_all_binders_and_reject_stale_hash(self):
        self.write('formal/A.lean', 'theorem alpha (n : Nat) : n = n := rfl')
        self.db.refresh(self.root)
        sha = self.db.con.execute('SELECT source_hash FROM files').fetchone()[0]
        row = dict(name='alpha', type_text='∀ n : Nat, n = n', type_shape='forall Nat Eq b0 b0',
                   binders=[dict(name='n', type='Nat', binder_info='default')],
                   axioms=[], type_dependencies=['Nat', 'Eq'], proof_dependencies=['Eq.refl'])
        self.assertEqual(self.db.install_compiler_rows('formal/A.lean', [row], source_hash='stale'), 0)
        self.assertEqual(self.db.install_compiler_rows('formal/A.lean', [row], source_hash=sha), 1)
        d = self.db.declaration(self.db.search('alpha')[0]['decl_id'])
        self.assertEqual(d['binders'], row['binders'])
        self.assertEqual(d['axioms'], [])
        self.assertIn(dict(target='Eq.refl', kind='proof'), d['dependencies'])

    def test_compiler_generated_names_with_shared_suffix_remain_distinct(self):
        self.write('formal/A.lean', 'theorem alpha : True := trivial')
        self.db.refresh(self.root)
        sha = self.db.con.execute('SELECT source_hash FROM files').fetchone()[0]
        rows = [dict(name=name, module='A', kind='theorem', type_text='True',
                     proof_dependencies=[dependency]) for name, dependency in (
            ('First.alpha._simp_1', 'First.witness'),
            ('Second.alpha._simp_1', 'Second.witness'))]
        self.db.install_compiler_rows('formal/A.lean', rows, source_hash=sha)
        for row in rows:
            declaration = self.db.con.execute('SELECT id FROM declarations WHERE name=?',
                                              (row['name'],)).fetchone()
            self.assertIsNotNone(declaration, row['name'])
            actual = self.db.declaration(declaration['id'])
            self.assertEqual(actual['compiler_metadata']['name'], row['name'])
            self.assertIn(dict(target=row['proof_dependencies'][0], kind='proof'), actual['dependencies'])

    def test_compiler_private_fallback_requires_full_source_name(self):
        self.write('formal/A.lean', 'namespace First\nprivate theorem alpha : True := trivial\nend First')
        self.db.refresh(self.root)
        sha = self.db.con.execute('SELECT source_hash FROM files').fetchone()[0]
        original = self.db.con.execute('SELECT id FROM declarations').fetchone()[0]
        common = dict(module='A', kind='theorem', line=2, type_text='True')
        rows = [dict(common, name='_private.A.0.Second.alpha'),
                dict(common, name='_private.A.0.First.alpha')]
        self.db.install_compiler_rows('formal/A.lean', rows, source_hash=sha)
        self.assertEqual(self.db.declaration(original)['name'], rows[1]['name'])
        self.assertEqual(self.db.con.execute('SELECT count(*) FROM compiler_metadata').fetchone()[0], 2)

    def test_methods_require_source_evidence_and_invalidate_dependents(self):
        self.write('formal/A.lean', 'theorem alpha : True := trivial')
        p = self.write('formal/B.lean', 'theorem beta : True := alpha')
        self.db.refresh(self.root)
        did = self.db.search('beta')[0]['decl_id']
        payload = dict(description='reuse witness', assumptions=[], steps=['apply alpha'],
                       obligations=['obtain alpha'], evidence=['alpha'])
        self.db.save_method(did, payload, model_version='local-model', prompt_version='v1')
        with self.assertRaises(ValueError):
            self.db.save_method(did, {**payload, 'evidence': ['invented']}, model_version='m', prompt_version='v1')
        with self.db.con:
            self.db.con.execute('INSERT INTO dependencies VALUES(?,?,?)', (did, 'alpha', 'proof'))
        self.write('formal/A.lean', 'theorem alpha : True := by trivial')
        self.db.refresh(self.root)
        self.assertIsNone(self.db.method(did))
        self.assertFalse(self.db.search('reuse witness', views=('method',)))

    def test_filters_apply_before_limit_and_cache_tracks_generation(self):
        self.write('formal/A_B.lean', 'theorem alpha : True := trivial')
        self.write('formal/AXB.lean', 'theorem alpha : True := trivial')
        self.db.refresh(self.root)
        self.assertEqual([h['module'] for h in self.db.search('alpha', module='A_B')], ['A_B'])
        self.assertEqual([h['module'] for h in self.db.search('alpha', exclude_modules=['A_B'])], ['AXB'])
        self.db.cache('q', {'ok': 1})
        self.assertEqual(self.db.cached('q'), {'ok': 1})
        self.write('formal/C.lean', 'theorem gamma : True := trivial')
        self.db.refresh(self.root)
        self.assertIsNone(self.db.cached('q'))

    def test_source_references_invalidate_without_compiler_metadata(self):
        self.write('formal/A.lean', 'namespace A\ntheorem alpha : True := trivial\nend A')
        self.write('formal/B.lean', 'theorem beta : True := A.alpha')
        self.db.refresh(self.root)
        did = self.db.search('beta')[0]['decl_id']
        self.db.save_method(did, dict(description='apply supplied witness', assumptions=[], steps=['use alpha'],
                                      obligations=['obtain witness'], evidence=['A.alpha']), model_version='m', prompt_version='v')
        self.write('formal/A.lean', 'namespace A\ntheorem alpha : True := by trivial\nend A')
        self.db.refresh(self.root)
        self.assertIsNone(self.db.method(did))

    def test_generated_declaration_cannot_overwrite_parent_at_same_range(self):
        self.write('formal/A.lean', 'theorem alpha : True := trivial')
        self.db.refresh(self.root)
        sha = self.db.con.execute('SELECT source_hash FROM files').fetchone()[0]
        payload = dict(name='alpha.helper',module='A',kind='theorem',type_text='True',type_shape='shape',
                       binders=[],axioms=[],type_dependencies=[],proof_dependencies=[],
                       source={'range': {'start': {'line': 1}, 'end': {'line': 1}}})
        self.db.install_compiler_rows('formal/A.lean',[payload],source_hash=sha,status='compiled_snapshot')
        self.assertEqual({r[0] for r in self.db.con.execute('SELECT name FROM declarations')}, {'alpha','alpha.helper'})

    def test_pending_method_cannot_publish_after_dependency_evidence_changes(self):
        self.write('formal/A.lean', 'theorem alpha : True := trivial')
        self.write('formal/B.lean', 'theorem beta : True := alpha')
        self.db.refresh(self.root)
        did = self.db.search('beta')[0]['decl_id']
        epoch = self.db.evidence_epoch
        self.write('formal/A.lean', 'theorem alpha : True := by trivial')
        self.db.refresh(self.root)
        with self.assertRaises(EvidenceChanged):
            self.db.save_method(did, dict(description='use witness', assumptions=[], steps=['apply alpha'],
                obligations=[], evidence=['alpha']), model_version='m', prompt_version='v', expected_evidence_epoch=epoch)
        self.assertIsNone(self.db.method(did))

    def test_extractor_migration_does_not_walk_dependencies_of_unchanged_sources(self):
        self.write('formal/A.lean', 'theorem alpha : True := trivial')
        self.db.refresh(self.root)
        with self.db.con:
            self.db.con.execute("UPDATE files SET extractor_version='old'")
        with patch.object(self.db, '_invalidate_dependents', side_effect=AssertionError('unnecessary graph traversal')):
            self.assertEqual(self.db.refresh(self.root)['changed'], 1)

    def test_invalidation_deadline_marks_descriptions_stale_without_blocking(self):
        self.write('formal/A.lean', 'theorem alpha : True := trivial')
        self.db.refresh(self.root)
        did = self.db.search('alpha')[0]['decl_id']
        self.db.save_method(did, dict(description='use witness', assumptions=[], steps=[], obligations=[], evidence=['trivial']), model_version='m', prompt_version='v')
        with self.db.con:
            self.db._invalidate_dependents(['alpha'], deadline=time.monotonic()-1)
        self.assertIsNone(self.db.method(did))
        self.assertFalse(self.db.search('witness', views=('method',)))

    def test_dependency_invalidation_resumes_without_deleting_unrelated_methods(self):
        self.write('formal/A.lean', 'theorem alpha : True := trivial')
        self.write('formal/B.lean', 'theorem beta : True := alpha')
        self.write('formal/C.lean', 'theorem gamma : True := beta')
        self.write('formal/D.lean', 'theorem independent : True := trivial')
        self.db.refresh(self.root)
        ids = {r['name']:r['id'] for r in self.db.con.execute('SELECT id,name FROM declarations')}
        for name, evidence in [('beta','alpha'), ('gamma','beta'), ('independent','trivial')]:
            self.db.save_method(ids[name], dict(description='witness '+name, assumptions=[],
                steps=[], obligations=[], evidence=[evidence]), model_version='m', prompt_version='v')
        with self.db.con:
            self.db._invalidate_dependents(['alpha'], deadline=time.monotonic()-1)
        self.assertTrue(self.db.invalidation_pending())
        self.assertEqual(self.db.con.execute('SELECT count(*) FROM methods').fetchone()[0], 3)
        with Corpus(self.db.directory) as resumed:
            resumed.drain_invalidations(deadline=time.monotonic()+5)
            self.assertFalse(resumed.invalidation_pending())
            self.assertIsNone(resumed.method(ids['beta']))
            self.assertIsNone(resumed.method(ids['gamma']))
            self.assertIsNotNone(resumed.method(ids['independent']))
            self.assertEqual(len(resumed.search('witness', views=('method',))), 1)

    def test_method_generation_cannot_publish_while_dependencies_are_pending(self):
        self.write('formal/A.lean', 'theorem alpha : True := trivial')
        self.db.refresh(self.root)
        d = dict(self.db.con.execute('SELECT * FROM declarations').fetchone())
        with self.db.con:
            self.db.con.execute("INSERT INTO method_invalidation(name) VALUES('alpha')")
        payload = dict(description='witness', assumptions=[], steps=[], obligations=[], evidence=['trivial'])
        with self.assertRaises(EvidenceChanged):
            self.db.save_method(d['id'], payload, model_version='m', prompt_version='v')
        with self.assertRaises(EvidenceChanged):
            self.db.save_method_chunk(d, 'chunk', payload, 'm', 'v', self.db.evidence_epoch)


if __name__ == '__main__':
    unittest.main()
