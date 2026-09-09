from __future__ import annotations

import json
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from lean_research_corpus import Corpus
from lean_research_engine import Engine, json_object, reciprocal_rank_fusion, method_payload, enrich


class FakeRuntime:
    def __init__(self, answers=()):
        self.answers = list(answers)
        self.calls = []

    def status(self):
        return {'available': True, 'embedding_model': 'fake', 'generation_model': 'fake'}

    def embed(self, texts, *, query=False, deadline):
        self.calls.append(('embed', texts))
        return [[1., 0.] for _ in texts]

    def rerank(self, query, documents, *, deadline):
        return [1. / (i + 1) for i in range(len(documents))]

    def generate(self, prompt, *, deadline, max_tokens):
        self.calls.append(('generate', prompt))
        if self.answers:
            return json.dumps(self.answers.pop(0))
        return '{"next_queries":[],"sufficient":true}'


class EmptyVectors:
    def coverage(self, model):
        return {'complete': True, 'expected': 1, 'ready': 1}

    def search(self, embedding, **kwargs):
        return []


class FusionTests(unittest.TestCase):
    def test_many_chunks_do_not_multiply_a_declaration_score(self):
        rows = [{'decl_id': 'a', 'text': 'chunk'}] * 10 + [{'decl_id': 'b'}]
        result = reciprocal_rank_fusion([rows, [{'decl_id': 'b'}]])
        self.assertEqual([r['decl_id'] for r in result], ['b', 'a'])

    def test_json_parser_never_evaluates_text(self):
        self.assertEqual(json_object('```json\n{"queries":[]}\n```'), {'queries': []})
        with self.assertRaises(ValueError):
            json_object("__import__('os').system('false')")

    def test_truncated_outer_judgment_is_not_replaced_by_valid_inner_step(self):
        with self.assertRaisesRegex(ValueError, 'incomplete or malformed'):
            json_object('{"ingredient_sets":[{"steps":[{"goal":"partial","candidate_ids":["c0"]}]},')

    def test_method_evidence_is_resolved_to_exact_source_and_invalid_ids_rejected(self):
        proof = 'by\n  exact h\n/-- Another declaration description -/\n'
        payload = dict(description='reuse a supplied witness', assumptions=['h'], steps=['apply h'], obligations=['supply h'], evidence_lines=[2])
        self.assertEqual(method_payload(json.dumps(payload), proof)['evidence'], ['  exact h'])
        for ids in ([0], [99], [True], [], ['2'], [3]):
            with self.assertRaises(ValueError):
                method_payload(json.dumps({**payload, 'evidence_lines': ids}), proof)


class EngineTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        (root / 'formal').mkdir()
        (root / 'formal' / 'Amplifier.lean').write_text('namespace A\n/-- uniform growth bound -/\n'
            'theorem alpha (n : Nat) (h : n > 0) : n = n := by\n  -- iterate growth bound\n  rfl\nend A\n')
        (root / 'formal' / 'Other.lean').write_text('theorem beta : True := trivial\n')
        self.db = Corpus(root / 'cache')
        self.addCleanup(self.db.close)
        self.db.refresh(root)
        self.did = self.db.search('alpha')[0]['decl_id']

    def test_no_models_returns_truthful_partial_results(self):
        result = Engine(self.db).search('growth bound')
        self.assertTrue(result['partial'])
        self.assertIn('local_models_unavailable', result['unfinished_stages'])
        self.assertEqual(result['candidate_lemmas'][0]['name'], 'A.alpha')
        self.assertEqual(result['candidate_lemmas'][0]['applicability'], 'not_checked')
        self.assertIn('(h : n > 0)', result['candidate_lemmas'][0]['statement'])
        self.assertFalse(result['proof_ideas'])

    def test_ideas_need_existing_source_and_exact_evidence(self):
        runtime = FakeRuntime([dict(sufficient=True, proof_ideas=[
            dict(source_id=self.did, transfer='iterate a new growth estimate', obligations=['prove matching uniform bound'], evidence=['rfl']),
            dict(source_id='invented', transfer='x', obligations=['x'], evidence=['rfl']),
            dict(source_id=self.did, transfer='false quotation', obligations=['x'], evidence=['not in the proof'])],
            ingredient_sets=[dict(description='assembly', steps=[dict(goal='first step', candidate_ids=[self.did, 'invented'], obligations=['supply positivity'])])])])
        result = Engine(self.db, runtime, vectors=EmptyVectors()).search('growth bound')
        self.assertEqual(len(result['proof_ideas']), 1)
        self.assertEqual(result['proof_ideas'][0]['transfer'], 'iterate a new growth estimate')
        self.assertEqual(result['ingredient_sets'][0]['steps'][0]['candidate_ids'], [self.did])
        self.assertEqual(result['ingredient_sets'][0]['status'], 'not_verified')
        self.assertNotEqual(result.get('retrieval_assessment'), 'proved')

    def test_iterative_queries_are_recorded_and_duplicate_attempts_removed(self):
        runtime = FakeRuntime([dict(next_queries=['beta', 'beta', 'growth bound'], sufficient=False), dict(next_queries=[], sufficient=True)])
        result = Engine(self.db, runtime, vectors=EmptyVectors()).search('growth bound', options={'per_module': 0})
        self.assertEqual([q['query'] for q in result['query_trace']], ['growth bound', 'beta'])
        self.assertEqual({c['name'] for c in result['candidate_lemmas']}, {'A.alpha', 'beta'})

    def test_hybrid_does_not_call_reasoning_model(self):
        runtime = FakeRuntime()
        Engine(self.db, runtime, vectors=EmptyVectors()).search('alpha', mode='hybrid')
        self.assertFalse([c for c in runtime.calls if c[0] == 'generate'])

    def test_single_round_control_still_judges_but_does_not_expand(self):
        runtime = FakeRuntime([dict(next_queries=['beta'], sufficient=False)])
        result = Engine(self.db, runtime, vectors=EmptyVectors()).search('growth bound', options={'max_rounds': 1})
        self.assertEqual(result['max_rounds'], 1)
        self.assertEqual([q['query'] for q in result['query_trace']], ['growth bound'])
        self.assertEqual(len([c for c in runtime.calls if c[0] == 'generate']), 1)
        self.assertNotIn('beta', [c['name'] for c in result['candidate_lemmas']])

    def test_low_reranker_score_is_not_discarded_as_if_it_were_rrf(self):
        runtime = FakeRuntime()
        runtime.rerank = lambda query, documents, deadline: [.00001] * len(documents)
        result = Engine(self.db, runtime, vectors=EmptyVectors()).search('alpha', mode='hybrid')
        self.assertEqual(result['candidate_lemmas'][0]['reranker_score'], .00001)

    def test_context_reserves_space_for_proof_sources(self):
        candidate = Engine(self.db)._candidate({'decl_id': self.did})
        candidate['statement'] = 'long signature ' * 1000
        argument = {**candidate, 'proof_excerpt': 'rfl', 'method': None}
        context = json.loads(Engine(self.db)._context([candidate] * 20, [argument]))
        self.assertTrue(context['candidates'])
        self.assertEqual(context['source_arguments'][0]['proof'], 'rfl')
        self.assertFalse(context['source_arguments'][0]['statement_complete'])

    def test_incomplete_vectors_never_report_complete_search(self):
        vectors = EmptyVectors()
        vectors.coverage = lambda model: {'complete': False, 'expected': 10, 'ready': 1}
        result = Engine(self.db, FakeRuntime(), vectors=vectors).search('alpha', mode='hybrid')
        self.assertTrue(result['partial'])
        self.assertIn('semantic_index_incomplete', result['unfinished_stages'])

    def test_filters_apply_to_semantic_results_and_dependency_expansion(self):
        beta = self.db.search('beta')[0]['decl_id']
        with self.db.con:
            self.db.con.execute('INSERT INTO dependencies VALUES(?,?,?)', (self.did, 'beta', 'proof'))
        result = Engine(self.db).search('alpha', options={'exclude_modules': ['Other']})
        self.assertEqual([c['name'] for c in result['candidate_lemmas']], ['A.alpha'])

    def test_expired_budget_returns_immediately_without_inference(self):
        runtime = FakeRuntime()
        result = Engine(self.db, runtime, vectors=EmptyVectors()).search('alpha', budget_seconds=0)
        self.assertTrue(result['partial'])
        self.assertIn('deadline', result['unfinished_stages'])
        self.assertFalse(runtime.calls)

    def test_each_completed_lane_is_published_before_next_lane(self):
        snapshots = []
        search = self.db.search
        def observed(query, **kwargs):
            if kwargs['views'] == ('proof', 'method'):
                self.assertTrue(snapshots[-1]['candidate_lemmas'])
            return search(query, **kwargs)
        with patch.object(self.db, 'search', side_effect=observed):
            Engine(self.db).retrieve('alpha', options={}, deadline=time.monotonic() + 3,
                on_partial=lambda candidates, methods, prose: snapshots.append({'candidate_lemmas': candidates}))

    def test_candidates_precede_coverage_and_vector_setup(self):
        snapshots = []
        coverage = self.db.coverage
        def checked_coverage():
            self.assertTrue(any(r['candidate_lemmas'] for r in snapshots))
            return coverage()
        vectors = EmptyVectors()
        def checked_vectors(model):
            self.assertTrue(any(r['candidate_lemmas'] for r in snapshots))
            return {'complete': True, 'ready': 1, 'expected': 1}
        vectors.coverage = checked_vectors
        with patch.object(self.db, 'coverage', side_effect=checked_coverage):
            Engine(self.db, FakeRuntime(), vectors=vectors).search('alpha',
                progress=lambda r: snapshots.append(json.loads(json.dumps(r))))

    def test_semantic_candidates_are_published_before_reranking(self):
        snapshots = []
        vectors = EmptyVectors()
        vectors.search = lambda embedding, **kw: self.db.search('alpha') if 'statement' in kw['views'] else []
        runtime = FakeRuntime()
        def rerank(query, documents, *, deadline):
            self.assertTrue(snapshots[-1]['candidate_lemmas'])
            self.assertLess(deadline - time.monotonic(), 12)
            raise TimeoutError('reranking exhausted its stage budget')
        runtime.rerank = rerank
        r = Engine(self.db, runtime, vectors=vectors).search('unmatched', mode='hybrid',
            progress=lambda r: snapshots.append(json.loads(json.dumps(r))))
        self.assertEqual(r['candidate_lemmas'][0]['name'], 'A.alpha')
        self.assertIn('reranking', r['unfinished_stages'])
        self.assertIn('reranking exhausted its stage budget', [e['error'] for e in r['errors']])

    def test_long_deep_query_decomposes_into_explicit_short_queries(self):
        runtime = FakeRuntime([{'queries': ['growth AND bound', 'growth bound', 'beta']}, {'sufficient': True}])
        result = Engine(self.db, runtime, vectors=EmptyVectors()).search('use a uniform growth bound to constrain a parameter')
        self.assertIn('growth bound', [q['query'] for q in result['query_trace']])
        self.assertTrue(result['candidate_lemmas'])
        self.assertEqual(result['query_trace'][0]['lexical_operator'], 'AND')

    def test_long_goal_retains_explicit_lexical_candidates_when_planner_unavailable(self):
        runtime = FakeRuntime()
        snapshots = []
        def generate(prompt, **kwargs):
            self.assertTrue(any(r['candidate_lemmas'] for r in snapshots))
            raise TimeoutError('planner unavailable')
        runtime.generate = generate
        result = Engine(self.db, runtime).search('use a uniform growth bound to constrain a parameter',
            progress=lambda r: snapshots.append(json.loads(json.dumps(r))))
        self.assertTrue(result['candidate_lemmas'])
        self.assertTrue(any(q['origin'] == 'keyword_relaxation' for q in result['query_trace']))
        self.assertIn('planner unavailable', [e['error'] for e in result['errors']])

    def test_compact_judgment_ids_resolve_to_real_evidence(self):
        runtime = FakeRuntime([dict(sufficient=True, ingredient_sets=[dict(description='group',
            steps=[dict(goal='reuse growth estimate', candidate_ids=['c0'], obligations='supply h')])],
            proof_ideas=[dict(source_id='m0', transfer='reuse reflexivity', obligations='check the new goal', evidence='rfl')])])
        result = Engine(self.db, runtime, vectors=EmptyVectors()).search('growth bound')
        self.assertEqual(result['ingredient_sets'][0]['steps'][0]['candidate_ids'], [self.did])
        self.assertEqual(result['ingredient_sets'][0]['steps'][0]['obligations'], ['supply h'])
        self.assertEqual(result['proof_ideas'][0]['evidence'], ['rfl'])

    def test_readonly_search_and_optional_cache_work_during_writer_transaction(self):
        self.db.con.execute('BEGIN IMMEDIATE')
        self.addCleanup(self.db.con.rollback)
        with Corpus(self.db.directory, readonly=True) as reader:
            result = Engine(reader, FakeRuntime(), vectors=EmptyVectors()).search('alpha')
        self.assertTrue(result['candidate_lemmas'])
        self.assertFalse(result['partial'])

    def test_complete_result_cached_without_rerunning_model(self):
        runtime = FakeRuntime()
        engine = Engine(self.db, runtime, vectors=EmptyVectors())
        first = engine.search('alpha')
        count = len(runtime.calls)
        second = engine.search('alpha')
        self.assertFalse(first['partial'])
        self.assertTrue(second['cache_hit'])
        self.assertEqual(len(runtime.calls), count)

    def test_changed_generation_cannot_cache_old_retrieval_as_new(self):
        runtime = FakeRuntime()
        def generate(prompt, **kwargs):
            with self.db.con:
                self.db.bump(source=True)
            return '{"sufficient":true}'
        runtime.generate = generate
        result = Engine(self.db, runtime, vectors=EmptyVectors()).search('alpha')
        self.assertTrue(result['candidate_lemmas'])
        self.assertNotEqual(result['index_generation'], self.db.generation)
        self.assertEqual(self.db.con.execute('SELECT count(*) FROM cache').fetchone()[0], 0)

    def test_interrupted_multi_chunk_method_resumes_completed_chunks(self):
        from research_runtime.protocol import RuntimeDeadline
        d = self.db.declaration(self.did)
        with self.db.con:
            self.db.con.execute("DELETE FROM documents WHERE decl_id=? AND view='proof'", (self.did,))
            for text in ('by', '  rfl'):
                self.db._document(self.did, d['path'], d['module'], 'proof', text, 1, 2, {})
        class Runtime(FakeRuntime):
            def generate(inner, prompt, *, deadline, max_tokens, priority):
                inner.calls.append(('generate', prompt))
                if len(inner.calls) == 2:
                    raise RuntimeDeadline('interrupted batch')
                return json.dumps(dict(description='source operations', assumptions=[], steps=['reuse step'],
                    obligations=['check the new goal'], evidence_lines=[1]))
        runtime = Runtime()
        first = enrich(self.db, runtime, deadline=time.monotonic()+3, methods=True)
        self.assertEqual(first['methods'], 0)
        self.assertEqual(self.db.con.execute('SELECT count(*) FROM method_chunks').fetchone()[0], 1)
        second = enrich(self.db, runtime, deadline=time.monotonic()+3, methods=True)
        self.assertGreaterEqual(second['methods'], 1)
        first_chunk_calls = [p for op,p in runtime.calls if p.endswith('NUMBERED PROOF:\n1: by')]
        self.assertEqual(len(first_chunk_calls), 1)
        self.assertIsNotNone(self.db.method(self.did))


if __name__ == '__main__':
    unittest.main()
