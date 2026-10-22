from __future__ import annotations

import json
import sqlite3
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from lean_research_corpus import Corpus
from lean_research_engine import (Engine, json_object, reciprocal_rank_fusion, method_payload,
                                  enrich, pending_method_ids, METHOD_PROMPT_VERSION)


class FakeRuntime:
    def __init__(self, answers=()):
        self.answers = list(answers)
        self.calls = []

    def status(self):
        return {'available': True, 'embedding_model': 'fake', 'generation_model': 'fake',
                'models': {'embedding': {}, 'reranker': {}, 'generation': {}}}

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
    def __init__(self):
        self.searches = []

    def coverage(self, model, *, measure=False):
        return {'complete': True, 'expected': 1, 'ready': 1}

    def measure_coverage(self, model):
        return {'complete': True, 'expected': 1, 'ready': 1, 'status': 'measured'}

    def search(self, embedding, **kwargs):
        self.searches.append(kwargs.get('views'))
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
    def test_progress_reuses_records_and_external_commits_invalidate_them(self):
        engine = Engine(self.db)
        hit = {'decl_id': self.did, 'view': 'proof'}
        with patch.object(self.db, 'declaration', wraps=self.db.declaration) as declaration:
            first = engine._method_candidate(hit)
            second = engine._method_candidate(hit)
            self.assertEqual(first, second)
            self.assertEqual(declaration.call_count, 1)
            # A commit without bumping the application generation must count.
            other = sqlite3.connect(self.db.directory/'corpus.sqlite3')
            try:
                with other:
                    other.execute('UPDATE declarations SET statement=? WHERE id=?', ('changed hypothesis', self.did))
            finally:
                other.close()
            self.assertEqual(engine._candidate(hit)['statement'], 'changed hypothesis')
            self.assertEqual(declaration.call_count, 2)
            with self.db.con:
                self.db.con.execute('UPDATE declarations SET statement=? WHERE id=?', ('local edit', self.did))
            self.assertEqual(engine._candidate(hit)['statement'], 'local edit')

    def test_method_invalidation_is_not_hidden_by_record_cache(self):
        self.db.save_method(self.did, dict(description='reflexivity', assumptions=[], steps=[], obligations=[], evidence=['rfl']),
                            model_version='m', prompt_version='p')
        engine = Engine(self.db)
        hit = {'decl_id': self.did, 'view': 'method'}
        self.assertIsNotNone(engine._method_candidate(hit))
        with self.db.con:
            self.db.con.execute("UPDATE methods SET status='stale' WHERE decl_id=?", (self.did,))
        self.assertIsNone(engine._method_candidate(hit))

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

    def test_generation_cannot_overwrite_descriptions_awaiting_recovery(self):
        payload = dict(description='use reflexivity', assumptions=[], steps=[], obligations=[], evidence=['rfl'])
        self.db.save_method(self.did, payload, model_version='gpu', prompt_version='v')
        with self.db.con:
            self.db.con.execute("UPDATE methods SET status='stale'")
            self.db.con.execute("INSERT INTO meta VALUES('method-recovery:snapshot','{\"partial\":true}')")
        runtime = FakeRuntime()
        report = enrich(self.db, runtime, deadline=time.monotonic()+5, methods=True)
        self.assertEqual(report['deferred'][0]['reason'], 'stored_method_recovery')
        self.assertFalse(runtime.calls)
        self.assertEqual(self.db.con.execute('SELECT description FROM methods').fetchone()[0], payload['description'])

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

    def test_expansion_budget_reserves_judgment_and_reports_skipped_queries(self):
        runtime = FakeRuntime()
        engine = Engine(self.db, runtime, vectors=EmptyVectors())
        candidate = engine._candidate({'decl_id': self.did})
        now = [1000.]
        def retrieve(query, **kwargs):
            self.assertAlmostEqual(kwargs['deadline'], 1060.)
            now[0] = kwargs['deadline'] + .01
            return [candidate], [], []
        def judge(query, candidates, methods, deadline):
            self.assertGreater(deadline-now[0], 29)
            self.assertEqual(candidates[0]['id'], self.did)
            return dict(sufficient=True, ingredient_sets=[dict(description='reuse bound', steps=[
                dict(goal='apply estimate', candidate_ids=[self.did], obligations=['supply positivity'])])])
        with patch('lean_research_engine.time.monotonic', side_effect=lambda: now[0]), \
                patch.object(engine, 'retrieve', side_effect=retrieve), \
                patch.object(engine, '_judge', side_effect=judge):
            result = engine.search('uniform growth bound forces parameter zero', budget_seconds=90)
        self.assertTrue(result['ingredient_sets'])
        self.assertTrue(result['partial'])
        self.assertTrue(any(s.startswith('query:') for s in result['unfinished_stages']))
        self.assertNotIn('deadline', result['unfinished_stages'])

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

    def test_completed_search_keeps_incomplete_vector_coverage_explicit(self):
        vectors = EmptyVectors()
        vectors.coverage = lambda model: {'complete': False, 'expected': 10, 'ready': 1}
        result = Engine(self.db, FakeRuntime(), vectors=vectors).search('alpha', mode='hybrid')
        self.assertFalse(result['partial'])
        self.assertFalse(result['unfinished_stages'])
        self.assertIn('semantic_index_incomplete', result['index_warnings'])
        self.assertFalse(result['semantic_coverage']['complete'])
        self.assertTrue(result['candidate_lemmas'])

    def test_coverage_failure_cannot_prevent_semantic_retrieval(self):
        vectors = EmptyVectors()
        searched = []
        def search(embedding, **kwargs):
            searched.append(kwargs['views'])
            return self.db.search('alpha') if 'statement' in kwargs['views'] else []
        def coverage(model):
            self.assertTrue(searched)
            raise sqlite3.OperationalError('interrupted')
        vectors.search, vectors.coverage = search, coverage
        result = Engine(self.db, FakeRuntime(), vectors=vectors).search('unmatched', mode='hybrid')
        self.assertEqual(result['candidate_lemmas'][0]['name'], 'A.alpha')
        self.assertFalse(result['partial'])
        self.assertFalse(result['errors'])
        self.assertIsNone(result['semantic_coverage']['complete'])
        self.assertIn('semantic_coverage_unavailable', result['index_warnings'])

    def test_indexer_snapshot_avoids_recount_and_exposes_its_generation(self):
        (self.db.directory / 'indexer.json').write_text(json.dumps(dict(updated_at=123,
            coverage=dict(generation=0, pending_files=1, method_invalidation_pending=True))))
        with patch.object(self.db, 'coverage', side_effect=AssertionError('redundant corpus count')):
            result = Engine(self.db, FakeRuntime(), vectors=EmptyVectors()).search('alpha', mode='hybrid')
        self.assertFalse(result['partial'])
        self.assertEqual(result['coverage']['generation'], 0)
        self.assertEqual(result['coverage']['current_generation'], self.db.generation)
        self.assertEqual(result['coverage']['snapshot_written_at'], 123)
        self.assertIn('source_index_incomplete', result['index_warnings'])
        self.assertIn('method_dependency_refresh', result['index_warnings'])

    def test_slow_optional_counts_do_not_consume_search_budget(self):
        vectors = EmptyVectors()
        def coverage(model):
            self.db.con.execute('WITH RECURSIVE n(x) AS (VALUES(1) UNION ALL '
                'SELECT x+1 FROM n WHERE x<100000000) SELECT sum(x) FROM n').fetchone()
            raise AssertionError('count was not interrupted')
        vectors.coverage = coverage
        started = time.monotonic()
        result = Engine(self.db, FakeRuntime(), vectors=vectors).search('alpha', mode='hybrid', budget_seconds=5)
        self.assertLess(time.monotonic()-started, 2)
        self.assertFalse(result['partial'])
        self.assertTrue(result['candidate_lemmas'])
        self.assertIn('semantic_coverage_unavailable', result['index_warnings'])
        self.assertEqual(self.db.con.execute('SELECT 1').fetchone()[0], 1)

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
            self.assertGreater(deadline - time.monotonic(), 55)
            self.assertLessEqual(deadline - time.monotonic(), 60)
            raise TimeoutError('reranking exhausted its stage budget')
        runtime.rerank = rerank
        r = Engine(self.db, runtime, vectors=vectors).search('unmatched', mode='hybrid',
            progress=lambda r: snapshots.append(json.loads(json.dumps(r))))
        self.assertEqual(r['candidate_lemmas'][0]['name'], 'A.alpha')
        self.assertIn('reranking', r['unfinished_stages'])
        self.assertIn('reranking exhausted its stage budget', [e['error'] for e in r['errors']])

    def test_longer_stage_budgets_still_respect_explicit_request_deadline(self):
        for budget in (300, 1):
            with self.subTest(budget=budget):
                limits = {}
                runtime = FakeRuntime()
                vectors = EmptyVectors()
                search = self.db.search
                def text_search(*args, **kwargs):
                    limits.setdefault('text', []).append(kwargs['deadline']-time.monotonic())
                    return search(*args, **kwargs)
                def embed(texts, *, query, deadline):
                    limits['embedding'] = deadline-time.monotonic()
                    return [[1., 0.]]
                def rerank(query, documents, *, deadline):
                    limits['reranking'] = deadline-time.monotonic()
                    return [1.] * len(documents)
                def generate(prompt, *, deadline, max_tokens):
                    limits['judgment'] = deadline-time.monotonic()
                    return '{"sufficient":true}'
                runtime.embed, runtime.rerank, runtime.generate = embed, rerank, generate
                engine = Engine(self.db, runtime, vectors=vectors)
                retrieve = engine.retrieve
                def capture(*args, **kwargs):
                    limits['retrieval'] = kwargs['deadline']-time.monotonic()
                    return retrieve(*args, **kwargs)
                with patch.object(self.db, 'search', side_effect=text_search), \
                        patch.object(engine, 'retrieve', side_effect=capture):
                    result = engine.search('alpha', budget_seconds=budget)
                self.assertTrue(result['candidate_lemmas'])
                for stage, cap in (('embedding',30),('reranking',60),('judgment',60),('retrieval',90)):
                    self.assertLessEqual(limits[stage], min(cap,budget))
                    self.assertGreater(limits[stage], cap-1 if budget==300 else 0)
                for left in limits['text']:
                    self.assertLessEqual(left,min(10,budget))
                    self.assertGreater(left,9 if budget==300 else 0)

    def test_retrieval_only_runtime_skips_generation_stages_without_errors(self):
        """No generation model pinned: deep mode must still retrieve and must
        not report decomposition or judgment as failed stages."""
        class Retrieval(FakeRuntime):
            def status(self):
                return {'available': True, 'embedding_model': 'fake',
                        'models': {'embedding': {}, 'reranker': {}}}
            def generate(self, *args, **kwargs):
                raise AssertionError('no generation model is pinned')
        engine = Engine(self.db, Retrieval(), vectors=EmptyVectors())
        self.assertFalse(engine.can_generate)
        result = engine.search('growth bound', mode='deep')
        self.assertTrue(result['candidate_lemmas'])
        self.assertEqual([e['stage'] for e in result['errors']], [])
        self.assertNotIn('decomposition', result['unfinished_stages'])
        self.assertNotIn('filter_and_judge', result['unfinished_stages'])

    def test_deep_mode_long_query_still_reaches_the_vector_index(self):
        """Only the keyword relaxations are lexical; the user's own query keeps
        its vector lane and its reranking pass."""
        runtime = FakeRuntime([{'sufficient': True}])
        vectors = EmptyVectors()
        goal = 'use a uniform growth bound to constrain a parameter'
        result = Engine(self.db, runtime, vectors=vectors).search(goal, options={'max_rounds': 1})
        relaxed = [q['query'] for q in result['query_trace'] if q['origin'] == 'keyword_relaxation']
        self.assertTrue(relaxed, 'this goal must produce keyword relaxations')
        self.assertTrue(vectors.searches, 'the user query must reach the vector lane')
        embedded = [texts for kind, texts in runtime.calls if kind == 'embed']
        self.assertIn([goal], embedded)
        self.assertNotIn(relaxed[0], [t for texts in embedded for t in texts])

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

    def test_pending_methods_keep_priority_limit_and_valid_producer_results(self):
        root = Path(self.tmp.name)
        for path, text in {
            'formal/RHTower/Z.lean': '\n'.join('theorem '+n+' : True := trivial' for n in
                ('localReady','gpuReady','localFailed','staleMethod','afterStale')),
            'formal/HTGeometry/A.lean': 'theorem geometryPending : True := trivial',
        }.items():
            p = root/path; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(text)
        self.db.refresh(root)
        ids = {r['name']:r['id'] for r in self.db.con.execute('SELECT name,id FROM declarations')}
        payload = dict(description='use witness', assumptions=[], steps=[], obligations=[], evidence=['trivial'])
        for name, model in [('localReady','local'),('gpuReady','gpu'),('localFailed','local'),('staleMethod','local')]:
            self.db.save_method(ids[name], payload, model_version=model, prompt_version=METHOD_PROMPT_VERSION)
        with self.db.con:
            self.db.con.execute("UPDATE methods SET status='failed' WHERE decl_id=?", (ids['localFailed'],))
            self.db.con.execute("UPDATE methods SET status='stale' WHERE decl_id=?", (ids['staleMethod'],))
        rows = pending_method_ids(self.db, 'local', ['local','gpu'], limit=3)
        self.assertEqual([r[0] for r in rows], [ids['staleMethod'],ids['afterStale'],ids['geometryPending']])
        self.assertEqual(pending_method_ids(self.db, 'local', ['local','gpu'], limit=1)[0][0], ids['staleMethod'])
        self.assertEqual(pending_method_ids(self.db, 'local', ['local','gpu'], limit=0), [])

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

    def test_invalid_evidence_retries_once_and_only_saves_valid_source_lines(self):
        source = Path(self.tmp.name) / 'formal/Amplifier.lean'
        source.write_text('private abbrev XiWeilCarrier := lp (fun _ : XiZeroCopy => ℂ) 2\n\n'
                          '/-- Next declaration description. -/')
        self.db.refresh(Path(self.tmp.name))
        did = self.db.search('XiWeilCarrier')[0]['decl_id']
        answers = []
        def generate(prompt, **kwargs):
            repair = 'Previous attempt failed validation:' in prompt
            if 'XiWeilCarrier' in prompt:
                answers.append(prompt)
                if repair:
                    self.assertIn('Valid evidence line numbers: [1]', prompt)
            return json.dumps(dict(description='applies the displayed constant', assumptions=[],
                steps=['apply the constant'], obligations=['check the target'], evidence_lines=[1 if repair else 2]))
        runtime = FakeRuntime(); runtime.generate = generate
        result = enrich(self.db, runtime, deadline=time.monotonic()+3, methods=True)
        self.assertFalse(result['failures'])
        self.assertEqual(len(answers), 2)
        self.assertEqual(self.db.method(did)['evidence'], ['lp (fun _ : XiZeroCopy => ℂ) 2'])

    def test_invalid_repair_stays_failed_without_unbounded_retries(self):
        calls = []
        def generate(prompt, **kwargs):
            calls.append(prompt)
            return json.dumps(dict(description='invalid reference', assumptions=[], steps=[],
                obligations=[], evidence_lines=[999]))
        runtime = FakeRuntime(); runtime.generate = generate
        result = enrich(self.db, runtime, deadline=time.monotonic()+3, methods=True)
        self.assertEqual(result['methods'], 0)
        self.assertEqual(len(calls), 4)  # Two declarations, one retry each.
        self.assertEqual(len(result['failures']), 2)
        self.assertIsNone(self.db.method(self.did))

    def test_expired_enrichment_does_not_start_coverage_scan(self):
        with patch.object(self.db, 'coverage', side_effect=AssertionError('scan after deadline')):
            result = enrich(self.db, FakeRuntime(), deadline=time.monotonic()-1, methods=True)
        self.assertIn(dict(stage='coverage', reason='deadline'), result['deferred'])

    def test_coverage_sql_is_interrupted_and_connection_remains_usable(self):
        def slow_coverage():
            return self.db.con.execute('WITH RECURSIVE n(x) AS (VALUES(1) UNION ALL '
                'SELECT x+1 FROM n WHERE x<100000000) SELECT sum(x) FROM n').fetchone()
        started = time.monotonic()
        with patch.object(self.db, 'coverage', side_effect=slow_coverage):
            result = enrich(self.db, FakeRuntime(), deadline=started+.05)
        self.assertLess(time.monotonic()-started, .5)
        self.assertIn(dict(stage='coverage', reason='deadline'), result['deferred'])
        self.assertEqual(self.db.con.execute('SELECT 1').fetchone()[0], 1)


if __name__ == '__main__':
    unittest.main()
