from __future__ import annotations

import gzip
import io
import json
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from lean_research_corpus import Corpus
from lean_research_batch import embedding_spec, import_results, locks, snapshot, prepare, MATCH_INCOMING_SQL
from research_batch.format import (FORMAT, atomic_bytes, atomic_json, checked_file,
                                  descriptor, parity, read_shard, sha_file, validate_matrix)
from research_runtime.config import EMBEDDING_DIMENSIONS as DIMENSIONS
from research_batch.runner import run, validate_cuda
from lean_research_batch_sync import sync, owned_run


def unit(index):
    value = np.zeros(DIMENSIONS, dtype=np.float32)
    value[index % DIMENSIONS] = 1
    return value


class BatchTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.cache = self.root / 'cache'
        self.paths = []
        for folder, name in (('RHTower', 'alpha'), ('HTGeometry', 'beta'), ('Other', 'gamma')):
            path = self.root / 'formal' / folder / 'A.lean'
            path.parent.mkdir(parents=True)
            path.write_text(f'theorem {name} : True := by trivial\n')
            self.paths.append(path)
        with Corpus(self.cache) as corpus:
            corpus.refresh(self.root)
        self.stage = self.root / 'stage'
        self.stage.mkdir()
        self.bundle = self.root / 'bundle'
        self.output = self.root / 'results'
        (self.bundle / 'inputs').mkdir(parents=True)
        self.output.mkdir()
        self.model_patch = patch('lean_research_batch.installation_status', return_value={'embedding_model_version': 'm1'})
        self.model_patch.start()
        self.addCleanup(self.model_patch.stop)

    def make_bundle(self):
        meta = snapshot(self.cache, self.stage, 'm1')
        con = sqlite3.connect(self.stage / 'snapshot.sqlite3')
        shards = []
        self.hash_vectors = {}
        for i, (sha, text, priority, view) in enumerate(con.execute('SELECT * FROM texts ORDER BY priority,hash')):
            row = dict(hash=sha, text=text, view=view)
            path = self.bundle / 'inputs' / f'{i}.jsonl.gz'
            atomic_bytes(path, gzip.compress((json.dumps(row) + '\n').encode(), mtime=0))
            shards.append(descriptor(path, count=1, priority=priority))
            self.hash_vectors[sha] = unit(i)
        con.close()
        self.ref_vectors = np.array([unit(0), unit(1), unit(0), unit(1)], dtype=np.float32)
        reference = dict(documents=['doc 0', 'doc 1'], queries=['query 0', 'query 1'], vectors=self.ref_vectors.tolist())
        atomic_json(self.bundle / 'reference.json', reference)
        manifest = dict(meta, shards=shards, model_files=[], runner_files=[], support_files=[],
                        reference=descriptor(self.bundle / 'reference.json'))
        atomic_json(self.bundle / 'manifest.json', manifest)
        self.manifest = manifest
        return manifest

    def make_results(self):
        if not hasattr(self, 'manifest'):
            self.make_bundle()
        self.write_npy('audit-vectors.npy', self.ref_vectors)
        audit = dict(manifest_sha256=sha_file(self.bundle / 'manifest.json'),
                     reference_sha256=self.manifest['reference']['sha256'], target_model='m1',
                     environment=dict(device='cuda', dtype='bfloat16'),
                     vectors=descriptor(self.output / 'audit-vectors.npy'))
        atomic_json(self.output / 'audit.json', audit)
        for entry in self.manifest['shards']:
            rows = read_shard(self.bundle, entry)
            path = entry['name'] + '.npy'
            self.write_npy(path, np.array([self.hash_vectors[r['hash']] for r in rows]))
            atomic_json(self.output / (entry['name'] + '.done.json'),
                        dict(manifest_sha256=sha_file(self.bundle / 'manifest.json'),
                             input_sha256=entry['sha256'], audit_sha256=sha_file(self.output / 'audit.json'),
                             count=len(rows), vectors=descriptor(self.output / path)))

    def write_npy(self, name, matrix):
        stream = io.BytesIO()
        np.save(stream, matrix, allow_pickle=False)
        atomic_bytes(self.output / name, stream.getvalue())

    def imported(self):
        return import_results(self.cache, self.bundle, self.output, lock_seconds=.01)

    def test_snapshot_deduplicates_prioritizes_and_records_every_file(self):
        meta = self.make_bundle()
        con = sqlite3.connect(self.stage / 'snapshot.sqlite3')
        rows = con.execute('SELECT priority,text FROM texts ORDER BY priority').fetchall()
        self.assertEqual(meta['file_outcomes'], {'indexed': 3})
        self.assertEqual(meta['exported_document_references'], 6)
        self.assertEqual(meta['unique_pending'], 4)  # Three statements, one shared proof.
        self.assertEqual([p for p, _ in rows], [0, 0, 100, 200])
        self.assertEqual(con.execute('SELECT count(*) FROM files').fetchone()[0], 3)
        con.close()
        self.paths[0].write_text('theorem changed : True := trivial')
        with Corpus(self.cache) as corpus:
            corpus.refresh(self.root)
        self.assertEqual(snapshot(self.cache, self.stage, 'm1'), {k: v for k, v in meta.items()
            if k not in ('shards', 'model_files', 'runner_files', 'support_files', 'reference')})
        with self.assertRaisesRegex(ValueError, 'another model'):
            snapshot(self.cache, self.stage, 'm2')

    def test_prepare_requires_explicit_download_mode_for_missing_runtime_wheels(self):
        model = self.root / 'model'
        model.mkdir()
        (model / 'model.safetensors').write_bytes(b'fixture weights; never used for inference')
        record = descriptor(model / 'model.safetensors')
        (self.cache / 'runtime').mkdir()
        atomic_json(self.cache / 'runtime' / 'installed.json', dict(models=dict(embedding=dict(
            files={'model.safetensors': {k: v for k, v in record.items() if k != 'name'}}))))
        reference = dict(documents=['a', 'b'], queries=['q'], vectors=[unit(0).tolist()] * 3)
        with patch('lean_research_batch.installation_status', return_value=dict(ready=True,
                   embedding_model_version='m1', models=dict(embedding=dict(path=str(model))))), \
             patch('lean_research_batch.saved_reference', return_value=reference):
            directory = self.root / 'prepared'
            with self.assertRaisesRegex(ValueError, 'Prefetch Linux wheel'):
                prepare(self.cache, directory)
            self.assertFalse((directory / 'bundle' / 'manifest.json').exists())
            manifest = prepare(self.cache, directory, download_runtime=True)
            self.assertFalse(manifest['offline_setup_ready'])
            self.assertIn('torch==2.8.0+cu129', manifest['pending_runtime_wheels'])
            self.assertEqual(manifest['unique_pending'], 4)
            self.assertEqual(manifest['file_outcomes'], {'indexed': 3})

    def test_snapshot_excludes_cached_hashes_and_import_is_idempotent(self):
        self.make_results()
        self.assertEqual(self.imported()['published'], 6)
        self.assertEqual(self.imported()['published'], 0)
        next_stage = self.root / 'next'
        next_stage.mkdir()
        meta = snapshot(self.cache, next_stage, 'm1')
        self.assertEqual(meta['unique_pending'], 0)
        self.assertEqual(meta['cached_documents'], 6)

    def test_cuda_provenance_survives_compaction(self):
        self.make_results()
        self.imported()
        from lean_research_vectors import Vectors
        with Corpus(self.cache) as corpus:
            original = {r[0]: json.loads(r[1]) for r in corpus.con.execute(
                "SELECT key,value FROM meta WHERE key LIKE 'vector_provenance:%'")}
            self.assertEqual(len(original), 4)
            self.assertTrue(all(p['kind'] == 'cuda_batch' for p in original.values()))
            Vectors(corpus).compact('m1')
            current = corpus.con.execute('SELECT DISTINCT shard FROM vectors').fetchone()[0]
            provenance = json.loads(corpus.con.execute('SELECT value FROM meta WHERE key=?',
                                                     ('vector_provenance:' + current,)).fetchone()[0])
            self.assertEqual({'vector_provenance:' + p for p in provenance['parent_shards']}, set(original))

    def test_edits_deletions_and_moved_ids_match_only_current_content(self):
        self.make_results()
        self.paths[0].write_text('-- added line\ntheorem alpha : True := by trivial\n')
        self.paths[1].write_text('theorem newBeta : True := by trivial\n')
        self.paths[2].unlink()
        with Corpus(self.cache) as corpus:
            corpus.refresh(self.root)
        report = self.imported()
        self.assertEqual(report['published'], 3)  # alpha statement, two shared proofs.
        with Corpus(self.cache, readonly=True) as corpus:
            rows = corpus.con.execute('SELECT d.text FROM vectors v JOIN documents d ON d.id=v.doc_id').fetchall()
            self.assertTrue(any('alpha' in r[0] for r in rows))
            self.assertFalse(any('beta' in r[0] or 'gamma' in r[0] or 'newBeta' in r[0] for r in rows))

    def test_incomplete_outputs_are_partial_and_resume(self):
        self.make_results()
        marker = self.output / (self.manifest['shards'][0]['name'] + '.done.json')
        saved = marker.read_bytes()
        marker.unlink()
        first = self.imported()
        self.assertTrue(first['partial'])
        self.assertEqual(first['pending_shards'], 1)
        atomic_bytes(marker, saved)
        second = self.imported()
        self.assertFalse(second['partial'])
        self.assertEqual(first['published'] + second['published'], 6)

    def test_budget_preserves_completed_shards(self):
        self.make_results()
        report = import_results(self.cache, self.bundle, self.output, budget_seconds=0)
        self.assertTrue(report['partial'])
        self.assertEqual(report['published'], 0)
        self.assertEqual(self.imported()['published'], 6)

    def test_wrong_model_or_preprocessing_never_publishes(self):
        self.make_results()
        with patch('lean_research_batch.installation_status', return_value={'embedding_model_version': 'm2'}):
            with self.assertRaisesRegex(ValueError, 'model changed'):
                self.imported()
        self.manifest['spec']['context_tokens'] = 512
        atomic_json(self.bundle / 'manifest.json', self.manifest)
        with self.assertRaisesRegex(ValueError, 'model changed'):
            self.imported()
        with Corpus(self.cache, readonly=True) as corpus:
            self.assertEqual(corpus.con.execute('SELECT count(*) FROM vectors').fetchone()[0], 0)

    def test_corrupt_result_rejected_without_publication(self):
        self.make_results()
        path = self.output / (self.manifest['shards'][0]['name'] + '.npy')
        path.write_bytes(path.read_bytes()[:-4] + b'BAD!')
        with self.assertRaisesRegex(ValueError, 'checksum'):
            self.imported()
        with Corpus(self.cache, readonly=True) as corpus:
            self.assertEqual(corpus.con.execute('SELECT count(*) FROM vectors').fetchone()[0], 0)

    def test_false_audit_claim_cannot_bypass_recomputed_parity(self):
        self.make_results()
        self.write_npy('audit-vectors.npy', -self.ref_vectors)
        path = self.output / 'audit.json'
        report = json.loads(path.read_text())
        report.update(passed=True, vectors=descriptor(self.output / 'audit-vectors.npy'))
        atomic_json(path, report)
        with self.assertRaisesRegex(ValueError, 'numerical compatibility'):
            self.imported()

    def test_invalid_matrix_and_path_traversal_are_rejected(self):
        for value in (np.zeros((1, DIMENSIONS), dtype=np.float32), np.array([unit(0)], dtype=np.float64),
                      np.full((1, DIMENSIONS), np.nan, dtype=np.float32), np.ones((1, 4), dtype=np.float32)):
            with self.assertRaises(ValueError):
                validate_matrix(value, 1, DIMENSIONS)
        # The width is never a module constant: a model swap must not pass.
        with self.assertRaisesRegex(ValueError, 'dimensions'):
            validate_matrix(np.array([unit(0)], dtype=np.float32), 1, DIMENSIONS // 2)
        for bad in (None, 1024.0, 4, 1 << 20):
            with self.assertRaisesRegex(ValueError, 'bundle spec'):
                validate_matrix(np.array([unit(0)], dtype=np.float32), 1, bad)
        with self.assertRaisesRegex(ValueError, 'filename'):
            checked_file(self.root, dict(name='../escape', size=0, sha256='x'))

    def test_query_whitespace_exactly_matches_local_embedding_template(self):
        from research_runtime.adapters import embedding_text
        for text in ('entropy', ' ∀ x, f x ≥ 0', 'line one\nline two', '{x} → x'):
            self.assertEqual(embedding_spec()['query_template'].format(text=text), embedding_text(text, True))

    def test_b300_requires_prepared_cuda_and_never_falls_back_to_cpu(self):
        def fake(capability=(10, 3), cuda='12.9', available=True, count=1):
            return SimpleNamespace(version=SimpleNamespace(cuda=cuda), cuda=SimpleNamespace(
                is_available=lambda: available, device_count=lambda: count,
                get_device_capability=lambda _: capability))
        validate_cuda(fake())
        validate_cuda(fake(capability=(10, 0), cuda='12.8'))
        for options in (dict(cuda='12.8'), dict(available=False), dict(count=2), dict(capability=(9, 0))):
            with self.assertRaises(RuntimeError):
                validate_cuda(fake(**options))

    def test_input_hash_mismatch_detected_even_with_updated_file_checksum(self):
        self.make_bundle()
        entry = self.manifest['shards'][0]
        path = self.bundle / 'inputs' / entry['name']
        rows = read_shard(self.bundle, entry)
        rows[0]['text'] = 'wrong source'
        path.write_bytes(gzip.compress((json.dumps(rows[0]) + '\n').encode()))
        entry.update(descriptor(path))
        with self.assertRaisesRegex(ValueError, 'source hash'):
            read_shard(self.bundle, entry)

    def test_maintenance_lock_contention_is_bounded(self):
        self.make_results()
        with locks([self.cache / 'enrichment.lock'], seconds=0):
            with self.assertRaisesRegex(TimeoutError, 'Maintenance busy'):
                self.imported()
        self.assertEqual(self.imported()['published'], 6)

    def test_shard_matching_does_not_rescan_whole_corpus(self):
        con = sqlite3.connect(':memory:')
        self.addCleanup(con.close)
        con.executescript('CREATE TABLE batch_current(id INTEGER,content_hash TEXT); '
            'CREATE INDEX batch_hash ON batch_current(content_hash); '
            'CREATE TABLE batch_incoming(hash TEXT PRIMARY KEY,position INTEGER);')
        con.executemany('INSERT INTO batch_current VALUES(?,?)', [(i, str(i)) for i in range(10000)])
        con.execute("INSERT INTO batch_incoming VALUES('9000',0)")
        # A corpus scan exceeds this VM instruction budget. One indexed probe
        # does not; this checks actual query work, not the SQL's spelling.
        con.set_progress_handler(lambda: 1, 1000)
        self.assertEqual(con.execute(MATCH_INCOMING_SQL).fetchall(), [(9000, '9000', 0)])

    def test_real_readers_keep_committed_results_during_import_transaction(self):
        self.make_results()
        from lean_research_vectors import Vectors
        original = Vectors.publish
        observations = []
        def publish(vectors, docs, matrix, model, **kwargs):
            with Corpus(self.cache, readonly=True) as reader:
                observations.append(reader.con.execute('SELECT count(*) FROM documents').fetchone()[0])
            return original(vectors, docs, matrix, model, **kwargs)
        with patch.object(Vectors, 'publish', publish):
            self.assertEqual(self.imported()['published'], 6)
        self.assertTrue(observations and all(n >= 6 for n in observations))

    def test_runner_pilot_resume_and_cpu_audit_cannot_publish(self):
        self.make_bundle()
        vectors = self.hash_vectors
        calls = []
        class FakeEncoder:
            torch = SimpleNamespace(cuda=SimpleNamespace(max_memory_allocated=lambda: 123))
            def __init__(self, *args, **kwargs):
                self.cpu = kwargs['cpu_audit']
            def encode(self, texts, query=False):
                from research_batch.format import sha_text
                calls.extend(texts)
                values = [unit(int(t[-1])) if t.startswith(('doc ', 'query ')) else vectors[sha_text(t)] for t in texts]
                return np.array(values), len(texts)
            def environment(self):
                return dict(device='cpu' if self.cpu else 'cuda', dtype='bfloat16', attention='sdpa',
                            gpu='test', capability=[10, 0], cuda='12.8', packages={})
        args = SimpleNamespace(bundle=self.bundle, output=self.output, dtype='bfloat16', cpu_audit=True,
                               token_budget=2048, max_batch=4, max_shards=1)
        with patch('research_batch.runner.Encoder', FakeEncoder):
            run(args)
            self.assertFalse((self.output / 'audit.json').exists())
            args.cpu_audit = False
            run(args)
            self.assertEqual(len(list(self.output.glob('*.done.json'))), 1)
            self.assertFalse(json.loads((self.output / 'run.json').read_text())['complete'])
            args.max_shards = 0
            calls.clear()
            run(args)
            self.assertEqual(len(calls), len(self.manifest['shards']) - 1)
            self.assertTrue(json.loads((self.output / 'run.json').read_text())['complete'])
        self.assertEqual(self.imported()['published'], 6)

    def sync_connection(self):
        atomic_json(self.root / 'connection.json', dict(host='127.0.0.1', port=22, user='root',
                    identity_file=str(self.root / 'unused-key'), remote_directory='/workspace/lean-embedding'))

    def test_sync_stops_only_after_verified_snapshot_is_fully_imported(self):
        self.make_bundle()
        self.sync_connection()
        atomic_json(self.output / 'run.json', dict(complete=True,
                    manifest_sha256=sha_file(self.bundle / 'manifest.json')))
        report = dict(published=6, partial=False, checked_shards=len(self.manifest['shards']))
        with patch('lean_research_batch_sync.owned_run', return_value='') as command, \
             patch('lean_research_batch_sync.import_results', return_value=report):
            state = sync(self.root, cache=self.cache, interval=0)
        self.assertTrue(state['completed'])
        self.assertFalse(state['running'])
        self.assertEqual(state['total_published'], 6)
        self.assertEqual(command.call_count, 1)  # No needless SSH polling after verified completion.
        with patch('lean_research_batch_sync.owned_run', return_value=''), \
             patch('lean_research_batch_sync.import_results', return_value={**report, 'published': 0}):
            self.assertEqual(sync(self.root, cache=self.cache, interval=0)['total_published'], 6)

    def test_sync_reports_dead_gpu_worker_instead_of_waiting_forever(self):
        self.make_bundle()
        self.sync_connection()
        atomic_json(self.output / 'run.json', dict(complete=False))
        with patch('lean_research_batch_sync.owned_run', side_effect=['', '{"pid":123,"running":false}']), \
             patch('lean_research_batch_sync.import_results', return_value=dict(published=1, partial=True)):
            with self.assertRaisesRegex(ValueError, 'GPU worker stopped'):
                sync(self.root, cache=self.cache, interval=0)
        state = json.loads((self.root / 'sync-status.json').read_text())
        self.assertEqual(state['phase'], 'failed')
        self.assertFalse(state['running'])

    def test_sync_redownloads_when_gpu_finishes_after_previous_download(self):
        self.make_bundle()
        self.sync_connection()
        atomic_json(self.output / 'run.json', dict(complete=False))
        complete = dict(complete=True, manifest_sha256=sha_file(self.bundle / 'manifest.json'),
                        completed_shards=len(self.manifest['shards']))
        def next_download(*args, **kwargs):
            atomic_json(self.output / 'run.json', complete)
            return ''
        responses = iter(['', json.dumps(dict(pid=123, running=False, run=complete))])
        def command(*args, **kwargs):
            return next(responses, None) if command.calls < 3 else next_download()
        command.calls = 0
        def dispatch(*args, **kwargs):
            command.calls += 1
            return command(*args, **kwargs)
        reports = [dict(published=1, partial=True),
                   dict(published=5, partial=False, checked_shards=len(self.manifest['shards']))]
        with patch('lean_research_batch_sync.owned_run', side_effect=dispatch), \
             patch('lean_research_batch_sync.import_results', side_effect=reports):
            state = sync(self.root, cache=self.cache, interval=0)
        self.assertTrue(state['completed'])
        self.assertEqual(state['total_published'], 6)
        self.assertEqual(command.calls, 3)

    def test_sync_does_not_accept_another_jobs_remote_completion(self):
        self.make_bundle()
        self.sync_connection()
        atomic_json(self.output / 'run.json', dict(complete=False))
        remote = dict(pid=123, running=False, run=dict(complete=True, manifest_sha256='wrong'))
        with patch('lean_research_batch_sync.owned_run', side_effect=['', json.dumps(remote)]), \
             patch('lean_research_batch_sync.import_results', return_value=dict(published=0, partial=True)):
            with self.assertRaisesRegex(ValueError, 'GPU worker stopped'):
                sync(self.root, cache=self.cache, interval=0)

    def test_transfer_timeout_reaps_owned_process(self):
        original = subprocess.Popen
        children = []
        def launch(*args, **kwargs):
            child = original(*args, **kwargs)
            children.append(child)
            return child
        with patch('lean_research_batch_sync.subprocess.Popen', side_effect=launch):
            with self.assertRaises(subprocess.TimeoutExpired):
                owned_run([sys.executable, '-c', 'import time; time.sleep(30)'], timeout=.03)
        self.assertEqual(len(children), 1)
        self.assertIsNotNone(children[0].poll())


if __name__ == '__main__':
    unittest.main()
