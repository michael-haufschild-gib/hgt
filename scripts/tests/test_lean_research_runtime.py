"""Runtime contract tests: no model downloads or Lean builds.

Fakes run in actual spawned child processes behind the production Unix socket.
Optional local tokenizer test skips until explicit setup has installed weights.
"""
from __future__ import annotations

import concurrent.futures
import contextlib
import hashlib
import json
import math
import multiprocessing
import os
from pathlib import Path
import signal
import socket
import struct
import subprocess
import sys
import tempfile
import time
import unittest
from types import SimpleNamespace
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import lean_research_runtime as runtime
import lean_research_setup as setup
from research_runtime import adapters, config, protocol, worker


def fake_child(pipe, cache_dir):
    """Deliberately blocking backend exercises parent-enforced cancellation."""
    root = Path(cache_dir)
    try:
        while True:
            req = pipe.recv()
            name = req.get('prompt', req.get('texts', ['rerank'])[0])
            with (root / 'events').open('a') as log:
                log.write(json.dumps(['start', name, os.getpid(), time.monotonic()]) + '\n')
            if name == 'crash':
                os._exit(17)
            if name == 'partial-frame':
                pipe.sock.sendall(struct.pack('!I', 1000) + b'{')
                time.sleep(5)
            if name.startswith('slow'):
                time.sleep(5)
            else:
                time.sleep(0.06)
            value = ([[float(len(s))] for s in req['texts']] if req['op'] == 'embed'
                     else [0.25] * len(req['documents']) if req['op'] == 'rerank' else name)
            with (root / 'events').open('a') as log:
                log.write(json.dumps(['end', name, os.getpid(), time.monotonic()]) + '\n')
            pipe.send({'result': value, 'devices': {}})
    except (EOFError, BrokenPipeError):
        pass
    finally:
        pipe.close()


def serve_fake(cache_dir):
    server = worker.WorkerServer(Path(cache_dir), child_target=fake_child, idle_seconds=30)
    def stop(*args):
        server.stopping = True
    signal.signal(signal.SIGTERM, stop)
    server.serve()


class FakeTokenizer:
    unk_token_id = 0
    def encode(self, text, add_special_tokens=False):
        if text in ('yes', 'no'):
            return [11 if text == 'yes' else 7]
        return list(text.encode())
    def convert_tokens_to_ids(self, word):
        return {'yes': 11, 'no': 7, 'true': 101, 'false': 102}.get(word, 0)
    def __call__(self, texts, **kwargs):
        self.kwargs = kwargs
        return {'input_ids': [self.encode(t)[:kwargs['max_length']] for t in texts]}
    def pad(self, inputs, **kwargs):
        self.pad_kwargs = kwargs
        return inputs


class ContractTests(unittest.TestCase):
    def test_import_and_missing_setup_never_import_or_download_models(self):
        script = '''
import sys,tempfile,socket
from pathlib import Path
from unittest.mock import patch
import lean_research_runtime as r
with tempfile.TemporaryDirectory() as d:
 with patch('socket.getaddrinfo', side_effect=AssertionError('network')), patch('subprocess.Popen', side_effect=AssertionError('spawn')):
  c=r.RuntimeClient(Path(d)); assert not c.status()['ready']
  try: c.embed(['x'],deadline=__import__('time').monotonic()+1)
  except r.RuntimeUnavailable: pass
  else: raise AssertionError('missing setup accepted')
assert not any(x in sys.modules for x in ('torch','transformers','mlx_lm','huggingface_hub'))
'''
        proc = subprocess.run([sys.executable, '-c', script], cwd=config.RUNTIME_HOME.parent,
                              capture_output=True, text=True, timeout=5)
        self.assertEqual(proc.returncode, 0, proc.stderr)

    def test_offline_guard_overrides_flags_and_denies_network(self):
        script = '''
import os,socket
os.environ['HF_HUB_OFFLINE']='0'
from research_runtime.adapters import enforce_offline
from research_runtime.protocol import RuntimeUnavailable
enforce_offline()
assert os.environ['HF_HUB_OFFLINE']=='1'
assert os.environ['TRANSFORMERS_OFFLINE']=='1'
for action in (lambda: socket.socket(socket.AF_INET), lambda: socket.socket(socket.AF_INET6), lambda: socket.getaddrinfo('huggingface.co',443)):
 try: action()
 except RuntimeUnavailable: pass
 else: raise AssertionError('network allowed')
socket.socket(socket.AF_UNIX).close()
'''
        proc = subprocess.run([sys.executable, '-c', script], cwd=config.RUNTIME_HOME.parent,
                              capture_output=True, text=True, timeout=5)
        self.assertEqual(proc.returncode, 0, proc.stderr)

    def test_query_instruction_and_plain_documents(self):
        text = '∀ n : ℕ, n = n'
        self.assertEqual(adapters.embedding_text(text, False), text)
        self.assertEqual(adapters.embedding_text(text, True),
                         'Instruct: Find relevant Lean 4 math declarations\nQuery:' + text)

    def test_official_yes_no_ids_not_true_false(self):
        self.assertEqual(adapters.yes_no_ids(FakeTokenizer()), (7, 11))
        tokenizer = FakeTokenizer()
        tokenizer.convert_tokens_to_ids = lambda word: 0
        with self.assertRaises(runtime.RuntimeUnavailable):
            adapters.yes_no_ids(tokenizer)

    def test_wrapper_survives_truncation_with_no_extra_special_tokens(self):
        tokenizer = FakeTokenizer()
        # Independent literal fixture from Qwen's official model card.
        prefix = ('<|im_start|>system\nJudge whether the Document meets the requirements based on '
                  'the Query and the Instruct provided. Note that the answer can only be "yes" '
                  'or "no".<|im_end|>\n<|im_start|>user\n')
        suffix = '<|im_end|>\n<|im_start|>assistant\n<think>\n\n</think>\n\n'
        budget = 400
        result = adapters.reranker_inputs(tokenizer, 'question', ['x' * 1000, 'short'], budget)
        for ids, doc in zip(result['input_ids'], ['x' * 1000, 'short']):
            body = '<Instruct>: Find relevant Lean 4 math declarations\n<Query>: question\n<Document>: ' + doc
            room = budget-len(prefix.encode())-len(suffix.encode())
            self.assertEqual(ids, list(prefix.encode()) + list(body.encode())[:room] + list(suffix.encode()))
            self.assertLessEqual(len(ids), budget)
        self.assertIs(tokenizer.kwargs['add_special_tokens'], False)
        self.assertIs(tokenizer.kwargs['return_attention_mask'], False)

    def test_real_tokenizer_matches_official_recipe_when_installed(self):
        state = config.installation_status(config.DEFAULT_CACHE_DIR)
        if not state['ready']:
            self.skipTest('explicit model setup not installed')
        try:
            from transformers import AutoTokenizer
        except ImportError:
            self.skipTest('dedicated runtime Python not selected')
        tokenizer = AutoTokenizer.from_pretrained(state['models']['reranker']['path'],
                                                  local_files_only=True, trust_remote_code=False,
                                                  padding_side='left')
        pairs = ['<Instruct>: Find relevant Lean 4 math declarations\n<Query>: ℕ reflexivity\n<Document>: ' + d
                 for d in ['theorem refl (n : ℕ) : n = n := rfl', 'lemma x ' * 1000]]
        prefix = tokenizer.encode(adapters.RERANK_PREFIX, add_special_tokens=False)
        suffix = tokenizer.encode(adapters.RERANK_SUFFIX, add_special_tokens=False)
        official = tokenizer(pairs, padding=False, truncation='longest_first', return_attention_mask=False,
                             max_length=512-len(prefix)-len(suffix))
        official['input_ids'] = [prefix + ids + suffix for ids in official['input_ids']]
        official = tokenizer.pad(official, padding=True, return_tensors='pt', max_length=512)
        actual = adapters.reranker_inputs(tokenizer, 'ℕ reflexivity',
                    ['theorem refl (n : ℕ) : n = n := rfl', 'lemma x ' * 1000], 512)
        self.assertEqual(actual['input_ids'].tolist(), official['input_ids'].tolist())
        self.assertEqual(actual['attention_mask'].tolist(), official['attention_mask'].tolist())
        self.assertEqual(adapters.yes_no_ids(tokenizer),
                         (tokenizer.encode('no')[0], tokenizer.encode('yes')[0]))

    def test_bounds_and_deadlines_before_worker_start(self):
        client = runtime.RuntimeClient(Path('/nonexistent/test-cache'))
        with patch.object(client, '_request', side_effect=AssertionError('worker started')):
            for deadline in (time.monotonic()-1,):
                with self.assertRaises(runtime.RuntimeDeadline):
                    client.embed(['x'], deadline=deadline)
            for deadline in (float('inf'), float('nan'), True, time.monotonic()+700):
                with self.assertRaises(ValueError):
                    client.embed(['x'], deadline=deadline)
            for texts in (['x'] * 65, ['x' * 32769], [None]):
                with self.assertRaises(ValueError):
                    client.embed(texts, deadline=time.monotonic()+1)
            with self.assertRaises(ValueError):
                client.generate('x', max_tokens=2049, deadline=time.monotonic()+1)
            self.assertEqual(client.embed([], deadline=time.monotonic()+1), [])

    def test_fragmented_frame_and_oversize_header(self):
        wire = protocol.frame({'op': 'embed', 'texts': ['∀']})
        buffer = bytearray()
        for b in wire[:-1]:
            buffer.append(b)
            self.assertIsNone(protocol.pop_frame(buffer))
        buffer.append(wire[-1])
        self.assertEqual(protocol.pop_frame(buffer)['texts'], ['∀'])
        with self.assertRaises(ValueError):
            protocol.pop_frame(bytearray(struct.pack('!I', config.MAX_FRAME+1)))

    def test_revision_fingerprints_change_with_pins(self):
        before = config.fingerprints()
        with patch.dict(config.MODELS, {'embedding': {'repo': 'same', 'revision': 'changed'}}):
            after = config.fingerprints()
        self.assertNotEqual(before['runtime'], after['runtime'])
        self.assertNotEqual(before['models']['embedding'], after['models']['embedding'])
        self.assertEqual(before['models']['reranker'], after['models']['reranker'])

    def test_runtime_python_and_standard_cache_contract(self):
        root = Path(__file__).resolve().parents[2]
        self.assertEqual(runtime.runtime_python(root), config.PYTHON)
        self.assertEqual(config.DEFAULT_CACHE_DIR, root/'formal/.lake/hgt-research/discovery-1')
        state = runtime.RuntimeClient(config.DEFAULT_CACHE_DIR).status()
        self.assertEqual(state['available'], state['ready'])
        for role in ('embedding', 'reranker', 'generation'):
            self.assertIn(config.MODELS[role]['revision'], state[role+'_model_version'])

    def test_malformed_manifest_reports_unavailable_without_model_import(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'runtime').mkdir()
            for value in ([], {'models': []}, {'models': {'embedding': []}},
                          {'models': {'embedding': {'files': []}}}):
                (root/'runtime/installed.json').write_text(json.dumps(value))
                self.assertFalse(runtime.RuntimeClient(root).status()['available'])


class SetupTests(unittest.TestCase):
    def test_setup_pins_revisions_and_checks_upstream_hashes(self):
        files = {'config.json': b'{}', 'tokenizer.json': b'{}', 'model.safetensors': b'weights'}
        calls = []
        def download(**kwargs):
            calls.append(kwargs)
            folder = Path(kwargs['local_dir'])
            folder.mkdir(parents=True, exist_ok=True)
            for name, data in files.items():
                (folder/name).write_bytes(data)
        def model_info(repo, revision, files_metadata):
            siblings = [SimpleNamespace(rfilename=name, size=len(data),
                         lfs=SimpleNamespace(sha256=hashlib.sha256(data).hexdigest()), blob_id=None)
                        for name, data in files.items()]
            return SimpleNamespace(sha=revision, siblings=siblings)
        hub = SimpleNamespace(snapshot_download=download,
                              HfApi=lambda: SimpleNamespace(model_info=model_info))
        with tempfile.TemporaryDirectory() as directory, patch.dict(sys.modules, {
                'huggingface_hub': hub, 'huggingface_hub.utils': SimpleNamespace(disable_progress_bars=lambda: None)}):
            root = Path(directory)
            with contextlib.redirect_stdout(__import__('io').StringIO()):
                manifest = setup.download_models(root)
            self.assertEqual([c['revision'] for c in calls], [m['revision'] for m in config.MODELS.values()])
            self.assertTrue(all(c['max_workers'] == 2 for c in calls))
            self.assertTrue(setup.verify(root)['verified'])
            damaged = root/'runtime/models/embedding'/config.MODELS['embedding']['revision']/'model.safetensors'
            damaged.write_bytes(b'WEIGHTS')  # same-size corruption defeats cheap size checks
            with self.assertRaisesRegex(RuntimeError, 'hash mismatch'):
                setup.verify(root)
            # Upstream hash disagreement must never publish a new manifest.
            files['model.safetensors'] = b'altered'
            original_info = model_info
            def wrong_info(*args, **kwargs):
                info = original_info(*args, **kwargs)
                info.siblings[-1].lfs.sha256 = '0'*64
                return info
            hub.HfApi = lambda: SimpleNamespace(model_info=wrong_info)
            before = (root/'runtime/installed.json').read_bytes()
            with contextlib.redirect_stdout(__import__('io').StringIO()), self.assertRaisesRegex(RuntimeError, 'upstream content hash'):
                setup.download_models(root)
            self.assertEqual((root/'runtime/installed.json').read_bytes(), before)


class AdapterPolicyTests(unittest.TestCase):
    def test_mlx_failure_falls_back_and_does_not_retry_mlx_next_call(self):
        models = adapters.LocalModels(Path('/unused'))
        def search(request, role):
            models.devices[role] = 'cpu'
            models.loaded[role] = ('model', 'tokenizer')
            return [[1.0]]
        with patch.object(models, '_mlx_embed', side_effect=ImportError('unavailable')) as mlx, patch.object(
                models, '_search', side_effect=search):
            for _ in range(2):
                self.assertEqual(models.run({'op': 'embed', 'deadline': time.monotonic()+2}), [[1.0]])
        mlx.assert_called_once()
        self.assertIn('MLX failure', models.status()['embedding']['fallback_reason'])
        self.assertEqual(models.status()['embedding']['backend'], 'torch')

    def test_mlx_deadline_does_not_start_fallback(self):
        models = adapters.LocalModels(Path('/unused'))
        with patch.object(models, '_mlx_embed', side_effect=runtime.RuntimeDeadline('expired')), patch.object(
                models, '_search') as fallback:
            with self.assertRaises(runtime.RuntimeDeadline):
                models.run({'op': 'embed', 'deadline': time.monotonic()+1})
        fallback.assert_not_called()

    def test_mlx_receives_official_query_instruction(self):
        from unittest.mock import MagicMock
        model = MagicMock()
        models = adapters.LocalModels(Path('/unused'))
        models.loaded['embedding'] = model
        models.devices['embedding'] = 'metal'
        deadline = time.monotonic()+2
        models.run({'op': 'embed', 'texts': ['n = n'], 'query': True, 'deadline': deadline})
        model.embed.assert_called_once_with([adapters.embedding_text('n = n', True)], deadline=deadline)
        self.assertEqual(models.status()['embedding']['backend'], 'mlx')

    def test_local_only_loads_select_explicit_mps_float32(self):
        from unittest.mock import MagicMock
        torch = MagicMock()
        torch.backends.mps.is_available.return_value = True
        factory = MagicMock()
        tokenizer = MagicMock()
        transformer = SimpleNamespace(AutoModel=factory, AutoModelForCausalLM=factory, AutoTokenizer=tokenizer)
        models = adapters.LocalModels(Path('/unused'))
        with patch.dict(sys.modules, {'torch': torch, 'transformers': transformer}), patch.object(
                models, '_path', return_value='/local/snapshot'):
            models._torch_model('embedding')
        kwargs = factory.from_pretrained.call_args.kwargs
        self.assertTrue(kwargs['local_files_only'])
        self.assertFalse(kwargs['trust_remote_code'])
        self.assertIs(kwargs['dtype'], torch.float32)
        factory.from_pretrained.return_value.eval.return_value.to.assert_called_once_with('mps')
        self.assertEqual(tokenizer.from_pretrained.call_args.kwargs['padding_side'], 'right')

    def test_nonfinite_mps_retries_once_on_cpu_and_reports_reason(self):
        from unittest.mock import MagicMock
        models = adapters.LocalModels(Path('/unused'))
        models.devices['embedding'] = 'mps'
        with patch.dict(sys.modules, {'torch': MagicMock()}), patch.object(models, '_search',
                side_effect=[RuntimeError('non-finite inference output'), [[1.0]]]) as search, patch.object(
                models, '_torch_model') as load:
            result = models.run({'op': 'embed', 'deadline': time.monotonic()+2})
        self.assertEqual(result, [[1.0]])
        self.assertEqual(search.call_count, 2)
        load.assert_called_once_with('embedding', cpu=True)
        self.assertIn('non-finite output', models.fallbacks['embedding'])

    def test_mps_batches_embeddings_and_pools_last_nonpad(self):
        try:
            import torch
        except ImportError:
            self.skipTest('dedicated runtime Python not selected')
        batches = []
        class Inputs(dict):
            def to(self, device):
                return self
        def tokenizer(texts, **kwargs):
            batches.append(texts)
            return Inputs(attention_mask=torch.tensor([[1, 0, 0], [1, 1, 0], [1, 1, 1]]))
        def model(**kwargs):
            # Distinct padding vectors expose pooling the last position by mistake.
            return SimpleNamespace(last_hidden_state=torch.tensor([
                [[1., 0., 0.], [0., 9., 0.], [0., 0., 9.]],
                [[0., 9., 0.], [0., 1., 0.], [0., 0., 9.]],
                [[0., 9., 0.], [0., 0., 9.], [0., 0., 1.]]]))
        models = adapters.LocalModels(Path('/unused'))
        models.devices['embedding'] = 'mps'
        with patch.object(models, '_torch_model', return_value=(model, tokenizer)):
            result = models._search({'texts': ['short', 'a much longer text', 'middle'],
                                     'deadline': time.monotonic()+2}, 'embedding')
        self.assertEqual(list(map(len, batches)), [3])
        self.assertEqual(result, [[1., 0., 0.], [0., 1., 0.], [0., 0., 1.]])


class MLXEmbeddingTests(unittest.TestCase):
    def setUp(self):
        try:
            import mlx.core as mx
            import numpy as np
        except ImportError:
            self.skipTest('dedicated Apple runtime Python not selected')
        from research_runtime.mlx_embedding import MLXEmbedding
        self.mx, self.np = mx, np
        self.model = MLXEmbedding.__new__(MLXEmbedding)

    def test_right_padding_pooling_sort_order_and_repeated_shapes(self):
        mx, np = self.mx, self.np
        calls = []
        class Tokenizer:
            def __call__(self, texts, **kwargs):
                return {'input_ids': [[ord(c) for c in text] for text in texts]}
            def pad(self, inputs, **kwargs):
                calls.append((inputs['input_ids'], kwargs))
                ids = inputs['input_ids']
                length = ((max(map(len, ids))+31)//32)*32
                return {'input_ids': np.array([x+[0]*(length-len(x)) for x in ids]),
                        'attention_mask': np.array([[1]*len(x)+[0]*(length-len(x)) for x in ids])}
        self.model.tokenizer = Tokenizer()
        # Padding gives a different vector; gathering the wrong position fails.
        self.model.forward = mx.compile(lambda x: mx.stack([x.astype(mx.float32),
                                                           mx.ones(x.shape)], axis=-1), shapeless=False)
        for texts in (['aaaaaz', 'b', 'ccc', 'ddddx', 'qq'], ['z'*40, 'y']):
            actual = np.array(self.model.embed(texts, deadline=time.monotonic()+5))
            expected = np.array([[ord(text[-1]), 1] for text in texts], dtype=float)
            expected /= np.linalg.norm(expected, axis=1, keepdims=True)
            np.testing.assert_allclose(actual, expected, atol=1e-7)
        self.assertEqual([len(ids) for ids, _ in calls], [4, 1, 2])
        self.assertTrue(all(kwargs['pad_to_multiple_of'] == 32 for _, kwargs in calls))
        with self.assertRaises(runtime.RuntimeDeadline):
            self.model.embed(['abc'], deadline=time.monotonic()-1)
        self.assertEqual(len(calls), 3)

    def test_nonfinite_and_zero_vectors_are_rejected(self):
        import numpy as np
        self.model.tokenizer = SimpleNamespace()
        class Tokenizer:
            def __call__(self, *args, **kwargs):
                return {'input_ids': [[1]]}
            def pad(self, *args, **kwargs):
                return {'input_ids': np.array([[1]]), 'attention_mask': np.array([[1]])}
        self.model.tokenizer = Tokenizer()
        for value in (0., float('nan')):
            self.model.forward = lambda ids: self.mx.full((1, 1, 2), value)
            with self.assertRaisesRegex(RuntimeError, 'zero-norm'):
                self.model.embed(['x'], deadline=time.monotonic()+2)


class WorkerTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.server = multiprocessing.get_context('spawn').Process(target=serve_fake, args=(str(self.root),))
        self.server.start()
        self.addCleanup(self.stop_server)
        self.client = runtime.RuntimeClient(self.root)
        self.addCleanup(self.client.close)
        self.wait_for(lambda: self.client.status()['running'])

    def stop_server(self):
        if self.server.is_alive():
            self.server.terminate()
        self.server.join(3)
        if self.server.is_alive():
            self.server.kill()
            self.server.join()
        import shutil
        shutil.rmtree(worker.socket_directory(self.root), ignore_errors=True)

    def wait_for(self, predicate, seconds=4):
        end = time.monotonic()+seconds
        while time.monotonic() < end:
            if predicate():
                return
            time.sleep(0.01)
        self.fail('condition not reached')

    def events(self):
        path = self.root / 'events'
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def test_concurrent_clients_serialize_inference(self):
        with concurrent.futures.ThreadPoolExecutor(8) as pool:
            futures = [pool.submit(runtime.RuntimeClient(self.root).embed, [str(i)], deadline=time.monotonic()+6)
                       for i in range(8)]
            self.assertEqual([f.result() for f in futures], [[[1.0]]] * 8)
        events = self.events()
        self.assertEqual([e[0] for e in events], ['start', 'end']*8)
        self.assertEqual(len({e[2] for e in events}), 1)
        state = self.client.status()
        self.assertEqual(state['models']['embedding']['revision'], config.MODELS['embedding']['revision'])
        self.assertIn('runtime', state['fingerprints'])

    def test_client_with_process_local_clock_uses_worker_relative_budget(self):
        with patch('time.monotonic', return_value=10.0):
            self.assertEqual(self.client.embed(['ok'], deadline=12.0), [[2.0]])

    def test_deadline_returns_promptly_and_reaps_blocked_child(self):
        start = time.monotonic()
        with self.assertRaises(runtime.RuntimeDeadline):
            self.client.embed(['slow-deadline'], deadline=start+0.6)
        self.assertLess(time.monotonic()-start, 1.0)
        old = self.events()[0][2]
        self.wait_for(lambda: self.client.status().get('child_pid') is None)
        with self.assertRaises(ProcessLookupError):
            os.kill(old, 0)
        self.assertEqual(self.client.embed(['ok'], deadline=time.monotonic()+3), [[2.0]])

    def test_close_cancels_only_own_request_and_preserves_other_client(self):
        other = runtime.RuntimeClient(self.root)
        with concurrent.futures.ThreadPoolExecutor(2) as pool:
            first = pool.submit(self.client.embed, ['slow-cancel'], deadline=time.monotonic()+10)
            self.wait_for(lambda: bool(self.events()))
            second = pool.submit(other.embed, ['other'], deadline=time.monotonic()+4)
            start = time.monotonic()
            self.client.close()
            with self.assertRaises(runtime.RuntimeUnavailable):
                first.result(timeout=1)
            self.assertLess(time.monotonic()-start, 0.5)
            self.assertEqual(second.result(timeout=3), [[5.0]])
        self.assertEqual(other.status()['pid'], self.server.pid)

    def test_interactive_preempts_enrichment_without_overlap(self):
        with concurrent.futures.ThreadPoolExecutor(2) as pool:
            low = pool.submit(self.client.generate, 'slow-enrichment', priority='enrichment',
                              deadline=time.monotonic()+10)
            self.wait_for(lambda: bool(self.events()))
            old = self.events()[0][2]
            result = self.client.embed(['search'], deadline=time.monotonic()+3)
            self.assertEqual(result, [[6.0]])
            with self.assertRaisesRegex(runtime.RuntimeUnavailable, 'preempted'):
                low.result(timeout=1)
            with self.assertRaises(ProcessLookupError):
                os.kill(old, 0)

    def test_expired_queued_request_never_reaches_model(self):
        with concurrent.futures.ThreadPoolExecutor(2) as pool:
            first = pool.submit(self.client.embed, ['slow-active'], deadline=time.monotonic()+0.8)
            self.wait_for(lambda: bool(self.events()))
            with self.assertRaises(runtime.RuntimeDeadline):
                self.client.embed(['expired'], deadline=time.monotonic()+0.1)
            with self.assertRaises(runtime.RuntimeDeadline):
                first.result(timeout=2)
        self.assertNotIn('expired', [e[1] for e in self.events()])

    def test_crash_restarts_only_owned_child(self):
        with self.assertRaises(runtime.RuntimeUnavailable):
            self.client.embed(['crash'], deadline=time.monotonic()+3)
        self.assertEqual(self.client.embed(['alive'], deadline=time.monotonic()+3), [[5.0]])
        self.assertEqual(self.client.status()['pid'], self.server.pid)

    def test_status_responsive_during_inference(self):
        with concurrent.futures.ThreadPoolExecutor(1) as pool:
            job = pool.submit(self.client.embed, ['slow-status'], deadline=time.monotonic()+0.8)
            self.wait_for(lambda: bool(self.events()))
            start = time.monotonic()
            state = self.client.status()
            self.assertLess(time.monotonic()-start, 0.3)
            self.assertEqual(state['active'], 'embed')
            with self.assertRaises(runtime.RuntimeDeadline):
                job.result(timeout=2)

    def test_partial_child_frame_cannot_block_deadline_or_status(self):
        with concurrent.futures.ThreadPoolExecutor(1) as pool:
            job = pool.submit(self.client.embed, ['partial-frame'], deadline=time.monotonic()+0.7)
            self.wait_for(lambda: bool(self.events()))
            start = time.monotonic()
            self.assertTrue(self.client.status()['running'])
            self.assertLess(time.monotonic()-start, 0.3)
            with self.assertRaises(runtime.RuntimeDeadline):
                job.result(timeout=1)
        self.assertEqual(self.client.embed(['after-partial'], deadline=time.monotonic()+3), [[13.0]])

    def test_supervisor_shutdown_reaps_child(self):
        with concurrent.futures.ThreadPoolExecutor(1) as pool:
            job = pool.submit(self.client.embed, ['slow-shutdown'], deadline=time.monotonic()+10)
            self.wait_for(lambda: bool(self.events()))
            child = self.events()[0][2]
            self.server.terminate()
            self.server.join(2)
            with self.assertRaises(runtime.RuntimeUnavailable):
                job.result(timeout=2)
            with self.assertRaises(ProcessLookupError):
                os.kill(child, 0)

    def test_second_supervisor_does_not_replace_socket(self):
        duplicate = multiprocessing.get_context('spawn').Process(target=serve_fake, args=(str(self.root),))
        duplicate.start()
        duplicate.join(2)
        self.assertEqual(duplicate.exitcode, 0)
        self.assertEqual(self.client.status()['pid'], self.server.pid)

    def test_bounded_admission_and_malformed_frame_recovery(self):
        peers = []
        try:
            for _ in range(config.MAX_PENDING):
                sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
                sock.connect(str(self.client.directory/'worker.sock'))
                peers.append(sock)
            time.sleep(0.1)
            with self.assertRaises(runtime.RuntimeUnavailable):
                self.client.embed(['overflow'], deadline=time.monotonic()+1)
        finally:
            for sock in peers:
                sock.close()
        self.wait_for(lambda: self.client.status()['running'])
        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as bad:
            bad.connect(str(self.client.directory/'worker.sock'))
            bad.sendall(struct.pack('!I', config.MAX_FRAME+1))
            bad.settimeout(1)
            self.assertIn(b'invalid', bad.recv(1024))
        self.assertEqual(self.client.embed(['recovered'], deadline=time.monotonic()+3), [[9.0]])


if __name__ == '__main__':
    unittest.main()
