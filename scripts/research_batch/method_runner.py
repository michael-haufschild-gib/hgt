"""Pinned offline CUDA generation, resumable by bounded source/result shards."""
from __future__ import annotations

import argparse
import fcntl
import importlib.metadata
import json
import os
import sys
from pathlib import Path
import time

from research_batch.format import atomic_json, checked_file, sha_file, sha_text
from research_batch.methods import (PRODUCER, VLLM_VERSION, checked_output, load_manifest,
                                    method_payload, method_prompt, proof_parts, read_rows,
                                    validated_payload, write_rows)


class Generator:
    def __init__(self, bundle, *, max_seqs=256):
        manifest = load_manifest(bundle)
        runtime = checked_file(bundle, manifest['runtime_packages'])
        for line in runtime.read_text().splitlines():
            if not line or line.startswith('#'):
                continue
            name, expected = line.split('==',1)
            if importlib.metadata.version(name) != expected:
                raise ValueError('method runtime version changed: ' + name)
        for key in ('HF_HUB_OFFLINE', 'TRANSFORMERS_OFFLINE', 'HF_HUB_DISABLE_TELEMETRY', 'VLLM_NO_USAGE_STATS'):
            os.environ[key] = '1'
        os.environ['DO_NOT_TRACK'] = '1'
        # vLLM invokes installed build helpers such as ninja by executable name.
        os.environ['PATH'] = str(Path(sys.executable).parent) + os.pathsep + os.environ.get('PATH','')
        compiler = importlib.metadata.distribution('nvidia-cuda-nvcc')
        nvcc = next(Path(compiler.locate_file(f)) for f in compiler.files if str(f).endswith('bin/nvcc'))
        # The container toolkit is 12.8 and cannot compile B300 (sm_103a).
        # Use the pinned compiler/headers already installed in this environment.
        os.environ['CUDA_HOME'] = str(nvcc.parent.parent)
        os.environ['CUDA_PATH'] = str(nvcc.parent.parent)
        os.environ['PATH'] = str(nvcc.parent) + os.pathsep + os.environ['PATH']
        cuda = nvcc.parent.parent
        # NVIDIA wheels ship lib/ and a versioned runtime; FlashInfer's build
        # expects the toolkit's lib64/ and unversioned linker name.
        if not (cuda / 'lib64').exists():
            (cuda / 'lib64').symlink_to('lib', target_is_directory=True)
        if not (cuda / 'lib/libcudart.so').exists():
            (cuda / 'lib/libcudart.so').symlink_to('libcudart.so.13')
        os.environ.setdefault('VLLM_WORKER_MULTIPROC_METHOD', 'spawn')
        import torch
        from vllm import LLM, SamplingParams
        if importlib.metadata.version('vllm') != VLLM_VERSION:
            raise ValueError('vLLM version differs from reviewed runtime')
        if not torch.cuda.is_available() or torch.cuda.device_count() != 1:
            raise ValueError('one CUDA GPU required')
        self.llm = LLM(model=str(Path(bundle) / 'model'), dtype='bfloat16',
                       trust_remote_code=False, max_model_len=16384, max_num_seqs=max_seqs,
                       max_num_batched_tokens=32768, gpu_memory_utilization=.70,
                       enable_prefix_caching=True, seed=0)
        self.tokenizer = self.llm.get_tokenizer()
        self.params = SamplingParams(temperature=0, max_tokens=512)
        self.environment = dict(producer=PRODUCER, gpu=torch.cuda.get_device_name(0),
                                torch=torch.__version__, cuda=torch.version.cuda,
                                vllm=VLLM_VERSION, max_seqs=max_seqs, max_output_tokens=512,
                                runtime_sha256=manifest['runtime_packages']['sha256'])

    def generate(self, prompts):
        encoded = [self.tokenizer.apply_chat_template([dict(role='user', content=p)],
                    tokenize=True, add_generation_prompt=True, return_dict=False) for p in prompts]
        accepted = [(i, ids) for i, ids in enumerate(encoded) if len(ids) + 512 <= 16384]
        answers = [dict(response='', finish_reason='input_too_long', input_tokens=len(ids), output_tokens=0)
                   for ids in encoded]
        if accepted:
            outputs = self.llm.generate([dict(prompt_token_ids=ids) for _, ids in accepted], self.params, use_tqdm=False)
            if len(outputs) != len(accepted):
                raise ValueError('generation omitted requests')
            for (i, _), output in zip(accepted, outputs):
                value = output.outputs[0]
                answers[i] = dict(response=value.text, finish_reason=value.finish_reason,
                                  input_tokens=len(encoded[i]), output_tokens=len(value.token_ids))
        return answers


def generate_shard(generator, sources):
    tasks, mapping = [], []
    results = [dict(id=s['id'], source_hash=s['source_hash'], chunks=[], status='ready') for s in sources]
    for i, source in enumerate(sources):
        parts = list(proof_parts(source['proof']))
        if not parts:
            results[i].update(status='failed', error='proof has no code chunks')
        for part, code in parts:
            mapping.append((i, part))
            tasks.append(method_prompt(source['statement'], code))
    answers = generator.generate(tasks) if tasks else []
    if len(answers) != len(tasks):
        raise ValueError('generation omitted proof chunks')
    retry, retry_ids = [], []
    for i, ((_, part), answer) in enumerate(zip(mapping, answers)):
        try:
            if answer['finish_reason'] != 'stop':
                raise ValueError('generation ended with ' + answer['finish_reason'])
            method_payload(answer['response'], part)
        except ValueError as exc:
            if answer['finish_reason'] != 'input_too_long':
                retry_ids.append(i)
                retry.append(tasks[i] + '\nPrevious attempt failed validation: ' + str(exc)
                             + '. Return a complete JSON object with valid numbered code-line evidence.')
    if retry:
        repaired = generator.generate(retry)
        if len(repaired) != len(retry):
            raise ValueError('retry omitted proof chunks')
        for i, answer in zip(retry_ids, repaired):
            answers[i] = {**answer, 'retried': True}
    for (i, part), answer in zip(mapping, answers):
        results[i]['chunks'].append(dict(chunk_hash=sha_text(part), **answer))
    for source, result in zip(sources, results):
        if result['status'] == 'ready':
            try:
                validated_payload(source, result)
            except ValueError as exc:
                result.update(status='failed', error=str(exc))
    return results


def run(args):
    bundle, output = args.bundle.resolve(), args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    manifest = load_manifest(bundle)
    manifest_sha = sha_file(bundle / 'manifest.json')
    for item in manifest['code']:
        checked_file(bundle / item['directory'], item['file'])
    for item in manifest['model_files']:
        checked_file(bundle / 'model', item)
    with (output / 'runner.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        pending, completed, ready, failed = [], 0, 0, 0
        for entry in manifest['shards']:
            if (output / (entry['name'] + '.done.json')).exists():
                _, results = checked_output(bundle, output, entry)
                completed += 1
                ready += sum(r['status'] == 'ready' for r in results)
                failed += sum(r['status'] == 'failed' for r in results)
            else:
                pending.append(entry)
        generator = Generator(bundle, max_seqs=args.max_seqs) if pending else None
        if generator:
            atomic_json(output / 'environment.json', generator.environment)
        started = time.monotonic()
        new_count = 0
        for entry in pending:
            if args.max_shards and new_count >= args.max_shards:
                break
            sources = read_rows(bundle / 'inputs', entry)
            tick = time.monotonic()
            results = generate_shard(generator, sources)
            data = write_rows(output / ('result-' + entry['name']), results)
            atomic_json(output / (entry['name'] + '.done.json'),
                        dict(manifest_sha256=manifest_sha, input_sha256=entry['sha256'],
                             producer=PRODUCER, results=data, seconds=time.monotonic()-tick))
            completed += 1
            new_count += 1
            ready += sum(r['status'] == 'ready' for r in results)
            failed += sum(r['status'] == 'failed' for r in results)
            progress = dict(complete_shards=completed, total_shards=len(manifest['shards']),
                            ready=ready, failed=failed, seconds=time.monotonic()-started,
                            last_shard_seconds=time.monotonic()-tick, last_shard_count=len(sources))
            atomic_json(output / 'progress.json', progress)
            print(json.dumps(progress), flush=True)
        result = dict(complete=completed == len(manifest['shards']), completed_shards=completed,
                      total_shards=len(manifest['shards']), ready=ready, failed=failed,
                      manifest_sha256=manifest_sha, seconds=time.monotonic()-started)
        atomic_json(output / 'run.json', result)
        return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--max-shards', type=int, default=0)
    parser.add_argument('--max-seqs', type=int, default=256)
    print(json.dumps(run(parser.parse_args())), flush=True)
