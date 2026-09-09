"""Finite transfer/import of an authorized method-generation and vector pipeline."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import os
import shlex
import signal
import time

from lean_research_batch import locks, import_results as import_vectors
from lean_research_batch_sync import owned_run
from lean_research_method_batch import import_results as import_methods
from research_batch.format import atomic_json, sha_file
from research_batch.methods import load_manifest
from research_runtime.config import DEFAULT_CACHE_DIR


def sync(directory, *, cache, root, interval=120):
    connection = json.loads((directory / 'connection.json').read_text())
    bundle, output = directory / 'bundle', directory / 'results'
    vectors = directory / 'vectors'
    output.mkdir(exist_ok=True)
    vectors.mkdir(exist_ok=True)
    manifest = load_manifest(bundle)
    source_sha = sha_file(bundle / 'manifest.json')
    ssh = ['ssh','-o','BatchMode=yes','-o','StrictHostKeyChecking=yes','-o','ConnectTimeout=15',
           '-o','ServerAliveInterval=30','-o','ServerAliveCountMax=3','-p',str(connection['port']),
           '-i',connection['identity_file']]
    address = connection['user'] + '@' + connection['host']
    def download(remote, local, *, vector=False):
        flags = ['--exclude=*.tmp','--exclude=runner.lock','--exclude=*.log']
        if vector:
            flags += ['--exclude=model','--exclude=research_batch','--exclude=texts.sqlite3']
        return owned_run(['rsync','-a','--partial',*flags,'-e',shlex.join(ssh),
                          address+':'+shlex.quote(remote+'/'),str(local)+'/'])
    probe = ('import json,sys; from pathlib import Path; p=Path(sys.argv[1]); '
             'pid=int((p/"pipeline.pid").read_text()); c=Path(f"/proc/{pid}/cmdline"); '
             'running=c.exists() and b"method-pipeline.sh" in c.read_bytes(); '
             'r=p/"pipeline.json"; print(json.dumps({"running":running,"pipeline":'
             'json.loads(r.read_text()) if r.exists() else {}}))')
    state = dict(pid=os.getpid(), running=True, completed=False, phase='starting', manifest_sha256=source_sha)
    target = directory / 'sync-status.json'
    with locks([directory / 'sync.lock'], seconds=0):
        failures = 0
        try:
            while True:
                try:
                    state.update(phase='method_download', updated=time.time())
                    atomic_json(target,state)
                    download(connection['remote_directory']+'/results',output)
                    state.update(phase='method_import', updated=time.time())
                    atomic_json(target,state)
                    report = import_methods(cache,bundle,output,root=root,budget_seconds=90,lock_seconds=150)
                    state['methods'] = report
                    gpu = json.loads((output/'run.json').read_text()) if (output/'run.json').exists() else {}
                    methods_complete = (gpu.get('complete') and gpu.get('manifest_sha256') == source_sha
                                        and not report['partial'] and report['checked_shards'] == len(manifest['shards']))
                    state['generation'] = gpu
                    if methods_complete:
                        state.update(phase='vector_download',updated=time.time())
                        atomic_json(target,state)
                        download(connection['remote_vector_directory'],vectors,vector=True)
                        if (vectors/'manifest.json').exists() and (vectors/'results/audit.json').exists():
                            vm = json.loads((vectors/'manifest.json').read_text())
                            if vm.get('method_manifest_sha256') != source_sha:
                                raise ValueError('description vectors belong to a different method job')
                            state.update(phase='vector_import',updated=time.time())
                            atomic_json(target,state)
                            vr = import_vectors(cache,vectors,vectors/'results',budget_seconds=120,lock_seconds=150)
                            state['vectors'] = vr
                            run = json.loads((vectors/'results/run.json').read_text()) if (vectors/'results/run.json').exists() else {}
                            if run.get('complete') and run.get('manifest_sha256') == sha_file(vectors/'manifest.json') and not vr['partial']:
                                state.update(completed=True,phase='complete',error=None)
                                return state
                    remote = json.loads(owned_run(ssh+[address,'python -c '+shlex.quote(probe)+' '+shlex.quote(connection['remote_directory'])],timeout=30))
                    state['remote'] = remote
                    if not remote['running'] and remote['pipeline'].get('status') != 'complete':
                        raise ValueError('GPU method pipeline stopped before completion; inspect pipeline.log')
                    failures = 0
                    state.update(phase='waiting',error=None)
                except TimeoutError as exc:
                    state.update(phase='waiting_for_maintenance',error=str(exc))
                except (OSError,RuntimeError) as exc:
                    failures += 1
                    state.update(phase='retrying',error=str(exc))
                    if failures >= 5:
                        raise
                state['updated'] = time.time()
                atomic_json(target,state)
                time.sleep(interval)
        except BaseException as exc:
            state.update(phase='stopped' if isinstance(exc,KeyboardInterrupt) else 'failed',error=str(exc))
            raise
        finally:
            state.update(running=False,updated=time.time())
            atomic_json(target,state)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, required=True)
    parser.add_argument('--cache-dir', type=Path, default=DEFAULT_CACHE_DIR)
    parser.add_argument('--root', type=Path, required=True)
    args = parser.parse_args()
    signal.signal(signal.SIGTERM,lambda *_: (_ for _ in ()).throw(KeyboardInterrupt()))
    print(json.dumps(sync(args.directory.resolve(),cache=args.cache_dir.resolve(),root=args.root.resolve())))
