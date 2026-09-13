#!/usr/bin/env python3
"""Finite background transfer/import for one explicitly authorized GPU job.

Uses connection.json created for that job. No model inference or Lean process.
Exits after all completed output shards are verified and imported, or on failure.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shlex
import signal
import subprocess
import sys
import time

from lean_research_batch import import_results, locks
from research_batch.format import atomic_json, load_manifest, sha_file
from research_runtime.config import DEFAULT_CACHE_DIR
from research_runtime.processes import terminate_owned, cancellation_signals


@cancellation_signals()
def owned_run(argv, timeout=900):
    """Cancellation and timeouts reap only this command and its SSH children."""
    child = subprocess.Popen(argv, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             text=True, start_new_session=True)
    try:
        output, _ = child.communicate(timeout=timeout)
        if child.returncode:
            raise RuntimeError(f'{argv[0]} failed ({child.returncode}): {output[-2000:]}')
        return output
    finally:
        terminate_owned(child)
        child.stdout.close()


def sync(directory, *, cache=DEFAULT_CACHE_DIR, interval=120, max_failures=5):
    directory = directory.resolve()
    connection = json.loads((directory / 'connection.json').read_text())
    bundle, output = directory / 'bundle', directory / 'results'
    output.mkdir(exist_ok=True)
    manifest = load_manifest(bundle)
    manifest_sha = sha_file(bundle / 'manifest.json')
    remote = connection['remote_directory']
    ssh = ['ssh', '-o', 'BatchMode=yes', '-o', 'StrictHostKeyChecking=yes',
           '-o', 'ConnectTimeout=15', '-o', 'ServerAliveInterval=30',
           '-o', 'ServerAliveCountMax=3', '-p', str(int(connection['port'])),
           '-i', connection['identity_file']]
    address = connection['user'] + '@' + connection['host']
    copy = ['rsync', '-a', '--partial', '--stats', '--exclude=*.tmp', '--exclude=runner.lock',
            '-e', shlex.join(ssh), address + ':' + shlex.quote(remote + '/results/'), str(output) + '/']
    # Check the recorded process command, not just a possibly recycled PID.
    probe = ('import json,sys; from pathlib import Path; p=Path(sys.argv[1]); '
             'pid=int((p/"embedding.pid").read_text()); c=Path(f"/proc/{pid}/cmdline"); '
             'running=c.exists() and b"research_batch.runner" in c.read_bytes(); '
             'r=p/"results/run.json"; '
             'print(json.dumps({"pid":pid,"running":running,"run":'
             'json.loads(r.read_text()) if r.exists() else {}}))')
    status_command = ssh + [address, 'python -c ' + shlex.quote(probe) + ' ' + shlex.quote(remote)]
    state = dict(pid=os.getpid(), running=True, phase='starting', manifest_sha256=manifest_sha,
                 completed=False, total_published=0, failures=0)
    target = directory / 'sync-status.json'
    with locks([directory / 'sync.lock'], seconds=0):
        try:
            previous = json.loads(target.read_text())
            if previous.get('manifest_sha256') == manifest_sha:
                state['total_published'] = previous.get('total_published', 0)
        except (OSError, ValueError):
            pass
        try:
            while True:
                try:
                    state.update(phase='downloading', updated=time.time())
                    atomic_json(target, state)
                    owned_run(copy)
                    state.update(phase='importing', updated=time.time())
                    atomic_json(target, state)
                    report = import_results(cache, bundle, output, budget_seconds=300, lock_seconds=150)
                    state['total_published'] += report['published']
                    state['import'] = report
                    gpu = json.loads((output / 'run.json').read_text()) if (output / 'run.json').exists() else {}
                    if gpu.get('complete') and not report['partial']:
                        if (gpu.get('manifest_sha256') != manifest_sha or
                                report['checked_shards'] != len(manifest['shards'])):
                            raise ValueError('GPU completion does not match the verified snapshot')
                        state.update(completed=True, phase='complete', failures=0)
                        return state
                    process = json.loads(owned_run(status_command, timeout=30))
                    state['remote_process'] = process
                    if not process['running'] and not gpu.get('complete'):
                        # Import may take minutes: the worker can finish after
                        # rsync's snapshot. Fetch its final shards next cycle.
                        finished = process.get('run', {})
                        if not (finished.get('complete') and finished.get('manifest_sha256') == manifest_sha
                                and finished.get('completed_shards') == len(manifest['shards'])):
                            raise ValueError('GPU worker stopped before completing; inspect remote embedding.log')
                    state.update(phase='waiting', failures=0, error=None, updated=time.time())
                except TimeoutError as exc:
                    state.update(phase='waiting_for_maintenance', error=str(exc), updated=time.time())
                except (OSError, RuntimeError, subprocess.SubprocessError) as exc:
                    state['failures'] += 1
                    state.update(phase='retrying', error=str(exc), updated=time.time())
                    if state['failures'] >= max_failures:
                        raise
                atomic_json(target, state)
                time.sleep(interval)
        except BaseException as exc:
            state.update(phase='stopped' if isinstance(exc, KeyboardInterrupt) else 'failed', error=str(exc))
            raise
        finally:
            state.update(running=False, updated=time.time())
            atomic_json(target, state)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--directory', type=Path, required=True)
    parser.add_argument('--cache-dir', type=Path, default=DEFAULT_CACHE_DIR)
    parser.add_argument('--interval', type=float, default=120)
    args = parser.parse_args()
    if args.interval < 10:
        parser.error('interval must be at least ten seconds')
    signal.signal(signal.SIGTERM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt()))
    print(json.dumps(sync(args.directory, cache=args.cache_dir, interval=args.interval)), flush=True)


if __name__ == '__main__':
    main()
