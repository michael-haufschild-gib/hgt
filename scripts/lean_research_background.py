"""One resumable, local corpus indexer. No agent, scheduler service or Lean build.

The worker owns each bounded Python maintenance child, stores progress atomically,
and checks a stop token while children run. The shared inference broker gives
interactive searches priority. Source/compiler freshness remains explicit.
"""
from __future__ import annotations

import argparse
import fcntl
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import threading
import time
import uuid

from lean_research_corpus import Corpus, cache_directory


def atomic_json(path: Path, value: dict):
    temporary = path.with_suffix('.%d.tmp' % os.getpid())
    try:
        temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2))
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def status(root: Path) -> dict:
    directory = cache_directory(root)
    try:
        value = json.loads((directory / 'indexer.json').read_text())
    except (OSError, ValueError):
        value = {}
    running = False
    if directory.exists():
        with (directory / 'indexer.lock').open('a') as lock:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                running = True
    return {**value, 'running': running, 'priority': ['RHTower', 'HTGeometry', 'rest'],
            'log': str(directory / 'indexer.log')}


def start(root: Path) -> dict:
    from lean_research_cli import engine_python
    directory = cache_directory(root)
    directory.mkdir(parents=True, exist_ok=True)
    before = status(root)
    if before['running']:
        return {**before, 'already_running': True}
    with (directory / 'indexer.log').open('ab') as log:
        child = subprocess.Popen([engine_python(root), str(Path(__file__).resolve()), 'run', '--root', str(root)],
                                 stdin=subprocess.DEVNULL, stdout=log, stderr=log,
                                 cwd=str(root), start_new_session=True)
    threading.Thread(target=child.wait, daemon=True).start()
    # Only startup acknowledgement; enrichment continues in the single worker.
    deadline = time.monotonic() + 3
    while time.monotonic() < deadline:
        current = status(root)
        if current['running'] and current.get('pid') == child.pid:
            atomic_json(directory / 'progressive.json', {'enabled': True, 'enabled_at': time.time()})
            return current
        if child.poll() is not None:
            return {**current, 'error': 'indexer failed to start; inspect log'}
        time.sleep(.05)
    return {**status(root), 'starting_pid': child.pid}


def stop(root: Path) -> dict:
    current = status(root)
    if current['running'] and current.get('token'):
        atomic_json(cache_directory(root) / 'indexer-stop.json', {'token': current['token']})
        return {**current, 'stop_requested': True}
    return current


def terminate_owned(child):
    if child.poll() is None:
        try:
            os.killpg(child.pid, signal.SIGTERM)
            child.wait(timeout=.5)
        except subprocess.TimeoutExpired:
            os.killpg(child.pid, signal.SIGKILL)
            child.wait()
        except ProcessLookupError:
            child.wait()


def classify_failures(reports):
    errors, deferred = [], []
    seen = set()
    for report in reports:
        for collection in ('failures', 'deferred'):
            for failure in report.get(collection, []):
                key = json.dumps(failure, sort_keys=True)
                if key in seen:
                    continue
                seen.add(key)
                message = failure.get('error', '').lower()
                retryable = (collection == 'deferred' or failure.get('reason') == 'maintenance_busy'
                             or 'deadline' in message or 'preempted' in message)
                (deferred if retryable else errors).append(failure)
    return errors[-5:], deferred[-5:]


def small_shard_count(directory):
    # This is a read probe, including while a bulk importer owns the writer.
    with Corpus(directory, readonly=True) as corpus:
        return corpus.con.execute('SELECT COUNT(*) FROM vector_shards s WHERE count<8192 '
            'AND EXISTS(SELECT 1 FROM vectors WHERE shard=s.id)').fetchone()[0]


def maintenance_contention(tail):
    return any(message in tail for message in (
        'database is locked', 'database table is locked',
        'Another enrichment process owns the resumable queue.'))


def run(root: Path, *, once=False) -> int:
    directory = cache_directory(root)
    directory.mkdir(parents=True, exist_ok=True)
    interrupted = False
    def interrupt(signum, frame):
        nonlocal interrupted
        interrupted = True
    signal.signal(signal.SIGINT, interrupt)
    signal.signal(signal.SIGTERM, interrupt)
    with (directory / 'indexer.lock').open('a') as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return 0
        token = uuid.uuid4().hex
        state = dict(pid=os.getpid(), token=token, started_at=time.time(), phase='starting', cycles=0,
                     model_inference='local_only', lean_compilation='foreground_only')
        def record(**values):
            state.update(values, updated_at=time.time())
            atomic_json(directory / 'indexer.json', state)
        def stopped():
            if interrupted:
                return True
            try:
                return json.loads((directory / 'indexer-stop.json').read_text()).get('token') == token
            except (OSError, ValueError):
                return False
        def phase(name, seconds, flags):
            if stopped():
                return
            record(phase=name)
            started = time.monotonic()
            report_file = directory / 'indexer-phase.log'
            with report_file.open('wb') as output:
                child = subprocess.Popen([sys.executable, str(root / 'scripts/formal_tools.py'), 'search-index',
                                          '--budget-seconds', str(seconds), *flags],
                                         cwd=str(root), stdin=subprocess.DEVNULL, stdout=output,
                                         stderr=output, start_new_session=True)
                deadline = time.monotonic() + seconds + 15
                try:
                    while child.poll() is None and time.monotonic() < deadline and not stopped():
                        time.sleep(.2)
                finally:
                    termination_reason = ('stop_requested' if stopped() else 'phase_deadline') if child.poll() is None else None
                    terminate_owned(child)
            # Keep a bounded tail; never read an arbitrarily large phase log.
            with report_file.open('rb') as output:
                output.seek(max(0, report_file.stat().st_size - 32000))
                tail = output.read().decode(errors='replace')
            reports = []
            for line in tail.splitlines():
                try:
                    value = json.loads(line)
                    if isinstance(value, dict):
                        reports.append(value)
                except ValueError:
                    continue
            for value in reports:
                if 'coverage' in value:
                    state['coverage'] = value['coverage']
            last = reports[-1] if reports else {}
            errors, deferred = classify_failures(reports)
            error = None
            if termination_reason == 'phase_deadline':
                error = f'{name} exceeded its {seconds}-second budget and 15-second shutdown allowance'
            elif child.returncode and termination_reason != 'stop_requested':
                if maintenance_contention(tail):
                    deferred.append(dict(stage=name, error=tail[-1200:], reason='maintenance_busy'))
                else:
                    error = tail[-1200:] or f'{name} exited with code {child.returncode}'
            phases = state.setdefault('phases', {})
            phases[name] = dict(at=time.time(), elapsed_seconds=time.monotonic()-started,
                                exit_code=child.returncode, termination_reason=termination_reason,
                                errors=errors, deferred=deferred, error=error,
                                completed={k: last[k] for k in ('changed', 'vectors', 'methods') if k in last})
            record(last_phase=name, last_exit_code=child.returncode, last_result=last,
                   errors=errors, deferred=deferred, last_error=error)
        record()
        try:
            while not stopped():
                phase('sources', 25, ['--corpus'])
                if stopped():
                    break
                from lean_research_runtime import RuntimeClient
                with RuntimeClient(directory) as client:
                    ready = client.status().get('available', False)
                if ready:
                    phase('embeddings', 90, ['--vectors'])
                    phase('methods', 45, ['--methods'])
                    if not stopped():
                        small = small_shard_count(directory)
                        if small > 256:
                            phase('compaction', 30, ['--compact'])
                else:
                    record(last_error='Local models unavailable; source indexing continues. Run research-setup to enable enrichment.')
                record(cycles=state['cycles'] + 1, phase='idle')
                if once:
                    break
                for _ in range(50 if ready else 300):
                    if stopped():
                        break
                    time.sleep(.1)
        finally:
            record(phase='stopped', stopped_at=time.time())
    return 0


def command(root: Path, action: str) -> int:
    if action == 'run':
        return run(root)
    result = {'start': start, 'status': status, 'stop': stop}[action](root)
    print(json.dumps(result, ensure_ascii=False, indent=2))
    return 1 if result.get('error') else 0


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=('start', 'status', 'stop', 'run'))
    parser.add_argument('--root', type=Path, required=True)
    args = parser.parse_args()
    raise SystemExit(command(args.root.resolve(), args.action))
