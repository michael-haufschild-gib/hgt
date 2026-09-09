"""CLI integration and deadline supervision, importable without model packages."""
from __future__ import annotations

import json
import fcntl
import os
import selectors
import signal
import sqlite3
import subprocess
import sys
import time
from contextlib import ExitStack, contextmanager
from pathlib import Path

from lean_research_corpus import Corpus, cache_directory, source_priority


class MaintenanceBusy(RuntimeError):
    """Another worker owns a corpus maintenance lock."""


@contextmanager
def maintenance_locks(directory: Path):
    # Match the bulk importer's lock order. Hold all writer locks before even
    # opening Corpus: schema initialization itself can start a transaction.
    directory.mkdir(parents=True, exist_ok=True)
    with ExitStack() as stack:
        for name in ('source.lock', 'compiler.lock', 'enrichment.lock'):
            lock = stack.enter_context((directory / name).open('a'))
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                raise MaintenanceBusy(name) from None
        yield


def compile_corpus(root: Path, corpus: Corpus, *, deadline: float, module="", progress=None):
    """Extract small compatible batches, classifying absent artifacts cheaply."""
    from lean_research_export import export_modules
    from lean_research_corpus import digest
    progress = progress or (lambda value: None)
    rows = corpus.con.execute("SELECT * FROM files WHERE collection='lean' AND status='indexed' "
                              "AND compile_status IN ('pending','stale','unavailable') ORDER BY package,path").fetchall()
    ready = []
    missing = 0
    with corpus.con:
        for row in sorted(rows, key=lambda r: (source_priority(r['path']), r['path'])):
            if module and module.casefold() not in row['module'].casefold():
                continue
            if row['module'] == 'GaloisForLFunctions':
                corpus.con.execute("UPDATE files SET compile_status='umbrella_source_only' WHERE path=?", (row['path'],))
                continue
            base = root / 'formal'
            if row['package'] != 'project':
                base = base / '.lake' / 'packages' / row['package']
            artifact = base / '.lake' / 'build' / 'lib' / 'lean' / (row['module'].replace('.', '/') + '.olean')
            if not artifact.is_file():
                corpus.con.execute("UPDATE files SET compile_status='unavailable' WHERE path=?", (row['path'],))
                missing += 1
            else:
                ready.append(row)
    progress(dict(available_modules=len(ready), missing_artifacts=missing))
    batches = [ready[i:i + 8] for i in range(0, len(ready), 8)]
    while batches and time.monotonic() < deadline:
        batch = batches.pop(0)
        modules = [row['module'] for row in batch]
        if len(set(modules)) != len(modules):
            batches[:0] = [[r] for r in batch]
            continue
        result = export_modules(root / 'formal', modules, timeout_seconds=min(60, deadline - time.monotonic()),
                                source_paths={row['module']: root / row['path'] for row in batch})
        status = result.get('status', 'failed')
        if status not in ('ok', 'partial'):
            if len(batch) > 1 and time.monotonic() < deadline:
                # A single broken import must not hide otherwise available
                # modules. Retry disjoint halves sequentially, never in parallel.
                middle = len(batch) // 2
                batches[:0] = [batch[:middle], batch[middle:]]
                continue
            with corpus.con:
                for row in batch:
                    outcome = 'pending' if status == 'timeout' else 'error'
                    corpus.con.execute('UPDATE files SET compile_status=? WHERE path=?', (outcome, row['path']))
            progress(dict(modules=modules, compiler=status, error=result.get('error', '')))
            continue
        for row in batch:
            source = root / row['path']
            try:
                current = digest(source.read_bytes()) == row['source_hash']
            except OSError:
                current = False
            snapshot = result.get('snapshots', {}).get(row['module'], {})
            if snapshot.get('source_path') and Path(snapshot['source_path']).resolve() != source.resolve():
                current = False
            if not current:
                with corpus.con:
                    corpus.con.execute("UPDATE files SET compile_status='stale' WHERE path=?", (row['path'],))
                progress(dict(module=row['module'], compiler='source_changed_or_mapping_mismatch'))
                continue
            snapshot_status = 'stale_snapshot' if snapshot.get('freshness') == 'stale' else 'compiled_snapshot'
            declarations = [d for d in result.get('declarations', []) if d['module'] == row['module']]
            if any(d.get('status') == 'error' for d in declarations):
                snapshot_status += '_partial'
            applied = corpus.install_compiler_rows(row['path'], declarations, source_hash=row['source_hash'], status=snapshot_status)
            progress(dict(module=row['module'], compiler=snapshot_status, declarations=applied))


def default_mode(root: Path) -> str:
    """Progressive hybrid can run during enrichment; deep requires acceptance."""
    try:
        release = json.loads((cache_directory(root) / "release.json").read_text())
        if release.get("accepted") is True:
            return 'deep'
    except (OSError, ValueError):
        pass
    try:
        directory = cache_directory(root)
        if json.loads((directory / 'progressive.json').read_text()).get('enabled') and (directory / 'corpus.sqlite3').is_file():
            return 'hybrid'
    except (OSError, ValueError):
        pass
    return 'lexical'


def release(root: Path, report_path: Path) -> dict:
    """Promote the measured configuration; an incomplete report cannot activate it."""
    from lean_research_benchmark import release_gates
    from lean_research_corpus import digest
    report = json.loads(report_path.read_text())
    gates = release_gates(report)
    if not gates.get('passed'):
        return dict(accepted=False, gates=gates)
    directory = cache_directory(root)
    directory.mkdir(parents=True, exist_ok=True)
    record = dict(accepted=True, activated_at=time.time(), report_path=str(report_path.resolve()),
                  report_hash=digest(report_path.read_bytes()), gates=gates)
    temporary = directory / ('release.%d.tmp' % os.getpid())
    try:
        temporary.write_text(json.dumps(record, indent=2))
        os.replace(temporary, directory / 'release.json')
    finally:
        temporary.unlink(missing_ok=True)
    return record


def engine_python(root: Path) -> str:
    try:
        from lean_research_runtime import runtime_python
        path = runtime_python(root)
        if Path(path).exists():
            return str(path)
    except (ImportError, AttributeError):
        pass
    return sys.executable


def empty_extra(mode: str, reason: str) -> dict:
    return dict(mode=mode, candidate_lemmas=[], proof_ideas=[], ingredient_sets=[], source_arguments=[],
                prose=[], source_passages=[], partial=True, unfinished_stages=[reason], query_trace=[], elapsed_seconds=0)


def supervise(command: list[str], request: dict, *, deadline: float) -> dict:
    """Read progressive snapshots while enforcing the whole child lifetime."""
    latest = empty_extra(request.get("mode", "deep"), "not_started")
    if time.monotonic() >= deadline:
        latest["unfinished_stages"] = ["deadline"]
        return latest
    # Start a separate process group so only this request's owned processes are
    # terminated. The shared model worker must detach its own process group.
    process = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, start_new_session=True)
    selector = selectors.DefaultSelector()
    buffers = {"stdout": b"", "stderr": b""}
    try:
        process.stdin.write(json.dumps(request).encode())
        process.stdin.close()
        for stream, name in ((process.stdout, "stdout"), (process.stderr, "stderr")):
            os.set_blocking(stream.fileno(), False)
            selector.register(stream, selectors.EVENT_READ, name)
        while selector.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                latest["partial"] = True
                latest.setdefault("unfinished_stages", []).append("deadline")
                break
            for key, _ in selector.select(min(.1, remaining)):
                chunk = os.read(key.fileobj.fileno(), 65536)
                if not chunk:
                    selector.unregister(key.fileobj)
                    continue
                name = key.data
                if name == "stderr":
                    buffers[name] = (buffers[name] + chunk)[-4000:]
                    continue
                buffers[name] += chunk
                while b"\n" in buffers[name]:
                    line, buffers[name] = buffers[name].split(b"\n", 1)
                    try:
                        value = json.loads(line)
                        if isinstance(value, dict) and "candidate_lemmas" in value:
                            latest = value
                    except (ValueError, UnicodeError):
                        continue
                if len(buffers[name]) > 16 * 1024 * 1024:
                    raise ValueError("search result exceeded bounded protocol size")
        if not selector.get_map() and process.poll() is None:
            try:
                process.wait(timeout=max(0, min(.1, deadline - time.monotonic())))
            except subprocess.TimeoutExpired:
                latest['partial'] = True
                latest.setdefault('unfinished_stages', []).append('engine_did_not_exit')
        if process.poll() not in (None, 0):
            latest["partial"] = True
            latest.setdefault("unfinished_stages", []).append("engine_failed")
            latest["engine_error"] = buffers["stderr"].decode(errors="replace")
    except KeyboardInterrupt:
        latest["partial"] = True
        latest.setdefault("unfinished_stages", []).append("cancelled")
    finally:
        selector.close()
        if process.poll() is None:
            try:
                os.killpg(process.pid, signal.SIGTERM)
                process.wait(timeout=.25)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            except ProcessLookupError:
                process.wait()
        process.stdout.close()
        process.stderr.close()
    if latest.get('partial') and latest.get('active_stage') not in (None, 'finished'):
        latest.setdefault('unfinished_stages', []).append(latest['active_stage'])
    if 'unfinished_stages' in latest:
        latest['unfinished_stages'] = list(dict.fromkeys(s for s in latest['unfinished_stages'] if s != 'search_in_progress'))
    return latest


def discovery(root: Path, args, options: dict) -> dict:
    start = getattr(args, "research_started", time.monotonic())
    deadline = start + args.budget_seconds
    directory = cache_directory(root)
    if not (directory / "corpus.sqlite3").exists():
        return empty_extra(args.mode, "corpus_not_initialized: run search-index --corpus")
    refresh = None
    if not args.no_refresh and time.monotonic() < deadline:
        from lean_research_background import status
        if status(root).get('running'):
            refresh = dict(complete=False, reason='background_indexer_running')
        else:
            # Inventory and coverage counts can exceed refresh's cooperative
            # deadline. Supervise its entire lifetime; never spend the search
            # budget waiting for a maintenance write lock.
            refresh_seconds = min(3, max(0, (deadline - time.monotonic()) * .15))
            command = [sys.executable, str(Path(__file__).resolve())]
            refreshed = supervise(command, dict(root=str(root), mode='refresh', budget_seconds=refresh_seconds),
                                   deadline=time.monotonic() + refresh_seconds)
            refresh = refreshed.get('refresh', dict(complete=False, reason='refresh_deferred',
                                                   unfinished_stages=refreshed.get('unfinished_stages', []),
                                                   error=refreshed.get('engine_error')))
    request = dict(root=str(root), query=" ".join(args.query), mode=args.mode,
                   budget_seconds=max(0, deadline - time.monotonic()),
                   options={**options, "limit": args.limit, "retrieval_views": getattr(args, 'retrieval_views', 'all'),
                            "max_rounds": getattr(args, 'max_rounds', 3)})
    result = supervise([engine_python(root), str(root / "scripts" / "lean_research_engine.py")], request, deadline=deadline)
    if refresh is not None:
        result["refresh"] = refresh
        if not refresh.get("complete"):
            result["partial"] = True
            result.setdefault("unfinished_stages", []).append("source_refresh")
    result["elapsed_seconds"] = time.monotonic() - start
    return result


def refresh_main():
    request = json.load(sys.stdin)
    root = Path(request['root'])
    directory = cache_directory(root)
    try:
        with maintenance_locks(directory), Corpus(directory) as corpus:
            refresh = corpus._refresh(root, deadline=time.monotonic() + request['budget_seconds'])
    except MaintenanceBusy as exc:
        refresh = dict(complete=False, reason='maintenance_busy', lock=str(exc))
    except (sqlite3.DatabaseError, OSError) as exc:
        refresh = dict(complete=False, error=str(exc))
    print(json.dumps(dict(candidate_lemmas=[], refresh=refresh)), flush=True)


def render_discovery(extra: dict) -> None:
    print("\nResearch discovery: %s%s (%.2fs)" % (extra.get("mode", "deep"),
          "; partial" if extra.get("partial") else "", extra.get("elapsed_seconds", 0)))
    for label, key in (("Candidate lemmas", "candidate_lemmas"), ("Proof ideas", "proof_ideas"),
                       ("Source arguments", "source_arguments")):
        values = extra.get(key, [])
        if not values:
            continue
        print(label + ":")
        for hit in values:
            print("- %s %s:%s [%s]" % (hit['name'], hit['relpath'], hit['line'], hit.get('compiler_status', 'source_only')))
            if hit.get("transfer"):
                print("  Transfer: " + hit["transfer"])
                print("  Obligations: " + "; ".join(hit.get("obligations", [])))
            elif key == "candidate_lemmas":
                print("  " + hit['statement'].replace('\n', '\n  '))
            elif hit.get("method"):
                print("  " + hit['method']['description'])
    for group in extra.get("ingredient_sets", []):
        print("Proposed ingredient set: " + group["description"])
        for step in group["steps"]:
            print("- " + step["goal"] + ": " + ", ".join(c['name'] for c in step['candidates']))
            if step["obligations"]:
                print("  Obligations: " + "; ".join(step["obligations"]))
    if extra.get("unfinished_stages"):
        print("Unfinished: " + ", ".join(extra["unfinished_stages"]))
    if extra.get("coverage"):
        print("Coverage: " + json.dumps(extra["coverage"], ensure_ascii=False))


def corpus_index(root: Path, args) -> int:
    import math
    if not math.isfinite(args.budget_seconds) or args.budget_seconds <= 0:
        print('indexing budget must be a finite positive number', file=sys.stderr)
        return 2
    python = engine_python(root)
    if (args.methods or args.vectors or args.compact) and os.path.abspath(python) != os.path.abspath(sys.executable):
        flags = ['search-index', '--budget-seconds', str(args.budget_seconds)]
        flags.extend('--' + key for key in ('corpus', 'compiler', 'methods', 'vectors', 'compact') if getattr(args, key, False))
        if args.module:
            flags.extend(['--module', args.module])
        return subprocess.call([python, str(root / 'scripts' / 'formal_tools.py'), *flags])
    directory = cache_directory(root)
    deadline = time.monotonic() + args.budget_seconds
    progress = lambda value: print(json.dumps(value), file=sys.stderr, flush=True)
    enriched = False
    try:
        with maintenance_locks(directory), Corpus(directory) as corpus:
            if args.corpus:
                # The source lock is already held; refresh() would acquire it again.
                print(json.dumps(corpus._refresh(root, deadline=deadline, progress=progress)))
            if args.compiler and time.monotonic() < deadline:
                compile_corpus(root, corpus, deadline=deadline, module=args.module, progress=progress)
            if (args.methods or args.vectors) and time.monotonic() < deadline:
                from lean_research_engine import runtime_for, enrich
                runtime = runtime_for(directory)
                if runtime is None:
                    print('Local models unavailable; run research-setup first.', file=sys.stderr)
                    return 2
                print(json.dumps(enrich(corpus, runtime, deadline=deadline, methods=args.methods, vectors=args.vectors, progress=progress)))
                enriched = True
            if args.compact and time.monotonic() < deadline:
                from lean_research_vectors import Vectors
                for row in corpus.con.execute('SELECT DISTINCT model FROM vector_shards').fetchall():
                    print(json.dumps(Vectors(corpus).compact(row[0], deadline=deadline)))
            if not enriched and time.monotonic() < deadline:
                print(json.dumps(dict(coverage=corpus.coverage()), ensure_ascii=False))
    except MaintenanceBusy as exc:
        deferred = [dict(stage=stage, reason='maintenance_busy', lock=str(exc))
                    for stage in ('corpus', 'compiler', 'methods', 'vectors', 'compact')
                    if getattr(args, stage, False)]
        print(json.dumps(dict(complete=False, reason='maintenance_busy', lock=str(exc), deferred=deferred)))
    return 0


if __name__ == '__main__':
    refresh_main()
