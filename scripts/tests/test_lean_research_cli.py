from __future__ import annotations

import json
import fcntl
import io
import os
import sys
import tempfile
import time
import unittest
from types import SimpleNamespace
from unittest.mock import patch
from pathlib import Path
from contextlib import redirect_stdout, redirect_stderr

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from lean_research_cli import default_mode, supervise, release, discovery, corpus_index, refresh_main
from lean_research_corpus import Corpus, cache_directory


class SupervisionTests(unittest.TestCase):
    def test_enrichment_does_not_repeat_corpus_coverage_scan(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            args = SimpleNamespace(budget_seconds=2, module='', corpus=False,
                                   compiler=False, methods=True, vectors=False, compact=False)
            report = dict(methods=1, vectors=0, coverage={'methods': {'ready': 1}})
            output = io.StringIO()
            with patch('lean_research_cli.engine_python', return_value=sys.executable), \
                    patch('lean_research_engine.runtime_for', return_value=object()), \
                    patch('lean_research_engine.enrich', return_value=report), \
                    patch.object(Corpus, 'coverage', side_effect=AssertionError('duplicate scan')), \
                    redirect_stdout(output):
                self.assertEqual(corpus_index(root, args), 0)
            self.assertEqual(json.loads(output.getvalue()), report)

    def test_every_maintenance_mode_defers_before_sqlite_startup(self):
        modes = ('corpus', 'compiler', 'methods', 'vectors', 'compact')
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            directory = cache_directory(root)
            with Corpus(directory) as writer:
                for lock_name in ('source.lock', 'compiler.lock', 'enrichment.lock'):
                    with (directory / lock_name).open('a') as lock:
                        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                        writer.con.execute('BEGIN IMMEDIATE')
                        try:
                            for selected in [(mode,) for mode in modes] + [modes]:
                                with self.subTest(lock=lock_name, modes=selected):
                                    args = SimpleNamespace(budget_seconds=1, module='',
                                        **{mode: mode in selected for mode in modes})
                                    output, errors = io.StringIO(), io.StringIO()
                                    with patch('lean_research_cli.engine_python', return_value=sys.executable), \
                                            patch('lean_research_cli.Corpus', wraps=Corpus) as constructor, \
                                            redirect_stdout(output), redirect_stderr(errors):
                                        self.assertEqual(corpus_index(root, args), 0)
                                    constructor.assert_not_called()
                                    report = json.loads(output.getvalue())
                                    self.assertFalse(report['complete'])
                                    self.assertEqual(report['reason'], 'maintenance_busy')
                                    self.assertEqual(report['lock'], lock_name)
                                    self.assertEqual({r['stage'] for r in report['deferred']}, set(selected))
                                    self.assertEqual(errors.getvalue(), '')
                        finally:
                            writer.con.rollback()
                    # A failed later lock must release every earlier lock.
                    for released_name in ('source.lock', 'compiler.lock', 'enrichment.lock'):
                        with (directory / released_name).open('a') as released:
                            fcntl.flock(released, fcntl.LOCK_EX | fcntl.LOCK_NB)

    def test_unlocked_source_and_compiler_run_under_one_lock_without_self_contention(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'formal').mkdir()
            (root / 'formal/Alpha.lean').write_text('theorem alpha : True := trivial')
            args = SimpleNamespace(budget_seconds=3, module='Alpha', corpus=True,
                                   compiler=True, methods=False, vectors=False, compact=False)
            output = io.StringIO()
            def compile_probe(root, corpus, **kwargs):
                self.assertEqual(kwargs['module'], 'Alpha')
                for name in ('source.lock', 'compiler.lock', 'enrichment.lock'):
                    with (corpus.directory / name).open('a') as lock:
                        with self.assertRaises(BlockingIOError):
                            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                self.assertEqual(corpus.con.execute('SELECT name FROM declarations').fetchone()[0], 'alpha')
            with patch('lean_research_cli.compile_corpus', side_effect=compile_probe) as compiler, \
                    redirect_stdout(output), redirect_stderr(io.StringIO()):
                self.assertEqual(corpus_index(root, args), 0)
            compiler.assert_called_once()
            reports = [json.loads(line) for line in output.getvalue().splitlines()]
            self.assertTrue(reports[0]['complete'])
            self.assertEqual(reports[0]['changed'], 1)

    def test_search_refresh_defers_before_sqlite_initialization(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            directory = cache_directory(root)
            with Corpus(directory) as writer, (directory / 'enrichment.lock').open('a') as lock:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
                writer.con.execute('BEGIN IMMEDIATE')
                request = io.StringIO(json.dumps(dict(root=str(root), budget_seconds=1)))
                output = io.StringIO()
                try:
                    with patch('sys.stdin', request), redirect_stdout(output), \
                            patch('lean_research_cli.Corpus', wraps=Corpus) as constructor:
                        refresh_main()
                    constructor.assert_not_called()
                    self.assertEqual(json.loads(output.getvalue())['refresh']['reason'], 'maintenance_busy')
                finally:
                    writer.con.rollback()

    def test_busy_refresh_cannot_stop_readonly_query(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'formal').mkdir()
            (root / 'formal' / 'Alpha.lean').write_text('theorem alpha : True := trivial')
            (root / 'scripts').symlink_to(Path(__file__).resolve().parents[1], target_is_directory=True)
            with Corpus(cache_directory(root)) as writer:
                writer.refresh(root)
                writer.con.execute('BEGIN IMMEDIATE')
                writer.con.execute('DELETE FROM declarations')
                try:
                    args = SimpleNamespace(query=['alpha'], mode='hybrid', no_refresh=False, limit=20,
                                           budget_seconds=3, research_started=time.monotonic())
                    with patch('lean_research_cli.engine_python', return_value=sys.executable):
                        result = discovery(root, args, {})
                    self.assertLess(result['elapsed_seconds'], 3.5)
                    self.assertTrue(result['candidate_lemmas'], result)
                    self.assertEqual(result['refresh']['error'], 'database is locked')
                    self.assertNotIn('engine_failed', result['unfinished_stages'])
                finally:
                    writer.con.rollback()

    def test_deadline_returns_last_snapshot_and_terminates_owned_child(self):
        with tempfile.TemporaryDirectory() as tmp:
            pidfile = Path(tmp) / 'pid'
            script = ('import os,time,json,sys\n'
                      'request=json.load(sys.stdin)\n'
                      'open(request["pidfile"],"w").write(str(os.getpid()))\n'
                      'print(json.dumps({"candidate_lemmas":[{"name":"retained"}],"active_stage":"reranking","partial":True,"unfinished_stages":["search_in_progress"]}),flush=True)\n'
                      'time.sleep(30)\n')
            start = time.monotonic()
            result = supervise([sys.executable, '-c', script], {'mode': 'deep', 'pidfile': str(pidfile)}, deadline=start + .35)
            self.assertLess(time.monotonic() - start, 1.2)
            self.assertEqual(result['candidate_lemmas'][0]['name'], 'retained')
            self.assertTrue(result['partial'])
            self.assertIn('deadline', result['unfinished_stages'])
            self.assertIn('reranking', result['unfinished_stages'])
            self.assertNotIn('search_in_progress', result['unfinished_stages'])
            with self.assertRaises(ProcessLookupError):
                os.kill(int(pidfile.read_text()), 0)

    def test_large_progress_messages_do_not_deadlock_pipe(self):
        script = ('import json,sys\njson.load(sys.stdin)\n'
                  'print(json.dumps({"candidate_lemmas":[{"statement":"x"*300000}],"partial":False}),flush=True)\n')
        result = supervise([sys.executable, '-c', script], {'mode': 'deep'}, deadline=time.monotonic() + 3)
        self.assertEqual(len(result['candidate_lemmas'][0]['statement']), 300000)

    def test_failed_engine_is_explicit_and_stderr_is_bounded(self):
        script = 'import sys\nsys.stderr.write("failure"*10000)\nsys.exit(2)'
        result = supervise([sys.executable, '-c', script], {'mode': 'deep'}, deadline=time.monotonic() + 2)
        self.assertTrue(result['partial'])
        self.assertIn('engine_failed', result['unfinished_stages'])
        self.assertLessEqual(len(result['engine_error']), 4000)

    def test_default_changes_only_after_recorded_acceptance(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.assertEqual(default_mode(root), 'lexical')
            directory = cache_directory(root)
            directory.mkdir(parents=True)
            (directory / 'release.json').write_text('{"accepted":false}')
            self.assertEqual(default_mode(root), 'lexical')
            (directory / 'release.json').write_text('{"accepted":true}')
            self.assertEqual(default_mode(root), 'deep')

    def test_incomplete_report_cannot_activate_default(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            report = root / 'report.json'
            report.write_text('{"release_gates":{"passed":true}}')
            self.assertFalse(release(root, report)['accepted'])
            self.assertEqual(default_mode(root), 'lexical')
            self.assertFalse((cache_directory(root) / 'release.json').exists())


if __name__ == '__main__':
    unittest.main()
