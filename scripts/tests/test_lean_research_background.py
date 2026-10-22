import os
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest import mock
import subprocess

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from lean_research_background import start, status, stop, classify_failures, small_shard_count, maintenance_contention, terminate_owned
from lean_research_corpus import Corpus


class BackgroundTests(unittest.TestCase):
    def test_embedding_pause_preserves_sources_and_qdrant_and_can_resume(self):
        from lean_research_background import run
        from lean_research_corpus import cache_directory
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            directory = cache_directory(root)
            directory.mkdir(parents=True)
            marker = directory / 'embeddings-paused.json'
            marker.write_text('{}')
            (directory / 'qdrant.json').write_text('{}')
            child = mock.Mock(returncode=0)
            child.poll.return_value = 0
            with mock.patch('lean_research_background.subprocess.Popen', return_value=child) as spawn, \
                    mock.patch('lean_research_background.terminate_owned'), \
                    mock.patch('lean_research_background.signal.signal'), \
                    mock.patch('lean_research_runtime.RuntimeClient') as client:
                client.return_value.__enter__.return_value.status.return_value = {'available': True}
                run(root, once=True)
                commands = [call.args[0] for call in spawn.call_args_list]
                self.assertTrue(any('--corpus' in command for command in commands))
                self.assertTrue(any(str(root / 'scripts/lean_research_qdrant.py') in command for command in commands))
                self.assertFalse(any('--vectors' in command for command in commands))
                self.assertTrue(status(root)['embeddings_paused'])
                marker.unlink()
                spawn.reset_mock()
                run(root, once=True)
                self.assertTrue(any('--vectors' in call.args[0] for call in spawn.call_args_list))
                self.assertFalse(status(root)['embeddings_paused'])

    def test_compaction_runs_even_when_qdrant_serves_queries(self):
        """Publication writes one small file per batch and `sync` reads those
        files back, so compaction is required whoever serves the queries."""
        from lean_research_background import run
        from lean_research_corpus import cache_directory
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            directory = cache_directory(root)
            directory.mkdir(parents=True)
            (directory / 'qdrant.json').write_text('{}')
            child = mock.Mock(returncode=0)
            child.poll.return_value = 0
            with mock.patch('lean_research_background.subprocess.Popen', return_value=child) as spawn, \
                    mock.patch('lean_research_background.terminate_owned'), \
                    mock.patch('lean_research_background.signal.signal'), \
                    mock.patch('lean_research_background.small_shard_count', return_value=1000), \
                    mock.patch('lean_research_runtime.RuntimeClient') as client:
                client.return_value.__enter__.return_value.status.return_value = {'available': True}
                run(root, once=True)
                commands = [call.args[0] for call in spawn.call_args_list]
            self.assertTrue(any('--compact' in command for command in commands))

    def test_compaction_probe_tolerates_a_cache_without_a_database(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            self.assertEqual(small_shard_count(directory), 0)

    def test_denied_group_shutdown_reaps_direct_child(self):
        child = mock.Mock(pid=123456789)
        child.poll.return_value = None
        with mock.patch('lean_research_background.os.killpg', side_effect=PermissionError):
            terminate_owned(child)
        child.kill.assert_called_once_with()
        child.wait.assert_called_once_with()

    def test_denied_force_group_shutdown_reaps_direct_child(self):
        child = mock.Mock(pid=123456789)
        child.poll.return_value = None
        with mock.patch('lean_research_background.os.killpg', side_effect=[None, PermissionError()]):
            terminate_owned(child)
        child.kill.assert_called_once_with()
        child.wait.assert_called_once_with()

    def test_running_worker_detects_added_edited_and_deleted_lean(self):
        import sqlite3
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);(root/'scripts').mkdir();(root/'formal').mkdir()
            scripts=Path(__file__).resolve().parents[1]
            (root/'scripts/formal_tools.py').write_text(
                f'import sys;sys.path.insert(0,{str(scripts)!r})\n'
                'from pathlib import Path\nfrom lean_research_corpus import Corpus,cache_directory\n'
                'root=Path.cwd()\nwith Corpus(cache_directory(root)) as c:c.refresh(root)\n')
            from lean_research_corpus import cache_directory
            def await_names(expected):
                deadline=time.monotonic()+40
                while time.monotonic()<deadline:
                    try:
                        with Corpus(cache_directory(root),readonly=True) as c:
                            names=[r[0] for r in c.con.execute('SELECT name FROM declarations ORDER BY name')]
                        if names==expected:return
                    except sqlite3.OperationalError:pass
                    time.sleep(.1)
                self.fail(f'background source indexing did not reach {expected}')
            source=root/'formal/A.lean';source.write_text('theorem alpha : True := True.intro')
            running=start(root)
            try:
                await_names(['alpha'])
                source.write_text('theorem beta : True := True.intro')
                await_names(['beta'])
                source.unlink();await_names([])
                self.assertEqual(status(root)['pid'],running['pid'])
            finally:
                stop(root);deadline=time.monotonic()+3
                while status(root)['running'] and time.monotonic()<deadline:time.sleep(.1)
                self.assertFalse(status(root)['running'])

    def test_structured_busy_deferral_needs_no_traceback_or_failure_exit(self):
        busy = dict(stage='methods', reason='maintenance_busy', lock='enrichment.lock')
        malformed = dict(stage='method', error='local model did not return a JSON object')
        errors, deferred = classify_failures([
            dict(complete=False, deferred=[busy]), dict(deferred=[busy], failures=[malformed])])
        self.assertEqual(errors, [malformed])
        self.assertEqual(deferred, [busy])

    def test_compaction_probe_reads_committed_state_while_importer_holds_writer(self):
        with tempfile.TemporaryDirectory() as tmp, Corpus(Path(tmp)) as writer:
            writer.con.execute('BEGIN IMMEDIATE')
            writer.con.execute("INSERT INTO vector_shards VALUES('pending','pending.faiss','m',32,0)")
            try:
                self.assertEqual(small_shard_count(Path(tmp)), 0)
            finally:
                writer.con.rollback()

    def test_maintenance_contention_is_retryable_but_model_failures_are_not(self):
        self.assertTrue(maintenance_contention('sqlite3.OperationalError: database is locked'))
        self.assertTrue(maintenance_contention('Another enrichment process owns the resumable queue.\n'))
        self.assertFalse(maintenance_contention('local model did not return a JSON object'))

    def test_expected_interruptions_are_distinct_from_invalid_model_output(self):
        malformed = dict(stage='method', error='local model did not return a JSON object')
        preempted = dict(stage='embedding', error='enrichment preempted by interactive search; retry later')
        deadline = dict(stage='embedding', error='local runtime deadline expired')
        errors, deferred = classify_failures([dict(failures=[malformed,preempted]), dict(failures=[malformed,preempted,deadline])])
        self.assertEqual(errors, [malformed])
        self.assertEqual(deferred, [preempted,deadline])

    def test_single_worker_stop_during_phase_reaps_only_owned_child(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'scripts').mkdir()
            (root / 'scripts/formal_tools.py').write_text(
                "import os,time,pathlib\n"
                "pathlib.Path('phase_pid').write_text(str(os.getpid()))\n"
                "time.sleep(30)\n")
            first = start(root)
            try:
                self.assertTrue(first['running'])
                self.assertEqual(start(root)['pid'], first['pid'])
                deadline = time.monotonic() + 3
                while not (root / 'phase_pid').exists() and time.monotonic() < deadline:
                    time.sleep(.05)
                child = int((root / 'phase_pid').read_text())
                self.assertTrue(stop(root)['stop_requested'])
                while status(root)['running'] and time.monotonic() < deadline:
                    time.sleep(.05)
                self.assertFalse(status(root)['running'])
                self.assertEqual(status(root)['phase'], 'stopped')
                with self.assertRaises(ProcessLookupError):
                    os.kill(child, 0)
            finally:
                stop(root)
                deadline = time.monotonic() + 2
                while status(root)['running'] and time.monotonic() < deadline:
                    time.sleep(.05)


if __name__ == '__main__':
    unittest.main()
