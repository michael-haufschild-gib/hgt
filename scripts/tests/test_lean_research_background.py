import os
from pathlib import Path
import sys
import tempfile
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from lean_research_background import start, status, stop, classify_failures, small_shard_count, maintenance_contention
from lean_research_corpus import Corpus


class BackgroundTests(unittest.TestCase):
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
