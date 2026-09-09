from __future__ import annotations

import json
import os
import sys
import tempfile
import time
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from lean_research_cli import default_mode, supervise, release
from lean_research_corpus import cache_directory


class SupervisionTests(unittest.TestCase):
    def test_deadline_returns_last_snapshot_and_terminates_owned_child(self):
        with tempfile.TemporaryDirectory() as tmp:
            pidfile = Path(tmp) / 'pid'
            script = ('import os,time,json,sys\n'
                      'request=json.load(sys.stdin)\n'
                      'open(request["pidfile"],"w").write(str(os.getpid()))\n'
                      'print(json.dumps({"candidate_lemmas":[{"name":"retained"}],"partial":False,"unfinished_stages":[]}),flush=True)\n'
                      'time.sleep(30)\n')
            start = time.monotonic()
            result = supervise([sys.executable, '-c', script], {'mode': 'deep', 'pidfile': str(pidfile)}, deadline=start + .35)
            self.assertLess(time.monotonic() - start, 1.2)
            self.assertEqual(result['candidate_lemmas'][0]['name'], 'retained')
            self.assertTrue(result['partial'])
            self.assertIn('deadline', result['unfinished_stages'])
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
