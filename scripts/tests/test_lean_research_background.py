import os
from pathlib import Path
import sys
import tempfile
import time
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from lean_research_background import start, status, stop


class BackgroundTests(unittest.TestCase):
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
