"""Real process lifetimes: no model loads or Lean builds."""
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from research_runtime.processes import terminate_owned

RUNNER = str(Path(__file__).resolve().parents[1] / 'run_guarded.py')


def alive(pid):
    result = subprocess.run(['ps', '-p', str(pid), '-o', 'stat='], capture_output=True, text=True)
    return bool(result.stdout.strip()) and not result.stdout.strip().startswith('Z')


class ProcessTests(unittest.TestCase):
    def await_dead(self, pid):
        deadline = time.monotonic() + 3
        while alive(pid) and time.monotonic() < deadline:
            time.sleep(.02)
        self.assertFalse(alive(pid), f'owned process {pid} survived cleanup')

    def test_parent_exit_and_term_resistant_grandchild_are_both_cleaned_up(self):
        with tempfile.TemporaryDirectory() as tmp:
            marker = Path(tmp) / 'child'
            script = ('import os,signal,time\n'
                      'pid=os.fork()\n'
                      'if pid:\n'
                      f' while not os.path.exists({str(marker)!r}):time.sleep(.01)\n'
                      ' os._exit(0)\n'
                      'signal.signal(signal.SIGTERM,signal.SIG_IGN)\n'
                      f'open({str(marker)!r},"w").write(str(os.getpid()))\n'
                      'time.sleep(30)\n')
            child = subprocess.Popen([sys.executable, '-c', script], start_new_session=True)
            try:
                child.wait(timeout=3)
                descendant = int(marker.read_text())
                self.assertTrue(alive(descendant))
                terminate_owned(child, grace=.05)
                self.await_dead(descendant)
            finally:
                terminate_owned(child, grace=0)

    def test_runner_preserves_stdin_stdout_and_failure_exit(self):
        result = subprocess.run([sys.executable, RUNNER, '--timeout', '3', '--', sys.executable,
                                 '-c', 'import sys;print(sys.stdin.read());sys.exit(7)'],
                                input='exact input', text=True, capture_output=True, timeout=5)
        self.assertEqual(result.returncode, 7)
        self.assertEqual(result.stdout, 'exact input\n')

    def test_search_sigterm_returns_partial_and_reaps_engine(self):
        with tempfile.TemporaryDirectory() as tmp:
            marker = Path(tmp)/'engine'
            engine = ('import os,sys,time,json\njson.load(sys.stdin)\n'
                      f'open({str(marker)!r},"w").write(str(os.getpid()))\n'
                      'print(json.dumps({"candidate_lemmas":[{"name":"kept"}],"partial":True}),flush=True)\n'
                      'time.sleep(30)')
            parent_code = ('import sys,time,json\n'
                           f'sys.path.insert(0,{str(Path(RUNNER).parent)!r})\n'
                           'from lean_research_cli import supervise\n'
                           f'print(json.dumps(supervise([sys.executable,"-c",{engine!r}],{{}},deadline=time.monotonic()+10)))')
            parent = subprocess.Popen([sys.executable,'-c',parent_code], stdout=subprocess.PIPE,
                                      stderr=subprocess.PIPE, text=True, start_new_session=True)
            try:
                deadline=time.monotonic()+3
                while not marker.exists() and time.monotonic()<deadline:time.sleep(.01)
                pid=int(marker.read_text());time.sleep(.05)
                parent.terminate()
                output,errors=parent.communicate(timeout=3)
                import json
                result=json.loads(output)
                self.assertIn('cancelled',result['unfinished_stages'])
                self.assertEqual(result['candidate_lemmas'][0]['name'],'kept')
                self.await_dead(pid)
            finally:
                terminate_owned(parent,grace=0)

    def test_deadline_cancel_and_killed_caller_stop_only_owned_job(self):
        unrelated = subprocess.Popen([sys.executable, '-c', 'import time;time.sleep(30)'], start_new_session=True)
        try:
            for action in ('deadline', 'term', 'kill'):
                with self.subTest(action=action), tempfile.TemporaryDirectory() as tmp:
                    marker = Path(tmp) / 'pid'
                    code = ('import os,signal,time\n'
                            'signal.signal(signal.SIGTERM,signal.SIG_IGN)\n'
                            f'open({str(marker)!r},"w").write(str(os.getpid()))\n'
                            'time.sleep(30)\n')
                    wrapper = subprocess.Popen([sys.executable, RUNNER, '--timeout', '1' if action == 'deadline' else '10',
                                                '--grace', '.05', '--', sys.executable, '-c', code],
                                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)
                    try:
                        deadline = time.monotonic() + 3
                        while not marker.exists() and time.monotonic() < deadline:
                            time.sleep(.01)
                        pid = int(marker.read_text())
                        if action == 'term': wrapper.terminate()
                        if action == 'kill': wrapper.kill()
                        result = wrapper.wait(timeout=4)
                        self.assertEqual(result, {'deadline': 124, 'term': 143, 'kill': -9}[action])
                        self.await_dead(pid)
                        self.assertIsNone(unrelated.poll())
                    finally:
                        terminate_owned(wrapper, grace=0)
        finally:
            terminate_owned(unrelated, grace=0)

    def test_search_supervisor_reaps_grandchild_after_engine_exits(self):
        from lean_research_cli import supervise
        with tempfile.TemporaryDirectory() as tmp:
            marker = Path(tmp) / 'pid'
            code = ('import os,sys,time,json,signal\njson.load(sys.stdin)\npid=os.fork()\n'
                    'if pid:\n'
                    f' while not os.path.exists({str(marker)!r}):time.sleep(.01)\n'
                    ' print(json.dumps({"candidate_lemmas":[{"name":"kept"}],"partial":False}),flush=True)\n'
                    ' os._exit(0)\n'
                    'signal.signal(signal.SIGTERM,signal.SIG_IGN)\n'
                    f'open({str(marker)!r},"w").write(str(os.getpid()))\n'
                    'time.sleep(30)\n')
            result = supervise([sys.executable, '-c', code], {}, deadline=time.monotonic()+.4)
            self.assertEqual(result['candidate_lemmas'][0]['name'], 'kept')
            self.assertTrue(result['partial'])
            self.await_dead(int(marker.read_text()))


if __name__ == '__main__':
    unittest.main()
