"""Run each research test module in a separate, owned foreground process.

Production isolates Torch inference from FAISS retrieval. The test audit does
likewise: their macOS wheels load different OpenMP runtimes and cannot safely
share one interpreter. Never use KMP_DUPLICATE_LIB_OK to suppress that failure.
"""
from pathlib import Path
import os
import signal
import subprocess
import sys


def main():
    root = Path(__file__).resolve().parents[2]
    paths = sorted((root / 'scripts/tests').glob('test_lean_research_*.py'))
    for path in paths:
        print(path.name, flush=True)
        child = subprocess.Popen([sys.executable, str(path), '-q'], cwd=root, start_new_session=True)
        try:
            code = child.wait(timeout=240)
            if code:
                return code
        finally:
            if child.poll() is None:
                os.killpg(child.pid, signal.SIGTERM)
                try:
                    child.wait(timeout=1)
                except subprocess.TimeoutExpired:
                    os.killpg(child.pid, signal.SIGKILL)
                    child.wait()
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
