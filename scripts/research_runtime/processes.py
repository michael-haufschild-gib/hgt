"""Cleanup for a freshly owned Popen started with start_new_session=True."""
import os
import signal
import time
import threading
from contextlib import contextmanager


@contextmanager
def cancellation_signals():
    """Let foreground try/finally cleanup also run on terminal/app cancellation."""
    if threading.current_thread() is not threading.main_thread():
        yield
        return
    def interrupt(_signum, _frame):
        raise KeyboardInterrupt
    previous = {sig: signal.signal(sig, interrupt) for sig in (signal.SIGTERM, signal.SIGHUP)}
    try:
        yield
    finally:
        for sig, handler in previous.items():
            signal.signal(sig, handler)


def terminate_owned(child, *, grace=0.25):
    """Stop the entire group even after its leader exits; reap the direct child.

    Call immediately at the end of ownership, never with a PID from a file or
    process-name search. Detached services must own separate sessions.
    """
    try:
        os.killpg(child.pid, signal.SIGTERM)
        deadline = time.monotonic() + grace
        while time.monotonic() < deadline:
            child.poll()
            os.killpg(child.pid, 0)
            time.sleep(min(.02, max(0, deadline - time.monotonic())))
        os.killpg(child.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    except PermissionError:
        # Retain the direct-child fallback on systems denying group signals.
        child.kill()
    child.wait()
