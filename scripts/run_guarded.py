#!/usr/bin/env python3
"""Run a foreground job with a hard deadline and owned process-group cleanup.

Usage: python3 scripts/run_guarded.py --timeout 600 -- python3 /tmp/job.py
Wrap a whole pipeline using -- /bin/zsh -c 'python3 /tmp/job.py | tail -20'.
Exit 124 means timeout, 125 means caller disappeared, 128+signal means cancelled.
The small guardian survives caller termination, including SIGKILL, and detects
it through pipe EOF. No persistent daemon, global process scan or name matching.
Jobs must not detach themselves into another session.
"""
import argparse
import math
import os
import select
import signal
import subprocess
import sys
import time

from research_runtime.processes import terminate_owned


def supervise(command, control, timeout, grace):
    stopped = 0

    def stop(signum, _frame):
        nonlocal stopped
        stopped = 128 + signum

    for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
        signal.signal(sig, stop)
    child = subprocess.Popen(command, start_new_session=True)
    deadline = time.monotonic() + timeout
    try:
        while child.poll() is None:
            if stopped:
                return stopped
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                print('run_guarded: deadline reached; stopping owned process group', file=sys.stderr, flush=True)
                return 124
            if select.select([control], [], [], min(.1, remaining))[0]:
                if not os.read(control, 1):
                    return 125
        return child.returncode if child.returncode >= 0 else 128 - child.returncode
    finally:
        terminate_owned(child, grace=grace)


def run(command, *, timeout, grace=.25):
    read_fd, write_fd = os.pipe()
    guardian = os.fork()
    if guardian == 0:
        os.close(write_fd)
        os.setsid()
        try:
            code = supervise(command, read_fd, timeout, grace)
        except Exception as exc:
            print(f'run_guarded: {exc}', file=sys.stderr, flush=True)
            code = 125
        finally:
            os.close(read_fd)
        os._exit(code)
    os.close(read_fd)
    cancelled = 0

    def stop(signum, _frame):
        nonlocal cancelled, write_fd
        cancelled = 128 + signum
        if write_fd is not None:
            os.close(write_fd)
            write_fd = None

    old = {sig: signal.signal(sig, stop) for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)}
    try:
        _, status = os.waitpid(guardian, 0)
        code = os.waitstatus_to_exitcode(status)
        return cancelled or (code if code >= 0 else 128 - code)
    finally:
        if write_fd is not None:
            os.close(write_fd)
        for sig, handler in old.items():
            signal.signal(sig, handler)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=float, required=True)
    parser.add_argument('--grace', type=float, default=.25)
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not command or not math.isfinite(args.timeout) or args.timeout <= 0 or not math.isfinite(args.grace) or args.grace < 0:
        parser.error('provide a command, a positive finite timeout and a nonnegative finite grace')
    return run(command, timeout=args.timeout, grace=args.grace)


if __name__ == '__main__':
    raise SystemExit(main())
