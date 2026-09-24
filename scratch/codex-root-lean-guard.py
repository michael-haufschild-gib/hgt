"""Run one foreground Lean/Lake command, aborting on memory pressure or overlap.

This is a task-local safety wrapper, not a build system.  It never signals
processes outside its own child tree.
"""

import argparse
import os
import signal
import subprocess
import sys
import time


def processes():
    out = subprocess.check_output(
        ["ps", "-axo", "pid=,ppid=,rss=,comm="], text=True
    )
    rows = {}
    for line in out.splitlines():
        fields = line.strip().split(maxsplit=3)
        if len(fields) == 4:
            pid, ppid, rss, command = fields
            rows[int(pid)] = (int(ppid), int(rss), os.path.basename(command))
    return rows


def child_tree(root, rows):
    result = {root}
    while True:
        enlarged = result | {
            pid for pid, (ppid, _, _) in rows.items() if ppid in result
        }
        if enlarged == result:
            return result
        result = enlarged


def free_percent():
    out = subprocess.check_output(["memory_pressure", "-Q"], text=True)
    marker = "System-wide memory free percentage: "
    return int(out.split(marker, 1)[1].split("%", 1)[0])


def stop_child_tree(root):
    for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGKILL):
        rows = processes()
        owned = child_tree(root, rows)
        if not any(pid in rows for pid in owned):
            return
        for pid in sorted(owned, reverse=True):
            if pid in rows:
                try:
                    os.kill(pid, sig)
                except ProcessLookupError:
                    pass
        time.sleep(0.25)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cwd", required=True)
    parser.add_argument("--max-rss-mib", type=int, default=3800)
    parser.add_argument("--min-free-percent", type=int, default=25)
    parser.add_argument("--allow-other-lean", action="store_true")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("command required after --")
    scratch_check = (
        command[:3] == ["lake", "env", "lean"]
        and len(command) in (4, 5)
        and (len(command) == 4 or command[3] == "-j1")
        and command[-1].endswith(".lean")
    )
    leaf_audit = (
        len(command) == 4 and command[:3] == ["lake", "--old", "build"]
        and command[3].endswith(":olean")
    )
    if not (scratch_check or leaf_audit):
        parser.error("only one scratch Lean file or one leaf :olean audit is allowed")
    initial = processes()
    if not args.allow_other_lean and any(name in {"lean", "lake"} for _, _, name in initial.values()):
        print("guard: another Lean/Lake process is active; not starting", file=sys.stderr)
        return 75
    if free_percent() < args.min_free_percent:
        print("guard: memory headroom too low; not starting", file=sys.stderr)
        return 75
    child = subprocess.Popen(command, cwd=args.cwd)
    try:
        while child.poll() is None:
            rows = processes()
            owned = child_tree(child.pid, rows)
            rss = sum(rows[pid][1] for pid in owned if pid in rows)
            other_lean = any(
                pid not in owned and name in {"lean", "lake"}
                for pid, (_, _, name) in rows.items()
            )
            if rss > args.max_rss_mib * 1024 or (other_lean and not args.allow_other_lean) or free_percent() < args.min_free_percent:
                reason = "RSS cap" if rss > args.max_rss_mib * 1024 else (
                    "another Lean/Lake process" if other_lean and not args.allow_other_lean else "memory pressure"
                )
                print(
                    f"guard: stopping own Lean/Lake tree: {reason}; "
                    f"owned RSS {rss // 1024} MiB; free {free_percent()}%",
                    file=sys.stderr,
                )
                stop_child_tree(child.pid)
                child.wait()
                return 75
            time.sleep(0.25)
    except BaseException:
        stop_child_tree(child.pid)
        child.wait()
        raise
    return child.returncode


if __name__ == "__main__":
    raise SystemExit(main())
