import argparse
import ctypes
import ctypes.util
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time

p = argparse.ArgumentParser()
p.add_argument('--seconds', type=float, default=90)
p.add_argument('--max-mib', type=float, default=1024)
p.add_argument('--log-prefix', required=True)
p.add_argument('command', nargs=argparse.REMAINDER)
a = p.parse_args()
command = a.command[1:] if a.command[:1] == ['--'] else a.command
started = time.monotonic()
peak = 0.0
samples = 0
reason = 'completed'
child = None

class RUsageV0(ctypes.Structure):
    _fields_ = [('ri_uuid', ctypes.c_uint8 * 16)] + [
        (name, ctypes.c_uint64) for name in (
            'ri_user_time', 'ri_system_time', 'ri_pkg_idle_wkups',
            'ri_interrupt_wkups', 'ri_pageins', 'ri_wired_size',
            'ri_resident_size', 'ri_phys_footprint',
            'ri_proc_start_abstime', 'ri_proc_exit_abstime')]

libproc = ctypes.CDLL(ctypes.util.find_library('proc'), use_errno=True)
libproc.proc_pid_rusage.argtypes = [ctypes.c_int, ctypes.c_int, ctypes.c_void_p]
libproc.proc_pid_rusage.restype = ctypes.c_int

def physical_mib(pid):
    info = RUsageV0()
    if libproc.proc_pid_rusage(pid, 0, ctypes.byref(info)) != 0:
        return None
    return info.ri_phys_footprint / (1024 * 1024)

def members():
    if child is None:
        return []
    rows = subprocess.check_output(['ps', '-axo', 'pid=,pgid='], text=True)
    return [int(parts[0]) for line in rows.splitlines()
            if len(parts := line.split()) == 2 and int(parts[1]) == child.pid]

def stop():
    if child is None or child.poll() is not None:
        return
    for pid in members():
        if pid != child.pid:
            try:
                os.kill(pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
    child.terminate()
    try:
        child.wait(timeout=3)
    except subprocess.TimeoutExpired:
        child.kill()
        child.wait(timeout=3)

def interrupted(signum, frame):
    raise KeyboardInterrupt

signal.signal(signal.SIGTERM, interrupted)
with open(a.log_prefix + '.log', 'w') as log:
    try:
        child = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT,
                                 start_new_session=True)
        print(json.dumps({'pid': child.pid, 'command': command,
                          'physical_limit_mib': a.max_mib}), flush=True)
        while child.poll() is None:
            physical = 0.0
            for pid in members():
                footprint = physical_mib(pid)
                if footprint is not None:
                    physical += footprint
            samples += 1
            peak = max(peak, physical)
            if physical > a.max_mib:
                reason = 'physical memory cutoff'
                stop()
                break
            if time.monotonic() - started > a.seconds:
                reason = 'time cutoff'
                stop()
                break
            time.sleep(0.1)
    except KeyboardInterrupt:
        reason = 'interrupted'
        stop()
    finally:
        stop()

result = {'command': command, 'exit_code': child.returncode if child else None,
          'reason': reason, 'seconds': round(time.monotonic() - started, 2),
          'sampled_peak_physical_mib': round(peak, 1), 'samples': samples,
          'measurement': 'proc_pid_rusage RUSAGE_INFO_V0 ri_phys_footprint',
          'remaining_owned_pids': members()}
Path(a.log_prefix + '.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result), flush=True)
raise SystemExit(child.returncode if reason == 'completed' and child else 125)
