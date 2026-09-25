"""Whole-family deadline; stops only the experiment's owned process group."""
import hashlib
import json
import os
import platform
import resource
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

root = Path.cwd()
start = time.monotonic()
env = dict(os.environ)
for name in ['OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS',
             'VECLIB_MAXIMUM_THREADS', 'NUMEXPR_NUM_THREADS']:
    env[name] = '1'
env['CAMPAIGN_DEADLINE'] = str(start + 265)
def limits():
    resource.setrlimit(resource.RLIMIT_AS, (3 * 1024**3, 3 * 1024**3))
    resource.setrlimit(resource.RLIMIT_FSIZE, (256 * 1024**2, 256 * 1024**2))
versions = subprocess.check_output([sys.executable, '-m', 'pip', 'freeze'], text=True, timeout=10)
metadata = dict(python=sys.version, platform=platform.platform(),
                affinity=sorted(os.sched_getaffinity(0)), packages=versions.splitlines(),
                cap_seconds=275, cleanup_seconds=10, max_workers=14,
                threads_per_worker=1, memory_limit_per_process_bytes=3*1024**3,
                input_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                              for p in root.iterdir() if p.is_file()})
(root/'environment.json').write_text(json.dumps(metadata, indent=2)+'\n')
with open('stdout.log', 'w', buffering=1) as out:
    proc = subprocess.Popen([sys.executable] + sys.argv[1:], env=env,
                            stdout=out, stderr=subprocess.STDOUT,
                            start_new_session=True, preexec_fn=limits)
    reason = None
    while proc.poll() is None:
        elapsed = time.monotonic()-start
        size = sum(p.stat().st_size for p in root.rglob('*') if p.is_file())
        if elapsed >= 275: reason = 'whole-family deadline'
        elif size > 2*1024**3: reason = 'scratch quota'
        elif shutil.disk_usage(root).free < 1024**3: reason = 'free disk reserve'
        if reason:
            os.killpg(proc.pid, signal.SIGTERM)
            try: proc.wait(timeout=7)
            except subprocess.TimeoutExpired: pass
            break
        time.sleep(.5)
    # Even after a parent exits, kill any surviving owned children.
    try: os.killpg(proc.pid, signal.SIGKILL)
    except ProcessLookupError: pass
    proc.wait(timeout=2)
status = dict(returncode=proc.returncode, stop_reason=reason,
              seconds=time.monotonic()-start, owned_group_cleaned=True)
(root/'run-status.json').write_text(json.dumps(status, indent=2)+'\n')
print(json.dumps(status), flush=True)
with open(root/'SHA256SUMS', 'w') as out:
    for path in sorted(root.iterdir()):
        if path.is_file() and path.name != 'SHA256SUMS':
            out.write(hashlib.sha256(path.read_bytes()).hexdigest()+'  '+path.name+'\n')
sys.exit(0 if proc.returncode == 0 else 1)
