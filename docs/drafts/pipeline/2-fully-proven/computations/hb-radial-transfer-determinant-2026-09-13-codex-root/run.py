import json
import os
import signal
import subprocess
import sys
import time

script = sys.argv[1]
limit = 570
started = time.monotonic()
env = dict(os.environ)
env["CAMPAIGN_DEADLINE"] = str(started + limit)
proc = subprocess.Popen([sys.executable, script], env=env, start_new_session=True)
status = "complete"
try:
    code = proc.wait(timeout=limit)
    if code != 0:
        status = "failed"
except subprocess.TimeoutExpired:
    status = "timeout"
    os.killpg(proc.pid, signal.SIGTERM)
    try:
        proc.wait(timeout=5)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        proc.wait()
    code = 124
with open("run-status-" + os.path.splitext(script)[0] + ".json", "w") as f:
    json.dump({"script": script, "status": status, "exit_code": code, "seconds": time.monotonic() - started}, f, indent=2)
raise SystemExit(code)
