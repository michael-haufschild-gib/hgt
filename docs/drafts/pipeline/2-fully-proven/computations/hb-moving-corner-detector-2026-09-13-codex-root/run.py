import json
import os
import signal
import subprocess
import time

started = time.monotonic()
limit = 570
env = dict(os.environ)
env["CAMPAIGN_DEADLINE"] = str(started + limit)
proc = subprocess.Popen(["python3", "experiment.py"], env=env, start_new_session=True)
status = "complete"
try:
    code = proc.wait(timeout=limit)
    if code:
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
with open("run-status.json", "w") as f:
    json.dump({"status": status, "exit_code": code, "seconds": time.monotonic() - started}, f, indent=2)
raise SystemExit(code)
