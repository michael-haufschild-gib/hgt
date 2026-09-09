"""Start/stop the local research stack; remote GPU jobs remain independent."""
from __future__ import annotations
import argparse
import fcntl
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

from lean_research_background import atomic_json, start as start_indexer, stop as stop_indexer, status as indexer_status
from lean_research_corpus import cache_directory
from lean_research_qdrant import IMAGE, Qdrant, settings
from lean_research_runtime import RuntimeClient

ROOT=Path(__file__).resolve().parents[1]


def docker_binary():
    bundled=Path('/Applications/Docker.app/Contents/Resources/bin/docker')
    found=str(bundled) if bundled.exists() else shutil.which('docker')
    if not found:
        raise RuntimeError('Docker Desktop missing. Install with: brew install --cask docker-desktop')
    return found


def docker(*args, check=True, timeout=60):
    executable=docker_binary()
    env={**os.environ,'PATH':str(Path(executable).parent)+os.pathsep+os.environ.get('PATH','')}
    return subprocess.run([executable,*args],check=check,capture_output=True,text=True,env=env,timeout=timeout)


def matching_processes(directory):
    output=subprocess.check_output(['ps','-axo','pid=,command='],text=True)
    result=[]
    for line in output.splitlines():
        pid,_,command=line.strip().partition(' ')
        if not pid.isdigit() or int(pid)==os.getpid():continue
        if command.endswith('research_runtime.worker --cache-dir '+str(directory)):
            result.append((int(pid),'inference',command))
        elif str(directory/'runpod')+'/' in command and any(name in command for name in ('lean_research_method_sync.py','lean_research_batch_sync.py')):
            result.append((int(pid),'receiver',command))
    return result


def stop_process(pid, expected):
    def current():
        return subprocess.run(['ps','-p',str(pid),'-o','command='],capture_output=True,text=True).stdout.strip()
    if current()!=expected.strip():return
    try:os.kill(pid,signal.SIGTERM)
    except ProcessLookupError:return
    deadline=time.monotonic()+8
    while current()==expected.strip() and time.monotonic()<deadline:time.sleep(.1)
    if current()==expected.strip():
        os.kill(pid,signal.SIGKILL)
        raise RuntimeError(f'Process {pid} required forced shutdown')


def stop(directory):
    (directory/'services-stopped').touch()
    stop_indexer(ROOT)
    deadline=time.monotonic()+8
    while indexer_status(ROOT)['running'] and time.monotonic()<deadline:time.sleep(.1)
    if indexer_status(ROOT)['running']:
        raise RuntimeError('Indexer did not stop; Qdrant left running to preserve writes')
    for pid,kind,command in matching_processes(directory):
        if kind=='receiver':stop_process(pid,command)
    for pid,kind,command in matching_processes(directory):
        if kind=='inference':stop_process(pid,command)
    if docker('info',check=False,timeout=5).returncode==0:
        name=settings(directory)['container']
        existing=docker('inspect',name,check=False)
        if existing.returncode==0:
            docker('stop','--time','15',name,timeout=25)
    atomic_json(directory/'services.json',dict(running=False,updated=time.time()))
    print('Stopped research indexer, inference worker, local GPU receivers and Qdrant.',flush=True)


def start_receivers(directory):
    existing=matching_processes(directory)
    started=[]
    for connection_path in sorted((directory/'runpod').glob('*/connection.json')):
        job=connection_path.parent
        status_path=job/'sync-status.json'
        state=json.loads(status_path.read_text()) if status_path.exists() else {}
        if state.get('completed'):continue
        if any(str(job) in command for _,kind,command in existing if kind=='receiver'):continue
        manifest=job/'bundle/manifest.json'
        if not manifest.exists():continue
        data=json.loads(manifest.read_text())
        method='proof-methods' in str(data.get('format',''))
        script='lean_research_method_sync.py' if method else 'lean_research_batch_sync.py'
        with (job/'sync.log').open('ab') as log:
            child=subprocess.Popen([sys.executable,str(ROOT/'scripts'/script),'--directory',str(job),
                '--root',str(ROOT)] if method else [sys.executable,str(ROOT/'scripts'/script),'--directory',str(job)],
                cwd=ROOT,stdin=subprocess.DEVNULL,stdout=log,stderr=log,start_new_session=True)
        connection=json.loads(connection_path.read_text());connection['sync_pid']=child.pid
        atomic_json(connection_path,connection);started.append(child.pid)
    return started


def start(directory):
    config=settings(directory)
    if docker('info',check=False,timeout=5).returncode:
        subprocess.run(['open','-a','Docker'],check=True)
        deadline=time.monotonic()+90
        while docker('info',check=False,timeout=5).returncode:
            if time.monotonic()>deadline:raise RuntimeError('Docker did not become ready; finish Docker Desktop setup')
            time.sleep(1)
    name=config['container']
    if docker('inspect',name,check=False).returncode:
        if docker('image','inspect',IMAGE,check=False).returncode:
            print('Downloading Qdrant image...',flush=True)
            docker('pull',IMAGE,timeout=300)
        docker('run','-d','--name',name,'--restart','unless-stopped','--cpus','6','--memory','5g','--memory-swap','5g',
            '-p','127.0.0.1:16333:6333','-p','127.0.0.1:16334:6334','-v',config['volume']+':/qdrant/storage',
            '-e','QDRANT__TELEMETRY_DISABLED=true',IMAGE)
    else:
        docker('start',name)
    q=Qdrant(directory);deadline=time.monotonic()+30
    while True:
        try:q.request('GET','/collections',deadline=min(deadline,time.monotonic()+2));break
        except RuntimeError:
            if time.monotonic()>=deadline:raise
            time.sleep(.2)
    atomic_json(directory/'qdrant.json',config)
    from lean_research_batch import locks
    from lean_research_corpus import Corpus
    from lean_research_qdrant import reconcile
    # A missing collection can be restored from the retained vector archives.
    # Normal restarts avoid scanning the corpus or repeating migration.
    with Corpus(directory,readonly=True) as corpus:
        seeded=corpus.con.execute("SELECT value FROM meta WHERE key='qdrant_initialized'").fetchone()
        models=[r[0] for r in corpus.con.execute('SELECT DISTINCT model FROM vector_shards')]
    missing=[model for model in models if q.request('GET','/collections/'+q.collection(model),missing_ok=True) is None]
    if not seeded or missing:
        with locks([directory/n for n in ('source.lock','compiler.lock','enrichment.lock')],seconds=150), Corpus(directory) as corpus:
            with corpus.con:
                for model in missing:corpus.con.execute('DELETE FROM qdrant_points WHERE model=?',(model,))
            reconcile(corpus)
            with corpus.con:corpus.con.execute("INSERT OR REPLACE INTO meta VALUES('qdrant_initialized','1')")
    (directory/'services-stopped').unlink(missing_ok=True)
    with RuntimeClient(directory) as runtime:
        state=runtime.start()
        if not state.get('available'):raise RuntimeError('Local models unavailable; run research-setup')
    atomic_json(directory/'services.json',dict(running=True,updated=time.time(),qdrant=name))
    worker=start_indexer(ROOT)
    if worker.get('error'):raise RuntimeError(worker['error'])
    receivers=start_receivers(directory)
    print('Running: Qdrant, inference worker, automatic source/method/vector indexing.',flush=True)
    if receivers:print(f'Resumed {len(receivers)} local GPU receiver(s).',flush=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    modes=parser.add_mutually_exclusive_group()
    modes.add_argument('--restart',action='store_true');modes.add_argument('--stop',action='store_true')
    args=parser.parse_args();directory=cache_directory(ROOT);directory.mkdir(parents=True,exist_ok=True)
    with (directory/'services.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        if args.stop or args.restart:stop(directory)
        if not args.stop:start(directory)

if __name__=='__main__':
    try:main()
    except (RuntimeError,subprocess.SubprocessError,OSError) as exc:
        print(str(exc),file=sys.stderr);raise SystemExit(1)
