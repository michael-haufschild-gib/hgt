from source import *
from concurrent.futures import ProcessPoolExecutor,as_completed

def work(job):
    start=time.monotonic();r=dict(job=job,dps=60);roots=[];fails=[]
    try:
        T=Transform(job['host'],job.get('remove'),job.get('insert'));r.update(mass=str(T.mass),second_moment=str(T.m2),sampled_source_positive=bool(T.min_weight>0));grid=[];br=[]
        for j in range(401):
            w=mp.mpf(j)/4;v=mp.re(T.val(w,False));grid.append([str(w),str(v)])
            if j and v*mp.mpf(grid[-2][1])<0:br.append((w-mp.mpf('.25'),w))
        starts=[(a+b)/2 for a,b in br]+[mp.mpc(x,y) for x in range(10,99,4) for y in ['.3','2','6','12','24']]
        if job['host']=='D':starts+=[mp.mpc('85.69934848537759','.308517182456637')]
        for w0 in starts:
            try:
                w,q=T.root(w0)
                if not any(abs(w-dec(z['root']))<mp.mpf('1e-12') for z in roots):roots.append(dict(start=enc(w0),root=enc(w),**q))
            except TimeoutError:raise
            except Exception as e:fails.append(dict(start=enc(w0),error=repr(e)))
        r.update(status='ok',real_grid=grid,real_brackets=[[str(a),str(b)] for a,b in br],starts=len(starts))
    except Exception as e:r.update(status='error',error=repr(e))
    r.update(roots=roots,failures=fails,seconds=time.monotonic()-start);save('case-'+job['label']+'.json',r);return r

def run_jobs(jobs,preparation=None):
    rows=[];start=time.monotonic();save('jobs.json',jobs)
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,j) for j in jobs]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,preparation=preparation,seconds=time.monotonic()-start));print(r['job']['label'],r['status'],len(r['roots']),flush=True)

if __name__=='__main__':
    start=time.monotonic();cs=[controls(h) for h in ['R','B4','L5','D']];save('carrier-controls.json',cs);m={a['host']:mp.mpf(a['second_moment']) for a in cs};zz=json.loads(Path('nodes.json').read_text());jobs=[]
    groups=[[],[1],[0],[4],[7],[8],[12],[0,4],[7,8]]
    for h in ['R','B4','L5','D']:
        for group in groups:
            for mode in (['native','variance'] if h!='R' and group else ['native']):
                scale=mp.sqrt(m[h]/m['R']) if mode=='variance' else mp.mpf(1)
                ins=[enc(dec(zz[i])*scale) for i in group]
                jobs.append(dict(label=h+'-'+('none' if not group else '_'.join(map(str,group)))+'-'+mode,host=h,remove=[],insert=ins,donor_indices=group,mode=mode,donor_scale=str(scale)))
    run_jobs(jobs,dict(seconds=time.monotonic()-start,controls='passed'))
