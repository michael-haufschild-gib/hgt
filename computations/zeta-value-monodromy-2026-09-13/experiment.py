from common import *
from concurrent.futures import ProcessPoolExecutor,as_completed

def work(job):
    n,kind,dps,step=job;mp.mp.dps=dps;start=time.monotonic()
    out=dict(n=n,kind=kind,dps=dps,step=step)
    try:
        s,info=lift(zeros()[n],lambda u:target(kind,u),step)
        out.update(status='ok',endpoint=enc(s),nearest_zero=closest(s),**info)
    except Exception as e:out.update(status='error',error=repr(e))
    out['seconds']=time.monotonic()-start
    save('loop-%03d-%s-%d.json'%(n,kind,dps),out)
    return {k:v for k,v in out.items() if k!='path'}
if __name__=='__main__':
    start=time.monotonic();jobs=[(n,'circle',50,.035) for n in range(1,65)]
    jobs += [(n,k,50,.035) for n in range(1,17) for k in ['reverse','small','flat','tall']]
    rows=[]
    with ProcessPoolExecutor(max_workers=14) as ex:
        pilot=list(ex.map(work,[jobs[0],jobs[7]]));rows.extend(pilot)
        save('pilot.json',dict(rows=pilot,wall_seconds=time.monotonic()-start,estimate_seconds=max(r['seconds'] for r in pilot)*len(jobs)/14))
        pending=[j for j in jobs if j not in [jobs[0],jobs[7]]]
        for fut in as_completed([ex.submit(work,j) for j in pending]):
            r=fut.result();rows.append(r);print(json.dumps(r),flush=True);save('summary.json',dict(planned=len(jobs),completed=len(rows),rows=rows))
    save('summary.json',dict(planned=len(jobs),completed=len(rows),rows=rows,seconds=time.monotonic()-start))
