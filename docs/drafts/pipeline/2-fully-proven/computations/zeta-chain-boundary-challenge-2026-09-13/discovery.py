from common import *
from concurrent.futures import ProcessPoolExecutor,as_completed

def startpoint(label):
    return -2*abs(label) if label<0 else zeros()[label]
def classify(s):
    candidates={str(n):z for n,z in zeros().items()};candidates.update({'trivial_'+str(m):-2*m for m in range(1,25)})
    candidates.update({'negative_'+str(n):mp.conj(z) for n,z in zeros().items() if n<=10})
    k=min(candidates,key=lambda k:abs(s-candidates[k]));return k,str(abs(s-candidates[k]))
def work(job):
    label,kind,dps=job;mp.mp.dps=dps;start=time.monotonic();r=dict(label=label,kind=kind,dps=dps)
    try:
        s,info=lift(startpoint(label),lambda u:target(kind,u),.018)
        r.update(status='ok',endpoint=enc(s),endpoint_label=classify(s),**info)
    except Exception as e:r.update(status='error',error=repr(e))
    r['seconds']=time.monotonic()-start;save('path-%s-%s-%d.json'%(label,kind,dps),r)
    return {k:v for k,v in r.items() if k!='path'}
if __name__=='__main__':
    # Trivial roots require a wider left domain; this is declared in protocol.
    jobs=[(n,k,50) for n in range(-1,-17,-1) for k in ['circle','reverse','small','flat','tall']]
    jobs += [(n,'circle',50) for n in list(range(65,129))+list(range(257,321))]
    rows=[];start=time.monotonic()
    with ProcessPoolExecutor(max_workers=14) as ex:
        pilots=[jobs[0],jobs[80]];pilot=list(ex.map(work,pilots));rows.extend(pilot)
        save('pilot.json',dict(rows=pilot,seconds=time.monotonic()-start))
        for f in as_completed([ex.submit(work,j) for j in jobs if j not in pilots]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['label'],r['kind'],r.get('endpoint_label',r.get('error')),flush=True)
