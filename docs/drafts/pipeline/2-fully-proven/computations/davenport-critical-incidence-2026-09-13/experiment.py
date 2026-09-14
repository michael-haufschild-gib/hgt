from carrier import *
from concurrent.futures import ProcessPoolExecutor,as_completed

def work(job):
    sigma,T=job;configure(60);start=time.monotonic();r=dict(start_real=sigma,start_height=T,dps=60)
    try:
        s=mp.mpc(str(sigma),str(T))
        for _ in range(40):
            v=D(s,1)
            if abs(v)<mp.mpf('1e-45'):break
            ds=v/D(s,2)
            if abs(ds)>1.5:ds*=mp.mpf('1.5')/abs(ds)
            s-=ds
            if not (-3<mp.re(s)<8 and 70<mp.im(s)<102):raise ArithmeticError('critical Newton domain escape')
        if abs(D(s,1))>mp.mpf('1e-43'):raise ArithmeticError('critical residual')
        cv=D(s);r.update(critical_point=enc(s),critical_value=enc(cv),critical_residual=str(abs(D(s,1))),second_derivative=enc(D(s,2)))
        eps=mp.mpf('1e-6');delta=mp.sqrt(-2*cv*eps/D(s,2));branches=[]
        for sign in [-1,1]:
            p=s+sign*delta;w=cv*(1-eps)
            for _ in range(10):p-=(D(p)-w)/D(p,1)
            end,info=c.lift(p,lambda u:cv*(1-eps)*(1-u),.018)
            branches.append(dict(sign=sign,endpoint=enc(end),endpoint_label=classify(end),**info))
        r.update(status='ok',branches=branches)
    except Exception as e:r.update(status='error',error=repr(e))
    r['seconds']=time.monotonic()-start;save('critical-%s-%s.json'%(sigma,T),r)
    out={k:v for k,v in r.items() if k!='branches'}
    if 'branches' in r:out['endpoints']=[br['endpoint_label'] for br in r['branches']]
    return out
if __name__=='__main__':
    start=time.monotonic();prepare();jobs=[(s,T) for s in [.15,.4,.8,1.5,2.5] for T in [76.5+j for j in range(20)]]
    jobs += [(s,T) for s in [.1,.3,.5,.7,.9] for T in [85.2,85.7,86.2]];rows=[]
    with ProcessPoolExecutor(max_workers=14) as ex:
        pilots=[jobs[0],jobs[-8]];pp=list(ex.map(work,pilots));rows.extend(pp);save('pilot.json',dict(rows=pp,preparation_plus_pilot_seconds=time.monotonic()-start))
        for f in as_completed([ex.submit(work,j) for j in jobs if j not in pilots]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['start_real'],r['start_height'],r.get('endpoints',r.get('error')),flush=True)
