from common import *
from concurrent.futures import ProcessPoolExecutor,as_completed

def work(job):
    n,sigma=job;mp.mp.dps=50;start=time.monotonic();zz=zeros();mid=(mp.im(zz[n])+mp.im(zz[n+1]))/2
    out=dict(gap=n,start_real=sigma);s=mp.mpc(sigma,mid)
    try:
        for k in range(35):
            v=zeta(s,1)
            if abs(v)<mp.mpf('1e-38'):break
            ds=v/zeta(s,2)
            if abs(ds)>2:ds*=2/abs(ds)
            s-=ds
            if not (-2<mp.re(s)<7 and abs(mp.im(s)-mid)<15):raise ArithmeticError('critical Newton domain escape')
        if abs(zeta(s,1))>mp.mpf('1e-35'):raise ArithmeticError('critical solve residual')
        c=zeta(s);out.update(critical_point=enc(s),critical_value=enc(c),critical_residual=str(abs(zeta(s,1))),second_derivative=enc(zeta(s,2)),distance_to_one=str(abs(c-1)),status='critical_found')
        # Two inverse sheets leave the simple critical point towards target zero.
        eps=mp.mpf('1e-5');delta=mp.sqrt(-2*c*eps/zeta(s,2));branches=[]
        for sign in [-1,1]:
            p=s+sign*delta
            w=c*(1-eps)
            for _ in range(8):p-=(zeta(p)-w)/zeta(p,1)
            end,info=lift(p,lambda u:c*(1-eps)*(1-u),.035)
            branches.append(dict(sign=sign,endpoint=enc(end),nearest_zero=closest(end),**info))
        out.update(status='ok',branches=branches)
    except Exception as e:out.update(status='error',error=repr(e))
    out['seconds']=time.monotonic()-start;save('critical-%03d-%s.json'%(n,str(sigma).replace('.','p')),out)
    result={k:v for k,v in out.items() if k!='branches'}
    if 'branches' in out:result['endpoints']=[b['nearest_zero'] for b in out['branches']]
    return result
if __name__=='__main__':
    start=time.monotonic();jobs=[(n,sigma) for n in range(1,64) for sigma in ['.7','1.3','2.0']];rows=[]
    with ProcessPoolExecutor(max_workers=14) as ex:
        pilots=[jobs[0],jobs[10]];pilot=list(ex.map(work,pilots));rows.extend(pilot)
        save('pilot.json',dict(rows=pilot,wall_seconds=time.monotonic()-start,estimate_seconds=max(r['seconds'] for r in pilot)*len(jobs)/14))
        for fut in as_completed([ex.submit(work,j) for j in jobs if j not in pilots]):
            r=fut.result();rows.append(r);print(json.dumps(r),flush=True);save('summary.json',dict(planned=len(jobs),completed=len(rows),rows=rows))
    save('summary.json',dict(planned=len(jobs),completed=len(rows),rows=rows,seconds=time.monotonic()-start))
