from source import *
from concurrent.futures import ProcessPoolExecutor,as_completed

def work(job):
    x,y=job;mp.mp.dps=60;start=time.monotonic();r=dict(start=[x,y],dps=60)
    try:
        z=mp.mpc(str(x),str(y))
        for it in range(60):
            v,nn,N,e=jets(z,3);Q=v[0]*v[2]-v[1]**2;Qp=v[0]*v[3]-v[1]*v[2];scale=abs(v[0]*v[2])+abs(v[1])**2
            if abs(Q)/scale<mp.mpf('1e-43') and abs(Q/Qp)<mp.mpf('1e-37'):break
            dz=Q/Qp
            if abs(dz)>.1:dz*=mp.mpf('.1')/abs(dz)
            z-=dz
            if abs(mp.re(z))>3 or abs(mp.im(z))>=mp.mpf('.7851'):raise ArithmeticError('Newton domain escape')
        else:raise ArithmeticError('Newton iteration limit')
        w=-1j*v[1]/v[0];vv,n2,N2,e2=jets(z,3,extra=30);qq=vv[0]*vv[2]-vv[1]**2;ww=-1j*vv[1]/vv[0]
        r.update(status='ok',point=enc(z),frequency=enc(w),residual=str(abs(Q)/scale),term_refinement_residual=str(abs(qq)/(abs(vv[0]*vv[2])+abs(vv[1])**2)),frequency_truncation_disagreement=str(abs(ww-w)),normalized_source_value=str(abs(v[0])/nn),terms=N,iterations=it)
    except Exception as ex:r.update(status='error',error=repr(ex))
    r['seconds']=time.monotonic()-start;save('critical-%s-%s.json'%(x,y),r);return r
if __name__=='__main__':
    jobs=[(x,y) for x in [0,.025,.05,.075,.1,.15,.2,.3,.4,.5,.6,.7,.85,1,1.25,1.5,1.75,2] for y in [.05,.15,.3,.4,.5,.55,.6,.625,.65,.675,.7,.725,.74,.755,.765,.775,.781,.784]];rows=[];start=time.monotonic()
    with ProcessPoolExecutor(max_workers=14) as ex:
        pilots=[(0,.4),(.5,.775)];pr=list(ex.map(work,pilots));rows.extend(pr);save('pilot.json',dict(rows=pr,seconds=time.monotonic()-start))
        for f in as_completed([ex.submit(work,j) for j in jobs if j not in pilots]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['start'],r.get('frequency',r.get('error')),flush=True)
