from source import *
from concurrent.futures import ProcessPoolExecutor,as_completed
import numpy as np
from scipy.integrate import solve_ivp

def fast(z):
    budget();sgn=-1 if z.real<0 else 1;zz=sgn*z;q1=np.pi*np.exp(2*zz);c=q1.real
    if c<=0:raise ArithmeticError('flow outside strip')
    N=int(np.ceil(np.sqrt(95/c)))+6
    if N>1000:raise ArithmeticError('flow term budget')
    q=np.arange(1,N+1)**2*q1;ex=np.exp(-(q-q1));v=[np.sum(np.polynomial.polynomial.polyval(q,p)*ex)*sgn**k for k,p in enumerate(POLYS[:3])]
    norm=np.sum(abs(np.polynomial.polynomial.polyval(q,POLYS[0])*ex));return v,norm,zz/2-q1+np.log(v[0])

def flow(z,w,direction,side):
    v,nn,lg=fast(z);hess=-(v[2]/v[0]-(v[1]/v[0])**2);axis=np.sqrt(1/hess)*(1 if direction==1 else 1j);axis/=abs(axis);p=z+side*1e-5*axis
    def rhs(t,a):
        v,n,l=fast(complex(*a));g=np.conj(-v[1]/v[0]+1j*w);g*=direction/max(abs(g),1e-30);return [g.real,g.imag]
    def boundary(t,a):return min(2.5-abs(a[0]),.78-abs(a[1]))
    boundary.terminal=True;boundary.direction=-1
    def zero(t,a):
        v,n,l=fast(complex(*a));return abs(v[0])/n-1e-9
    zero.terminal=True;zero.direction=-1
    def real(t,a):return a[1]
    sol=solve_ivp(rhs,[0,8],[p.real,p.imag],rtol=1e-8,atol=1e-10,max_step=.004,events=[boundary,zero,real])
    phases=[];s0=-fast(p)[2]+1j*w*p
    for a in sol.y.T:
        pp=complex(*a);ss=-fast(pp)[2]+1j*w*pp;phases.append(abs(np.angle(np.exp(1j*(ss-s0).imag))))
    return dict(direction=direction,side=side,status=int(sol.status),message=sol.message,endpoint=sol.y[:,-1].tolist(),arc=float(sol.t[-1]),boundary_events=sol.t_events[0].tolist(),source_zero_events=sol.t_events[1].tolist(),real_crossings=[x.tolist() for x in sol.y_events[2]],max_wrapped_phase_drift=max(phases),path=sol.y.T.tolist())

def work(job):
    label,ww=job;mp.mp.dps=50;w=mp.mpc(*ww);start=time.monotonic();r=dict(label=label,w=ww,dps=50);roots=[];fails=[];flows=[]
    try:
        for x in [-1.5,-.75,-.25,0,.25,.75,1.5]:
            for y in [-.2,-.5,-.7,-.775]:
                try:
                    z,info=solve(mp.mpc(str(x),str(y)),w)
                    if not any(abs(z-dec(v['point']))<mp.mpf('1e-20') for v in roots):roots.append(dict(point=enc(z),**info))
                except Exception as e:fails.append(dict(start=[x,y],error=repr(e)))
        save('saddles-'+label+'.json',dict(roots=roots,failures=fails,w=ww))
        for k,a in enumerate(roots):
            z=complex(float(a['point'][0]),float(a['point'][1]))
            if abs(z.real)>=2.5 or abs(z.imag)>=.7799:continue
            for di in [-1,1]:
                for side in [-1,1]:
                    try:f=flow(z,complex(w),di,side);f.update(saddle=k)
                    except Exception as e:f=dict(saddle=k,direction=di,side=side,error=repr(e))
                    flows.append(f);save('flows-'+label+'.json',dict(w=ww,roots=roots,flows=flows))
        r.update(status='ok',roots=roots,newton_failures=fails,flows=[{k:v for k,v in f.items() if k!='path'} for f in flows])
    except Exception as e:r.update(status='error',error=repr(e),roots=roots,newton_failures=fails)
    r['seconds']=time.monotonic()-start;save('target-'+label+'.json',r);return r
if __name__=='__main__':
    mp.mp.dps=70;zz=zeros();jobs=[]
    for n in [1,2,3,5,8,13]:
        t=mp.im(zz[n]);jobs.append(('zero_%02d'%n,[str(t),'0']));jobs.append(('mid_%02d'%n,[str((t+mp.im(zz[n+1]))/2),'0']))
    for n in [1,13]:
        for a in ['-.25','.25']:jobs.append(('tilt_%02d_%s'%(n,a),[str(mp.im(zz[n])),a]))
    save('parameters.json',dict(jobs=jobs));rows=[];start=time.monotonic()
    with ProcessPoolExecutor(max_workers=14) as ex:
        pilot=list(ex.map(work,jobs[:2]));rows.extend(pilot);save('pilot.json',dict(rows=pilot,seconds=time.monotonic()-start))
        for f in as_completed([ex.submit(work,j) for j in jobs[2:]]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['label'],r['status'],len(r['roots']),flush=True)
