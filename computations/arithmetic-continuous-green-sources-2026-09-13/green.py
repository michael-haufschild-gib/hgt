from source import *
from concurrent.futures import ProcessPoolExecutor,as_completed

class Green:
    def __init__(self,host,dps=60,hden=64):
        mp.mp.dps=dps;self.host=host;T=Transform(host,hden=hden,dps=dps);self.M={a:mp.fsum(v*mp.cosh(mp.mpf(a)*x) for x,v in zip(T.x,T.weights))*T.mass for a in ['.5','1.5']}
    def one(self,z,a):
        budget();sgn=-1 if mp.re(z)<0 else 1;z*=sgn;a=mp.mpf(a)
        if abs(mp.im(z))>=mp.pi/4:raise ArithmeticError('source strip')
        if self.host=='R':q=1;parity=0;c=None;gamma=mp.mpf('.5')
        else:q,parity,c=config(self.host);gamma=mp.mpf('.5')+parity
        Q=mp.pi*mp.exp(2*z)/q;N=int(mp.ceil(mp.sqrt((mp.mp.dps+80)*mp.log(10)/mp.re(Q))))+3
        if N>1500:raise ArithmeticError('source term cap')
        tails=[]
        for sig in [1,-1]:
            v=(gamma+sig*a)/2;U=mp.mpc(0)
            for n in range(1,N+1):
                co=1 if c is None else c[n%q]*n**parity
                if co==0:continue
                b=mp.pi*n*n/q;t=b*mp.exp(2*z)
                value=(2*mp.gammainc(v+2,t,mp.inf)-3*mp.gammainc(v+1,t,mp.inf)) if c is None else co*mp.gammainc(v,t,mp.inf)
                U+=b**(-v)*value
            tails.append(U)
        key='.5' if a==mp.mpf('.5') else '1.5';l=mp.exp(-a*z)*(self.M[key]-tails[0]);r=mp.exp(a*z)*tails[1]
        return l+r,sgn*a*(r-l),abs(l)+abs(r)
    def val(self,z,mode):
        if mode!='mixed':return self.one(z,mode)
        u=self.one(z,'.5');v=self.one(z,'1.5');return mp.mpf('1.5')*u[0]-v[0]/2,mp.mpf('1.5')*u[1]-v[1]/2,mp.mpf('1.5')*u[2]+v[2]/2

def work(job):
    start=time.monotonic();roots=[];fail=[];r=dict(job=job,dps=60)
    try:
        G=Green(job['host']);mode=job['mode']
        for x in ['0','.12','.3','.55','.9','1.3','1.9','2.5']:
            for y in ['.15','.35','.5','.62','.7','.75','.78','.784']:
                z=mp.mpc(x,y);seed=enc(z)
                try:
                    for it in range(44):
                        f,d,n=G.val(z,mode);ds=f/d
                        if abs(ds)<mp.mpf('1e-28') and abs(f)/n<mp.mpf('1e-28'):break
                        if abs(ds)>.15:ds*=mp.mpf('.15')/abs(ds)
                        zz=z-ds
                        if abs(mp.im(zz))>=mp.pi/4:zz=z-ds/2
                        z=zz
                        if abs(mp.re(z))>3.5 or not(mp.mpf('1e-8')<abs(mp.im(z))<mp.pi/4):raise ArithmeticError('root domain escape')
                    else:raise ArithmeticError('root iteration limit')
                    z=mp.mpc(abs(mp.re(z)),abs(mp.im(z)))
                    if not any(abs(z-dec(t['root']))<mp.mpf('1e-18') for t in roots):roots.append(dict(root=enc(z),correction=str(abs(ds)),normalized_residual=str(abs(f)/n),iterations=it))
                except Exception as e:fail.append(dict(start=seed,error=repr(e)))
        r.update(status='ok',moments={a:str(v) for a,v in G.M.items()})
    except Exception as e:r.update(status='error',error=repr(e))
    roots.sort(key=lambda r:float(r['root'][1]));r.update(roots=roots,failed_starts=fail,seconds=time.monotonic()-start);save('case-'+job['label']+'.json',r);return r
if __name__=='__main__':
    start=time.monotonic();G=Green('R');checks=[]
    for z in [mp.mpc('.3','.2'),mp.mpc('1','.5')]:
        val=G.one(z,'.5')[0];E=mp.exp(2*z);Q=mp.exp(-mp.pi*E);ref=mp.exp(-z/2)/2-mp.exp(z/2)*(mp.jtheta(3,0,Q)-1)/2;err=abs(val-ref)/abs(ref);assert err<mp.mpf('1e-24');checks.append(str(err))
    save('pilot.json',dict(seconds=time.monotonic()-start,closed_R_expression_errors=checks,moments={a:str(v) for a,v in G.M.items()}))
    jobs=[dict(host=h,mode=m,label=h+'-'+m) for h in ['R','B4','L5','D'] for m in ['.5','1.5','mixed']];save('jobs.json',jobs);rows=[]
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,j) for j in jobs]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['job']['label'],r['status'],len(r['roots']),flush=True)
