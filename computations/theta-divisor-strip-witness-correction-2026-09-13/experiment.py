from common import *
from concurrent.futures import ProcessPoolExecutor,as_completed
import math

class Transform:
    def __init__(self,remove,hden=64,dps=50):
        mp.mp.dps=dps;self.remove=remove;self.h=mp.mpf(1)/hden;self.nodes=[dec(z) for z in json.loads(Path('nodes.json').read_text())];self.weights=[];self.x=[]
        nmax=int(mp.ceil(mp.sqrt((dps+60)*mp.log(10)/mp.pi)))+2
        for j in range(int(mp.mpf('3.5')*hden)+1):
            budget();x=j*self.h;Q=mp.pi*mp.exp(2*x)
            ph=mp.fsum(mp.exp(x/2-n*n*Q)*(4*(n*n*Q)**2-6*n*n*Q) for n in range(1,nmax+1))
            P=mp.mpf(1)
            for i in remove:
                z=self.nodes[i]
                P*=1+x*x/mp.im(z)**2 if i==1 else abs(1-x*x/z**2)**2
            self.x.append(x);self.weights.append((1 if j==0 else 2)*self.h*ph/P)
        self.mass=mp.fsum(self.weights);self.m2=mp.fsum(x*x*c for x,c in zip(self.x,self.weights))/self.mass
        self.weights=[v/self.mass for v in self.weights]
    def val(self,w,jet=True):
        budget();c=mp.cos(w*self.h);s=mp.sin(w*self.h);cj=mp.mpc(1);sj=mp.mpc(0);F=mp.mpc(0);D=mp.mpc(0)
        for x,a in zip(self.x,self.weights):
            F+=a*cj
            if jet:D-=a*x*sj
            cj,sj=cj*c-sj*s,sj*c+cj*s
        return (F,D) if jet else F
    def root(self,w):
        w=mp.mpc(w)
        for k in range(36):
            F,D=self.val(w);step=F/D
            if abs(step)<mp.mpf('1e-22'):
                return w,dict(residual=str(abs(F)),correction=str(abs(step)),iterations=k)
            if abs(step)>3:step*=3/abs(step)
            w-=step
            if not(0<mp.re(w)<100 and abs(mp.im(w))<40):raise ArithmeticError('root domain escape')
        raise ArithmeticError('root iteration limit')

def work(job):
    start=time.monotonic();r=dict(job=job,dps=50,hden=64);roots=[];fails=[]
    try:
        T=Transform(job['remove']);r.update(mass=str(T.mass),second_moment=str(T.m2));grid=[];brackets=[]
        for j in range(321):
            w=mp.mpf(j)/4;v=mp.re(T.val(w,False));grid.append([str(w),str(v),str(v*mp.exp(mp.pi*w/4))])
            if j and v*mp.mpf(grid[-2][1])<0:brackets.append((w-mp.mpf('.25'),w))
        r['real_grid']=grid
        starts=[(a+b)/2 for a,b in brackets]+[mp.mpc(a,b) for a in range(10,79,4) for b in ['.3','2','6','12','28']]
        for w0 in starts:
            try:
                w,detail=T.root(w0)
                if not any(abs(w-dec(q['root']))<mp.mpf('1e-12') for q in roots):roots.append(dict(start=enc(w0),root=enc(w),**detail))
            except TimeoutError:raise
            except Exception as e:fails.append(dict(start=enc(w0),error=repr(e)))
        r.update(status='ok',real_brackets=[[str(a),str(b)] for a,b in brackets],planned_starts=len(starts))
    except Exception as e:r.update(status='error',error=repr(e))
    r.update(roots=roots,failures=fails,seconds=time.monotonic()-start)
    save('case-'+job['label']+'.json',r);return r

if __name__=='__main__':
    jobs=json.loads(Path('jobs.json').read_text());rows=[];start=time.monotonic()
    # One inexpensive literal/small case pilots performance before workers.
    p=jobs[0];pilot=work(p);rows.append(pilot);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start))
    if pilot['status']!='ok':raise RuntimeError('pilot failed')
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,j) for j in jobs[1:]]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['job']['label'],r['status'],len(r['roots']),flush=True)
