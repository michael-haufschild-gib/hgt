from interaction import jets
from experiment import Transform
from validation import phi_jacobi
from common import *
from concurrent.futures import ProcessPoolExecutor,as_completed

class Independent:
    def __init__(self,T,U,hden,shift='.2'):
        self.points=[];self.a=[];self.b=[];h=mp.mpf(1)/hden;y=mp.mpf(shift)
        for j in range(int(mp.mpf('3.5')*hden)+1):
            budget();z=j*h+1j*y;ph=phi_jacobi(z);P=mp.mpc(1);Q=mp.mpc(1)
            def poly(T):
                v=mp.mpc(1)
                for i in T.remove:
                    r=T.nodes[i];v*=1+z*z/mp.im(r)**2 if i==1 else (1-z*z/r**2)*(1-z*z/mp.conj(r)**2)
                return v
            aa=h*ph/poly(T)/T.mass;bb=h*ph/poly(U)/U.mass
            self.points.append(z);self.a.append(aa);self.b.append(bb)
            if j:self.points.append(-mp.conj(z));self.a.append(mp.conj(aa));self.b.append(mp.conj(bb))
    def val(self,w,lam):
        out=[mp.mpc(0) for k in range(3)]
        for z,a,b in zip(self.points,self.a,self.b):
            v=((1-lam)*a+lam*b)*mp.exp(1j*w*z)
            for k in range(3):out[k]+=v*(1j*z)**k
        return out

def work(task):
    row,dps=task;start=time.monotonic();r=dict(row=row,dps=dps)
    try:
        hden=128 if dps==100 else 256;T=Transform(row['job']['base'],hden,dps);U=Transform(row['job']['base']+[row['job']['extra']],hden,dps);w=dec(row['fold']['w'])
        for k in range(12):
            a=jets(T,w);b=jets(U,w);W=a[0]*b[1]-a[1]*b[0];D=a[0]*b[2]-a[2]*b[0];step=W/D;w-=step
            if abs(step)<mp.mpf(10)**(-dps+45):break
        a=jets(T,w);b=jets(U,w);lam=mp.re(-a[0]/(b[0]-a[0]));curv=(1-lam)*a[2]+lam*b[2];gain=mp.re(-2*(b[0]-a[0])/curv);ind=Independent(T,U,hden);v=ind.val(w,lam)
        r.update(w=enc(w),lambda_value=str(lam),gain=str(gain),independent_fold_F=str(abs(v[0])),independent_fold_D=str(abs(v[1])),independent_curvature=enc(v[2]),independent_mass_check=str(abs(ind.val(0,lam)[0]-1)))
        branches=[];delta=min(mp.mpf('.01'),lam/4,(1-lam)/4)
        for side in [-1,1]:
            ll=lam+side*delta
            for sign in [-1,1]:
                x=w+sign*mp.sqrt(mp.mpc(gain*side*delta))
                for k in range(30):
                    a=jets(T,x);b=jets(U,x);f=(1-ll)*a[0]+ll*b[0];d=(1-ll)*a[1]+ll*b[1];step=f/d;x-=step
                    if abs(step)<mp.mpf(10)**(-dps+45):break
                iv=ind.val(x,ll);branches.append(dict(lambda_value=str(ll),root=enc(x),independent_residual=str(abs(iv[0])),inferred_root_error=str(abs(iv[0]/iv[1])),correction=str(abs(step))))
        r.update(status='ok',branches=branches)
    except Exception as e:r.update(status='error',error=repr(e))
    r['seconds']=time.monotonic()-start;save('check-%d-%d.json'%(row['id'],dps),r);return r
if __name__=='__main__':
    tasks=[(r,d) for r in json.loads(Path('jobs.json').read_text()) for d in [100,160]];rows=[];start=time.monotonic()
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,t) for t in tasks]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(tasks),rows=rows,seconds=time.monotonic()-start));print(r['row']['id'],r['dps'],r['status'],flush=True)
