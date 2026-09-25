from experiment import Transform
from common import *
from concurrent.futures import ProcessPoolExecutor,as_completed

def phi_jacobi(z):
    E=mp.exp(2*z);Q=mp.exp(-mp.pi*E)
    return mp.exp(z/2)*(mp.pi**2*E**2*mp.jtheta(3,0,Q,derivative=4)/8+3*mp.pi*E*mp.jtheta(3,0,Q,derivative=2)/4)

def independent(w,remove,hden,mass,shift):
    h=mp.mpf(1)/hden;y=mp.mpf(shift);nodes=[dec(z) for z in json.loads(Path('nodes.json').read_text())];F=mp.mpc(0)
    # Independent Jacobi source, shifted integration contour, no reuse of cosine recurrence.
    for j in range(int(mp.mpf('3.5')*hden)+1):
        budget();x=j*h;z=x+1j*y;P=mp.mpc(1)
        for i in remove:
            q=nodes[i];P*=1+z*z/mp.im(q)**2 if i==1 else (1-z*z/q**2)*(1-z*z/mp.conj(q)**2)
        g=phi_jacobi(z)/P
        term=g*mp.exp(1j*w*z)
        if j:term+=mp.conj(g)*mp.exp(1j*w*(-x+1j*y))
        F+=h*term
    return F/mass

def work(job):
    row,dps=job;start=time.monotonic();r=dict(row=row,dps=dps)
    try:
        hden=128 if dps==100 else 256;T=Transform(row['job']['remove'],hden,dps);w=dec(row['root'])
        for k in range(12):
            v,d=T.val(w);step=v/d;w-=step
            if abs(step)<mp.mpf(10)**(-dps+20):break
        v,d=T.val(w);r.update(root=enc(w),residual=str(abs(v)),correction=str(abs(v/d)),derivative=enc(d),iterations=k+1,real_grid=hden)
        checks=[]
        for shift in ['.2','-.15']:
            vi=independent(w,row['job']['remove'],hden,T.mass,shift)
            checks.append(dict(shift=shift,normalized_residual=str(abs(vi)),inferred_root_error=str(abs(vi/d))))
        r['independent_checks']=checks
        # Numerical winding around root: stronger than small residual alone, still not interval proof.
        radius=mp.mpf('.01');winds=[]
        for count in [24,48]:
            values=[T.val(w+radius*mp.exp(2j*mp.pi*j/count),False) for j in range(count)]
            phases=[mp.arg(values[(j+1)%count]/values[j]) for j in range(count)]
            winds.append(dict(samples=count,winding=str(mp.fsum(phases)/(2*mp.pi)),max_phase_step=str(max(map(abs,phases)))))
        r.update(status='ok',winding=winds)
    except Exception as e:r.update(status='error',error=repr(e))
    r['seconds']=time.monotonic()-start;save('check-%d-%d.json'%(row['id'],dps),r);return r
if __name__=='__main__':
    jobs=[(row,dps) for row in json.loads(Path('validation-jobs.json').read_text()) for dps in [100,160]];out=[];start=time.monotonic()
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,j) for j in jobs]):
            r=f.result();out.append(r);save('summary.json',dict(planned=len(jobs),rows=out,seconds=time.monotonic()-start));print(r['row']['id'],r['dps'],r['status'],flush=True)
