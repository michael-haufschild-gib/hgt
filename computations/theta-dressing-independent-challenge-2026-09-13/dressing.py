from source import *
from concurrent.futures import ProcessPoolExecutor,as_completed

def dress(p,alpha,z,kind='full',order=1,extra=0):
    L=mp.log(p);r=mp.exp(-alpha*L);y=mp.im(z)
    if abs(y)>=mp.pi/4:raise ArithmeticError('source strip')
    C=mp.log((mp.mp.dps+90)*mp.log(10)/(mp.pi*mp.cos(2*y)))/2+2
    lo=int(mp.floor((-C-mp.re(z))/L))-1-extra;hi=int(mp.ceil((C-mp.re(z))/L))+1+extra
    vals=[mp.mpc(0) for _ in range(order+1)];norm=mp.mpf(0)
    scale=alpha*mp.re(z) if kind=='full' else 0
    for k in range(lo,hi+1):
        v,n,e,N=raw_jets('R',z+k*L,order,True)
        a=(-alpha*L*abs(k) if kind=='full' else alpha*L*k)+scale
        fac=mp.exp(e+a)
        for j in range(order+1):vals[j]+=fac*v[j]
        norm+=abs(fac)*n
    return vals,norm,dict(shift_lo=lo,shift_hi=hi,rescale=str(scale))

def refine(p,a,z,kind,steps=42):
    L=mp.log(p);tol=mp.mpf('1e-30')
    for it in range(steps):
        vv,n,meta=dress(p,a,z,kind);ds=vv[0]/vv[1]
        if abs(ds)<tol and abs(vv[0])/n<tol:return z,dict(correction=str(abs(ds)),normalized_residual=str(abs(vv[0])/n),iterations=it,**meta)
        if abs(ds)>.16:ds*=mp.mpf('.16')/abs(ds)
        nx=z-ds
        if abs(mp.im(nx))>=mp.pi/4: nx=z-ds/2
        z=nx
        if kind=='tail':z-=mp.floor(mp.re(z)/L)*L
        if abs(mp.im(z))>=mp.pi/4 or abs(mp.im(z))<mp.mpf('.00001') or (kind=='full' and abs(mp.re(z))>3):raise ArithmeticError('root domain escape')
    raise ArithmeticError('root iteration limit')

def work(job):
    start=time.monotonic();mp.mp.dps=60;p=mp.mpf(job['p']);a=mp.mpf(job['alpha']);kind=job['kind'];L=mp.log(p);roots=[];failed=[]
    try:
        for xr in ['.04','.2','.38','.56','.74','.94']:
            for yy in ['.2','.4','.55','.65','.72','.76','.78','.784']:
                z=mp.mpf(xr)*(L if kind=='tail' else mp.mpf('2.5'))+1j*mp.mpf(yy)
                try:
                    budget();w,d=refine(p,a,z,kind)
                    if mp.im(w)<0:w=mp.conj(w)
                    if kind=='full' and mp.re(w)<0:w=-mp.conj(w)
                    if not any(abs(w-dec(v['root']))<mp.mpf('1e-18') for v in roots):roots.append(dict(root=enc(w),**d))
                except Exception as e:failed.append(dict(start=enc(z),error=repr(e)))
        roots.sort(key=lambda v:float(v['root'][1]));translated=[]
        if kind=='tail' and roots:
            w=dec(roots[0]['root'])
            for m in [8,16]:
                zz=w+m*L
                try:
                    for it in range(10):
                        vv,n,meta=dress(p,a,zz,'full');ds=vv[0]/vv[1];zz-=ds
                        if abs(ds)<mp.mpf('1e-30'):break
                    translated.append(dict(m=m,root=enc(zz),correction=str(abs(ds)),relative_to_tail=enc(zz-m*L-w),normalized_residual=str(abs(vv[0])/n)))
                except Exception as e:translated.append(dict(m=m,error=repr(e)))
        r=dict(job=job,status='ok',roots=roots,failed_starts=failed,translated=translated)
    except Exception as e:r=dict(job=job,status='error',error=repr(e),roots=roots,failed_starts=failed)
    r['seconds']=time.monotonic()-start;save('case-'+job['label']+'.json',r);return r
if __name__=='__main__':
    start=time.monotonic();mp.mp.dps=60;z=mp.mpc('.3','.4');p=mp.mpf(2);a=mp.mpf('.5');L=mp.log(p);r=p**(-a)
    def physical(zz):return dress(p,a,zz,'full',0)[0][0]*mp.exp(-a*mp.re(zz))
    v=physical(z);rec=(1+r*r)*v-r*(physical(z+L)+physical(z-L));err=abs(rec-(1-r*r)*phi('R',z))/abs(phi('R',z));assert err<mp.mpf('1e-48')
    H=dress(p,a,z,'tail',0)[0][0];Hs=dress(p,a,z+L,'tail',0)[0][0];qe=abs(Hs-r*H)/abs(H);assert qe<mp.mpf('1e-48')
    pilot=[]
    for yy in ['.65','.76','.784']:
        try:w,d=refine(p,a,L/2+1j*mp.mpf(yy),'tail');pilot.append(dict(root=enc(w),**d))
        except Exception as e:pilot.append(dict(error=repr(e)))
    save('pilot.json',dict(seconds=time.monotonic()-start,recurrence_error=str(err),quasiperiod_error=str(qe),roots=pilot))
    jobs=[dict(p=p,alpha=a,kind=k,label=p+'-'+a+'-'+k) for p in ['2','3','5','7','4','6','2.5'] for a in ['.5','1'] for k in ['full','tail']];save('jobs.json',jobs);rows=[]
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,j) for j in jobs]):
            x=f.result();rows.append(x);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(x['job']['label'],x['status'],len(x['roots']),flush=True)
