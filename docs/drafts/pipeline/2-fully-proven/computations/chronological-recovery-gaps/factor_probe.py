"""Factor-coordinate minimax/moment exploration. Run only on authorized Runpod."""
import os
for name in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[name]='1'
import json
from concurrent.futures import ProcessPoolExecutor, as_completed
import numpy as np
import mpmath as mp


def valid(z):
    m=len(z)//2
    d,c=z[:m],z[m:]
    return c[0]>0 and d[-1]<1 and all(c[i]<d[i] for i in range(m)) and all(d[i]<c[i+1] for i in range(m-1))


def system_np(z):
    m=len(z)//2
    d,c=z[:m],z[m:]
    a=c[:,None]-d[None,:]
    b=2-c[:,None]-d[None,:]
    f=np.log(c)+np.sum(np.log(np.abs(a))+np.log(b)-2*np.log(1-d)[None,:],axis=1)/m
    v=1/c+np.sum(1/a-1/b,axis=1)/m
    jac=np.zeros((2*m,2*m))
    jac[:m,:m]=(-1/a-1/b+2/(1-d)[None,:])/m
    jac[:m,m:]=np.diag(v)
    jac[m:,:m]=(1/a**2-1/b**2)/m
    jac[m:,m:]=np.diag(-1/c**2-np.sum(1/a**2+1/b**2,axis=1)/m)
    return np.r_[f,v],jac


def system_mp(z):
    m=len(z)//2
    d,c=list(z[:m]),list(z[m:])
    f=mp.matrix(2*m,1)
    jac=mp.matrix(2*m,2*m)
    for i in range(m):
        a=[c[i]-v for v in d]
        b=[2-c[i]-v for v in d]
        f[i]=mp.log(c[i])+mp.fsum(mp.log(abs(a[j]))+mp.log(b[j])-2*mp.log(1-d[j]) for j in range(m))/m
        f[m+i]=1/c[i]+mp.fsum(1/a[j]-1/b[j] for j in range(m))/m
        for j in range(m):
            jac[i,j]=(-1/a[j]-1/b[j]+2/(1-d[j]))/m
            jac[m+i,j]=(1/a[j]**2-1/b[j]**2)/m
        jac[i,m+i]=f[m+i]
        jac[m+i,m+i]=-1/c[i]**2-mp.fsum(1/a[j]**2+1/b[j]**2 for j in range(m))/m
    return f,jac


def one(job):
    m,seed=job
    z=np.array(seed)
    success=False
    for step in range(100):
        f,jac=system_np(z)
        err=np.max(np.abs(f))
        if err<2e-10:
            success=True
            break
        dz=np.linalg.solve(jac,-f)
        length=1.
        while length>2.**-35:
            zz=z+length*dz
            if valid(zz) and np.max(np.abs(system_np(zz)[0])) < err:
                z=zz
                break
            length*=.5
        else:
            return {'m':m,'error':'double line search stalled','residual':float(err)}
    if not success:
        return {'m':m,'error':'double iteration limit','residual':float(err)}
    mp.mp.dps=110
    zz=mp.matrix([mp.mpf(str(v)) for v in z])
    for step in range(12):
        f,jac=system_mp(zz)
        if max(abs(v) for v in f)<mp.mpf('1e-85'):
            break
        zz+=mp.lu_solve(jac,-f)
    f,_=system_mp(zz)
    err=max(abs(v) for v in f)
    if not valid(list(zz)) or err>=mp.mpf('1e-80'):
        return {'m':m,'error':'high precision check failed','residual':str(err)}
    d=list(zz[:m]); c=list(zz[m:])
    sx=mp.fsum(v*(2-v) for v in d)
    delta=mp.power(4,1-m)*mp.fprod((1-v)**2 for v in d)/sx
    return {'m':m,'delta':str(delta),'root_c':[str(v) for v in d],
            'contacts':[str(v) for v in c], 'residual':str(err),'root_mean_r':str(sx/(4*m))}


def seeds(count):
    b=.838771399357062327
    s,w=np.polynomial.legendre.leggauss(1024)
    a=(s+1)*b/2; w=w*b/2
    ip=1/(1-a*a)+a*(np.pi/2+np.arcsin(a))/(1-a*a)**1.5
    density_weights=w*ip/np.pi
    t=np.linspace(b,0,6001)
    folded=np.sum((2/np.pi)*np.arcsin(np.minimum(1,t[:,None]/a[None,:]))*density_weights[None,:],axis=1)
    cdf=1-folded; cdf[0]=0; cdf[-1]=1
    cgrid=1-t
    jobs=[]
    for m in range(1,count+1):
        d=np.interp((np.arange(m)+.5)/m,cdf,cgrid)
        c=np.interp((np.arange(m)+.15)/m,cdf,cgrid)
        jobs.append((m,np.r_[d,c].tolist()))
    return jobs


if __name__=='__main__':
    results=[]
    with ProcessPoolExecutor(max_workers=24) as pool:
        futures=[pool.submit(one,j) for j in seeds(32)]
        for f in as_completed(futures):
            r=f.result();results.append(r)
            print('degree',r['m'],r.get('error','converged'),flush=True)
    results.sort(key=lambda r:r['m'])
    mp.mp.dps=100
    with open('refined-results.json') as f: prior=json.load(f)
    theta=mp.findroot(lambda t:2*(mp.pi-t)-3*mp.pi*mp.sin(t),(.5,.7))
    b=mp.cos(theta)
    rho=b*b/16*mp.exp(2*mp.quad(lambda t:mp.log(1-b*mp.cos(t)),[0,mp.pi/2])/mp.pi)
    complete=all('delta' in r for r in results)
    out={'results':results,'complete':complete,'rho':str(rho)}
    if complete:
        gaps=[mp.mpf(r['delta']) for r in results]
        moments=[(g/gaps[0])**2/rho**(2*i) for i,g in enumerate(gaps)]
        rows=[moments]
        while len(rows[-1])>1:
            p=rows[-1];rows.append([p[j]-p[j+1] for j in range(len(p)-1)])
        violations=[{'difference_order':i,'moment_index':j,'value':str(v)}
                    for i,row in enumerate(rows) for j,v in enumerate(row) if v<0]
        out['hausdorff_differences']=[[str(v) for v in row] for row in rows]
        out['hausdorff_violations']=violations
        out['ratios']=[str(gaps[i+1]/gaps[i]) for i in range(len(gaps)-1)]
        out['prior_relative_errors']=[str(abs(gaps[i]/mp.mpf(prior['results'][i]['delta'])-1)) for i in range(8)]
        out['scaled_gaps']=[str((i+1)*g/rho**(i+1)) for i,g in enumerate(gaps)]
        # Leading determinants alone are insufficient; use full PSD spectra
        # for both Stieltjes Hankel forms and the bounded-support localizers.
        tests={}
        for size in (4,8,12,16):
            for shift in (0,1):
                if 2*(size-1)+shift>=len(moments):continue
                mat=mp.matrix([[moments[i+j+shift] for j in range(size)] for i in range(size)])
                tests[f'hankel:{size}:{shift}']=[str(v) for v in mp.eigsy(mat,eigvals_only=True)]
            if 2*(size-1)+1<len(moments):
                mat=mp.matrix([[moments[i+j]-moments[i+j+1] for j in range(size)] for i in range(size)])
                tests[f'endpoint:{size}']=[str(v) for v in mp.eigsy(mat,eigvals_only=True)]
        out['moment_matrix_spectra']=tests
        print('Hausdorff violations:',len(violations),flush=True)
        print('Smallest matrix eigenvalue:',min(mp.mpf(v) for vv in tests.values() for v in vv),flush=True)
    with open('factor-results.json','w') as f:json.dump(out,f,indent=2)
