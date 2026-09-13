import concurrent.futures as cf
from functools import lru_cache
import json,os,time
import numpy as np
from scipy.special import roots_legendre
from scipy.optimize import root
import mpmath as mp

DEADLINE=float(os.environ['CAMPAIGN_DEADLINE'])
def budget():
    if time.monotonic()>DEADLINE-5:raise TimeoutError('family deadline')
def enc(z):return [mp.nstr(mp.re(z),mp.mp.dps),mp.nstr(mp.im(z),mp.mp.dps)]
def cc(z):return mp.mpc(*z)

@lru_cache(None)
def weights(shape,n):
    x,w=roots_legendre(n);u=(x+1)/4;w=w/4
    q=np.exp(shape*(-1/u+1/(1-u)))
    return u-.5,2*w*shape*(1/u**2+1/(1-u)**2)*q/(1+q)**2

def screen_value(z,shape,n=512,derivative=False):
    budget();x,w=weights(shape,n)
    z=np.asarray(z)
    if derivative:return np.sum(np.sinh(z[...,None]*x)*x*w,axis=-1)
    return np.sum(np.cosh(z[...,None]*x)*w,axis=-1)

def points(lo,hi,n):
    c=[.1+1j*lo,3+1j*lo,3+1j*hi,.1+1j*hi]
    return np.array([c[j]+(c[(j+1)%4]-c[j])*k/n for j in range(4) for k in range(n)])

def contour(shape,lo,hi,n,nodes):
    z=points(lo,hi,n);v=screen_value(z,shape,nodes);inc=np.angle(np.roll(v,-1)/v)
    return dict(nodes=nodes,edge_samples=n,winding=float(sum(inc)/(2*np.pi)),
                max_phase=float(max(abs(inc))),minimum=float(min(abs(v))),
                mass_error=float(abs(screen_value(0,shape,nodes)-1)),
                samples=[dict(z=[float(a.real),float(a.imag)],value=[float(b.real),float(b.imag)]) for a,b in zip(z,v)])

def screen(job):
    start=time.monotonic();shape,lo,hi=job
    out=dict(kind='screen',job=job,roots=[],rejected=[],failures=[])
    try:
        a=contour(shape,lo,hi,32,256);b=contour(shape,lo,hi,64,512);out['contours']=[a,b]
        out['matched_error']=max(abs(complex(*x['value'])-complex(*y['value'])) for x,y in zip(a['samples'],b['samples'][::2]))
        if b['winding']>.5 or b['max_phase']>2.9:
            nearest=min(b['samples'],key=lambda r:abs(complex(*r['value'])))
            seeds=[nearest['z']]+[[x,(lo+hi)/2] for x in [.3,1,2.5]]
            def fun(v):
                z=screen_value(complex(*v),shape);return [z.real,z.imag]
            def jac(v):
                d=screen_value(complex(*v),shape,derivative=True);return [[d.real,-d.imag],[d.imag,d.real]]
            for seed in seeds:
                sol=root(fun,seed,jac=jac,tol=1e-10)
                z=complex(*sol.x);res=abs(screen_value(z,shape))
                r=dict(z=[z.real,z.imag],residual=float(res),solver_success=bool(sol.success))
                if sol.success and .1<z.real<3 and .1<z.imag<144 and res<1e-11:
                    if not any(abs(z-complex(*old['z']))<1e-5 for old in out['roots']):out['roots'].append(r)
                else:out['rejected'].append(r)
    except Exception as e:out['error']=str(e)[:250]
    out['seconds']=time.monotonic()-start;return out

def chi(u,shape):
    if u<=0:return mp.mpf(0)
    if u>=1:return mp.mpf(1)
    if u>mp.mpf('.5'):return 1-chi(1-u,shape)
    q=mp.exp(shape*(-1/u+1/(1-u)));return q/(1+q)

def pulse(u,shape):
    if u<=0 or u>=1:return mp.mpf(0)
    q=mp.exp(shape*(-1/u+1/(1-u)))
    return shape*(1/u**2+1/(1-u)**2)*q/(1+q)**2

def G(z,shape,derivative=False):
    budget()
    if derivative:f=lambda u:2*pulse(u,shape)*(u-mp.mpf('.5'))*mp.sinh(z*(u-mp.mpf('.5')))
    else:f=lambda u:2*pulse(u,shape)*mp.cosh(z*(u-mp.mpf('.5')))
    return mp.quad(f,[0,mp.mpf('.125'),mp.mpf('.25'),mp.mpf('.375'),mp.mpf('.5')])

def primitive(z,shape):
    budget()
    v=mp.quad(lambda u:(chi(u,shape)-1)*mp.exp(z*u),[0,mp.mpf('.25'),mp.mpf('.5'),mp.mpf('.75'),1])
    return mp.exp(-z/2)*(1-z*v)

def validate(job):
    start=time.monotonic();shape,seed,isroot=job
    out=dict(kind='validation',shape=shape,seed=seed,isroot=isroot,precision=[])
    try:
        for dps in [50,100,160]:
            mp.mp.dps=dps;z=cc(seed);a=mp.mpf(shape)
            if isroot:z=mp.findroot(lambda x:G(x,a),(z,z+mp.mpf('.001')),tol=mp.power(10,-dps+8),maxsteps=30)
            v=G(z,a);out['precision'].append(dict(dps=dps,z=enc(z),value=enc(v)))
            seed=enc(z)
        mp.mp.dps=190;z=cc(seed);a=mp.mpf(shape)
        ref=primitive(z,a);out['independent']=dict(value=enc(ref),discrepancy=enc(ref-G(z,a)))
        anchor=z+mp.mpf('.01');out['anchor']=dict(z=enc(anchor),value=enc(primitive(anchor,a)),discrepancy=enc(primitive(anchor,a)-G(anchor,a)))
        if isroot:
            out['derivative']=enc(G(z,a,True));mp.mp.dps=70
            vals=[G(z+mp.mpf('.0001')*mp.exp(2j*mp.pi*k/16),a) for k in range(16)]
            out['local_winding']=mp.nstr(sum(mp.arg(vals[(k+1)%16]/vals[k]) for k in range(16))/(2*mp.pi),40)
            if shape==1.0:
                mp.mp.dps=100;out['physical_controls']=[]
                for aa in [z,-z,mp.conj(z),-mp.conj(z)]:
                    for b,s,A,B in [(True,True,'2.5','-3'),(True,False,'1.5','-2'),(False,True,'-1.5','-1'),(False,False,'-2.5','0')]:
                        rho=(aa-mp.mpf(B))/mp.mpf(A)
                        if 0<rho.real<1 and rho.imag>0:
                            exponents=[mp.mpf('2.5')*rho-3,mp.mpf('1.5')*rho-2,-mp.mpf('1.5')*rho-1,-mp.mpf('2.5')*rho]
                            out['physical_controls'].append(dict(branch=b,side=s,rho=enc(rho),centered_onsets=[enc(G(x,a)) for x in exponents]))
    except Exception as e:out['error']=str(e)[:300]
    out['seconds']=time.monotonic()-start;return out

def emit(row):
    with open('results.jsonl','a') as f:f.write(json.dumps(row)+'\n')
    print(json.dumps({k:v for k,v in row.items() if k not in ['contours','precision','physical_controls']}),flush=True)

def main():
    start=time.monotonic();pilot=screen((1.,120.,144.));emit(pilot)
    estimate=pilot['seconds']*18/14;emit(dict(kind='pilot',estimated_screen_seconds=estimate))
    if estimate>150:raise RuntimeError('pilot budget rejected')
    jobs=[(a,lo,hi) for a in [1.,.5,2.] for lo,hi in [(.1,24.),(24.,48.),(48.,72.),(72.,96.),(96.,120.),(120.,144.)] if (a,lo,hi)!=(1.,120.,144.)]
    rows=[pilot]
    with cf.ProcessPoolExecutor(max_workers=14) as pool:
        for f in cf.as_completed([pool.submit(screen,j) for j in jobs]):
            row=f.result();emit(row);rows.append(row)
        candidates=[]
        for r in sorted(rows,key=lambda r:(r['job'][0]!=1,r['job'][0],r['job'][1])):
            for z in r['roots']:
                job=(r['job'][0],list(map(str,z['z'])),True)
                if not any(c[0]==job[0] and abs(complex(*map(float,c[1]))-complex(*z['z']))<1e-5 for c in candidates):candidates.append(job)
        emit(dict(kind='candidate_count',count=len(candidates),validation_cap=6))
        checks=candidates[:6]+[(a,[r,i],False) for a in [1.,.5,2.] for r,i in [('1','13'),('3','144')]]
        for f in cf.as_completed([pool.submit(validate,j) for j in checks]):emit(f.result())
    emit(dict(kind='complete',seconds=time.monotonic()-start))

if __name__=='__main__':main()
