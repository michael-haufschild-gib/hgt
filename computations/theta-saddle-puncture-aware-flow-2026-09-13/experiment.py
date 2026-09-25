from discovery import *
import discovery as d

def flow(z,w,direction,side):
    v,nn,lg=fast(z);hess=-(v[2]/v[0]-(v[1]/v[0])**2);axis=np.sqrt(1/hess)*(1 if direction==1 else 1j);axis/=abs(axis);p=z+side*1e-5*axis
    s0=-fast(p)[2]+1j*w*p;pts=[p];arc=0.;h=.008;reject=0;reason='step budget';cross=[]
    def rhs(pp):
        a,n,l=fast(pp);g=np.conj(-a[1]/a[0]+1j*w);return direction*g/max(abs(g),1e-30)
    def rk(pp,hh):
        k1=rhs(pp);k2=rhs(pp+hh*k1/2);k3=rhs(pp+hh*k2/2);k4=rhs(pp+hh*k3);return pp+hh*(k1+2*k2+2*k3+k4)/6
    for it in range(2000):
        budget();v,n,l=fast(p);distance=abs(v[0]/v[1]) if abs(v[1])>0 else np.inf;boundary=min(2.5-abs(p.real),.78-abs(p.imag));g=-v[1]/v[0]+1j*w
        if distance<1e-5:reason='source_zero_approach';break
        if boundary<1e-5:reason='boundary_approach';break
        if abs(g)<1e-8:reason='critical_approach';break
        if arc>=4:reason='arc_cap';break
        hh=min(h,.2*distance,.4*boundary,4-arc)
        q=rk(p,hh);half=rk(rk(p,hh/2),hh/2);err=abs(half-q)
        if err>1e-8*max(1,abs(p)):
            h=hh/2;reject+=1
            if reject>1000:reason='rejection_cap';break
            continue
        if p.imag*half.imag<0:
            frac=-p.imag/(half.imag-p.imag);cr=p+frac*(half-p);cross.append([cr.real,0.])
        p=half;pts.append(p);arc+=hh
        h=min(.008,hh*1.5) if err<1e-9 else hh
    phases=[]
    for pp in pts:
        ss=-fast(pp)[2]+1j*w*pp;phases.append(abs(np.angle(np.exp(1j*(ss-s0).imag))))
    return dict(direction=direction,side=side,status='bounded',reason=reason,endpoint=[p.real,p.imag],arc=arc,steps=len(pts)-1,rejected=reject,newton_source_distance=float(distance),boundary_distance=float(boundary),real_crossings=cross,max_wrapped_phase_drift=max(phases),path=[[pp.real,pp.imag] for pp in pts])
d.flow=flow
if __name__=='__main__':
    mp.mp.dps=70;zz=zeros();jobs=[]
    for n in [1,2,3,5,8,13]:
        t=mp.im(zz[n]);jobs.append(('zero_%02d'%n,[str(t),'0']));jobs.append(('mid_%02d'%n,[str((t+mp.im(zz[n+1]))/2),'0']))
    for n in [1,13]:
        for a in ['-.25','.25']:jobs.append(('tilt_%02d_%s'%(n,a),[str(mp.im(zz[n])),a]))
    save('parameters.json',dict(jobs=jobs));rows=[];start=time.monotonic()
    with ProcessPoolExecutor(max_workers=14) as ex:
        pilots=list(ex.map(d.work,jobs[:2]));rows.extend(pilots);save('pilot.json',dict(rows=pilots,seconds=time.monotonic()-start))
        for f in as_completed([ex.submit(d.work,j) for j in jobs[2:]]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['label'],r['status'],len(r['roots']),flush=True)
