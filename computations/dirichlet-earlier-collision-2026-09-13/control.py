import json
import multiprocessing as mp
import os
import time
from pathlib import Path
import mpmath as m
import deformation as d

CURRENT_Q=4
CHARS={4:[0,1,0,-1],5:[0,1,-1,-1,1]}

def completed(s,q,derivatives=True):
    chi=CHARS[q];parity=1 if q==4 else 0
    lq=m.log(q);sums=[m.mpc(0) for _ in range(3)]
    for r in range(1,q):
        if not chi[r]:continue
        zz=m.zeta(s,m.mpf(r)/q)
        sums[0]+=chi[r]*zz
        if derivatives:
            dz=m.zeta(s,m.mpf(r)/q,derivative=1)
            ddz=m.zeta(s,m.mpf(r)/q,derivative=2)
            sums[1]+=chi[r]*(dz-lq*zz)
            sums[2]+=chi[r]*(ddz-2*lq*dz+lq*lq*zz)
    L,L1,L2=[m.exp(-s*lq)*v for v in sums]
    pref=m.exp((s+parity)/2*m.log(m.mpf(q)/m.pi)+m.loggamma((s+parity)/2))
    if not derivatives:return pref*L
    ld=(m.log(m.mpf(q)/m.pi)+m.digamma((s+parity)/2))/2
    ldd=m.polygamma(1,(s+parity)/2)/4
    return pref*L,pref*(L1+ld*L),pref*(L2+2*ld*L1+(ld*ld+ldd)*L)

def carrier_jets(t):
    z,z1,z2=completed(m.mpf('.5')+m.j*t,CURRENT_Q)
    return m.re(z),m.re(m.j*z1),m.re(-z2)

def prepare_control(q):
    global CURRENT_Q
    CURRENT_Q=q;d.xi_jets=carrier_jets;m.mp.dps=70
    chi=CHARS[q];parity=1 if q==4 else 0
    assert all(chi[(a*b)%q]==chi[a]*chi[b] for a in range(q) for b in range(q))
    gauss=sum(chi[r]*m.exp(2*m.pi*m.j*r/q) for r in range(q))
    root_number=gauss/(m.j**parity*m.sqrt(q))
    checks=[]
    for s in [m.mpc('.37','2.1'),m.mpc('.8','6.3')]:
        f=completed(s,q,False);g=completed(1-s,q,False)
        checks.append(m.nstr(abs(f-g)/max(abs(f),abs(g)),30))
    assert abs(root_number-1)<m.mpf('1e-60') and max(map(m.mpf,checks))<m.mpf('1e-60')
    params=d.prepare(70)
    params['search_window_upper']='55'
    def real(t):
        s=m.mpf('.5')+m.j*t
        return m.re(completed(s,q,False))*m.exp(m.pi*t/4)
    found=[];last=m.mpf(0);flast=real(last)
    for j in range(1,181):
        t=m.mpf(j)/4;ft=real(t)
        if ft*flast<0:
            root=m.findroot(real,(last,t),solver='anderson',tol=m.mpf('1e-55'),verify=True)
            if not found or abs(root-found[-1])>m.mpf('1e-20'):found.append(root)
        last=t;flast=ft
        if len(found)>=5:break
    assert len(found)>=5
    zeros={i+1:m.nstr(z,70) for i,z in enumerate(found)}
    return dict(q=q,parity=parity,character=chi,root_number=[m.nstr(root_number.real,70),m.nstr(root_number.imag,70)],
                functional_equation_relative_errors=checks,parameters=params,located_roots=zeros)

def task(args):
    global CURRENT_Q
    control,n,direction,interaction=args
    CURRENT_Q=control['q'];d.xi_jets=carrier_jets;d.ZEROS={int(k):v for k,v in control['located_roots'].items()}
    row=d.task((n,direction,interaction,control['parameters']));row['q']=CURRENT_Q
    return row

if __name__=='__main__':
    started=time.monotonic()
    controls=[prepare_control(q) for q in [4,5]]
    Path('controls.json').write_text(json.dumps(controls,indent=2)+'\n')
    print('controls verified and roots located',time.monotonic()-started,flush=True)
    directions=[(1,0),(-1,0),(0,1),(0,-1),(1,1),(1,-1),(-1,1),(-1,-1)]
    configurations=[(v,i) for v in directions for i in ([0,1] if v[0]*v[1] else [0])]
    with open('raw.jsonl','w',buffering=1) as out,mp.Pool(14) as pool:
        for indices in [[1],range(2,5)]:
            jobs=[(c,n,v,i) for c in controls for n in indices for v,i in configurations]
            duration=[]
            for row in pool.imap_unordered(task,jobs):
                out.write(json.dumps(row)+'\n');duration.append(row['seconds'])
            print('stage completed',time.monotonic()-started,flush=True)
            if indices==[1] and 3*sum(duration)/14>float(os.environ['CAMPAIGN_DEADLINE'])-time.monotonic():
                print('pilot rejects remaining scan',flush=True);break
