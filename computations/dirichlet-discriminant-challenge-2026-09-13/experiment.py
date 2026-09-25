import json
import multiprocessing as mp
import os
import time
from pathlib import Path
import mpmath as m
import deformation as d
import discriminant as e
import control as c

def pair(t):
    q=c.CURRENT_Q
    s=m.mpf('.5')+m.j*t
    a=1 if q==4 else 0
    lq=m.log(q)
    v=m.mpc(0);dv=m.mpc(0)
    for r in range(1,q):
        chi=c.CHARS[q][r]
        if not chi:continue
        z=m.zeta(s,m.mpf(r)/q)
        v+=chi*z
        dv+=chi*(m.zeta(s,m.mpf(r)/q,derivative=1)-lq*z)
    pref=m.exp((s+a)/2*m.log(m.mpf(q)/m.pi)+m.loggamma((s+a)/2)-s*lq)
    ld=(m.log(m.mpf(q)/m.pi)+m.digamma((s+a)/2))/2
    return m.re(pref*v),m.re(m.j*pref*(dv+ld*v))

def configure(q):
    c.CURRENT_Q=q
    d.xi_jets=c.carrier_jets
    e.pair=pair

def scan(args):
    control,n,interaction=args
    configure(control['q'])
    d.ZEROS={int(k):v for k,v in control['located_roots'].items()}
    row=e.scan((n,(-1,1),interaction,control['parameters']))
    row['q']=control['q']
    return row

def refine(args):
    row,dps,params=args
    configure(row['q'])
    result=e.refine((row,dps,params))
    result['q']=row['q']
    return result

def independent(args):
    item,params,offset=args
    start=time.monotonic();m.mp.dps=190
    q=item['q'];configure(q);parity=1 if q==4 else 0
    t=m.mpf(item['t'])+m.mpf(offset);lam=m.mpf(item['lam'])
    aa=-lam/m.sqrt(2);bb=lam/m.sqrt(2)
    hs=[{int(k):m.mpf(v) for k,v in params[n].items()} for n in ['h1','h2','h12']]
    def source(x):
        y=m.exp(2*x)
        return 2*m.exp((parity+m.mpf('.5'))*x)*sum(c.CHARS[q][n%q]*n**parity*m.exp(-m.pi*n*n*y/q) for n in range(1,41) if c.CHARS[q][n%q])
    def mult(x):
        vals=[sum(v*m.cos(k*x) for k,v in h.items()) for h in hs]
        return 1+aa*vals[0]+bb*vals[1]+item['interaction']*aa*bb*vals[2]
    bounds=[0,m.mpf('.25'),m.mpf('.5'),m.mpf('.75'),1,m.mpf('1.5'),2,3]
    actual=[2*m.quad(lambda x:source(x)*mult(x)*m.cos(t*x),bounds),
            -2*m.quad(lambda x:x*source(x)*mult(x)*m.sin(t*x),bounds)]
    def shifted(h,j):return sum(v*(pair(t+k)[j]+pair(t-k)[j])/2 for k,v in h.items())
    expected=[pair(t)[j]+aa*shifted(hs[0],j)+bb*shifted(hs[1],j)+item['interaction']*aa*bb*shifted(hs[2],j) for j in [0,1]]
    scale=m.exp(-m.pi*t/4)*(1+t*t)**m.mpf('.875')
    return dict(q=q,n=item['n'],interaction=item['interaction'],t=m.nstr(t,190),offset=offset,lam=item['lam'],dps=190,
                scaled_integral=[m.nstr(x/scale,80) for x in actual],
                scaled_formula_errors=[m.nstr(abs(x-y)/scale,80) for x,y in zip(actual,expected)],
                terms=40,cutoff=3,seconds=time.monotonic()-start)

if __name__=='__main__':
    started=time.monotonic()
    controls=json.loads(Path('initial-controls.json').read_text())
    params={}
    for control in controls:
        configure(control['q'])
        params[control['q']]={prec:d.prepare(prec) for prec in [70,120,180]}
        control['parameters']=params[control['q']][70]
    Path('parameters.json').write_text(json.dumps(params,indent=2)+'\n')
    rows=[]
    with mp.Pool(14) as pool,open('scan.jsonl','w',buffering=1) as output:
        for gaps in [[1],[4]]:
            stage=[]
            for row in pool.imap_unordered(scan,[(control,n,i) for control in controls for n in gaps for i in [0,1]]):
                rows.append(row);stage.append(row);output.write(json.dumps(row)+'\n')
            print('scan cells',len(rows),'elapsed',time.monotonic()-started,flush=True)
            if gaps==[1] and max(r['seconds'] for r in stage)*2>float(os.environ['CAMPAIGN_DEADLINE'])-time.monotonic():
                print('pilot rejects remaining scan',flush=True);break
        selected=[dict(q=r['q'],n=r['n'],direction=r['direction'],interaction=r['interaction'],**root)
                  for r in rows for root in r['roots'] if root['positive_lam'] and m.mpf(root['positivity_bound'])<1]
        validated=[]
        with open('validation.jsonl','w',buffering=1) as output2:
            for row in pool.imap_unordered(refine,[(r,dps,params[r['q']][prec]) for r in selected for dps,prec in [(100,120),(160,180)]]):
                output2.write(json.dumps(row)+'\n');validated.append(row)
        print('refined',len(validated),'elapsed',time.monotonic()-started,flush=True)
        with open('source-validation.jsonl','w',buffering=1) as output3:
            for row in pool.imap_unordered(independent,[(r,params[r['q']][180],offset) for r in validated if r['dps']==160 for offset in ['0','.125']]):
                output3.write(json.dumps(row)+'\n')
    Path('summary.json').write_text(json.dumps(dict(seconds=time.monotonic()-started),indent=2)+'\n')
