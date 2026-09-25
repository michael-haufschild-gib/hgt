from source import *
from concurrent.futures import ProcessPoolExecutor,as_completed

def independent(z):
    # Theta derivatives are with respect to the Jacobi argument, not its nome.
    budget();E=mp.exp(2*z);Q=mp.exp(-mp.pi*E)
    return mp.exp(z/2)*(mp.pi**2*E**2*mp.jtheta(3,0,Q,derivative=4)/8+3*mp.pi*E*mp.jtheta(3,0,Q,derivative=2)/4)

def work(job):
    idx,dps=job;mp.mp.dps=dps;start=time.monotonic();r=dict(index=idx,dps=dps)
    try:
        seeds=json.loads(Path('distinct-roots.json').read_text());z=dec(seeds[idx]['root'])
        for _ in range(9):
            v,nn,N,e=jets(z);z-=v[0]/v[1]
        v,nn,N,e=jets(z,extra=30);r.update(root=enc(z),terms=N,normalized_residual=str(abs(v[0])/nn),normalized_derivative=str(abs(v[1])/nn))
        mp.mp.dps=dps+50;sym=[]
        for label,sp in [('original',z),('negative',-z),('conjugate',mp.conj(z)),('negative_conjugate',-mp.conj(z))]:
            vv,n2,N2,ee=jets(sp,extra=30);value=independent(sp);scale=n2*mp.exp(mp.re(ee));sym.append(dict(label=label,normalized_independent_residual=str(abs(value)/scale),normalized_formula_disagreement=str(abs(value-vv[0]*mp.exp(ee))/scale)))
        r['independent_symmetry_checks']=sym
        radius=min(mp.mpf('.005'),(mp.pi/4-abs(mp.im(z)))/4,min(abs(z-dec(q['root']))/6 for j,q in enumerate(seeds) if j!=idx));r['winding_radius']=str(radius);winds=[]
        for count in [32,64,128]:
            mp.mp.dps=dps;vals=[]
            for j in range(count):
                pp=z+radius*mp.exp(2j*mp.pi*j/count);vv,n3,N3,ee=jets(pp);vals.append(vv[0]*mp.exp(ee))
            diffs=[mp.arg(vals[(j+1)%count]/vals[j]) for j in range(count)]
            winds.append(dict(samples=count,winding=str(mp.fsum(diffs)/(2*mp.pi)),max_phase_step=str(max(map(abs,diffs))),minimum_abs_value=str(min(map(abs,vals)))))
        r.update(status='ok',winding_checks=winds)
    except Exception as e:r.update(status='error',error=repr(e))
    r['seconds']=time.monotonic()-start;save('check-%d-%d.json'%(idx,dps),r);return r
if __name__=='__main__':
    seeds=json.loads(Path('distinct-roots.json').read_text());jobs=[(i,dps) for i in range(len(seeds)) for dps in [100,160]];rows=[];start=time.monotonic()
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,j) for j in jobs]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['index'],r['dps'],r['status'],flush=True)
