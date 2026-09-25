from source import *
from zeta_independent import em
from concurrent.futures import ProcessPoolExecutor,as_completed

def independent(z):
    budget();E=mp.exp(2*z);Q=mp.exp(-mp.pi*E)
    return mp.exp(z/2)*(mp.pi**2*E**2*mp.jtheta(3,0,Q,derivative=4)/8+3*mp.pi*E*mp.jtheta(3,0,Q,derivative=2)/4)

def work(job):
    idx,dps=job;mp.mp.dps=dps;start=time.monotonic();r=dict(index=idx,dps=dps)
    try:
        z=dec(json.loads(Path('seeds.json').read_text())[idx]['point'])
        for _ in range(9):
            v,nn,N,e=jets(z,3);z-=(v[0]*v[2]-v[1]**2)/(v[0]*v[3]-v[1]*v[2])
        v,nn,N,e=jets(z,3,extra=30);w=-1j*v[1]/v[0];r.update(point=enc(z),frequency=enc(w),source_value=enc(v[0]*mp.exp(e)))
        mp.mp.dps=dps+50;vv=[mp.diff(independent,z,k) for k in range(4)];Q=vv[0]*vv[2]-vv[1]**2;Qp=vv[0]*vv[3]-vv[1]*vv[2];wi=-1j*vv[1]/vv[0]
        r.update(normalized_independent_degeneracy_residual=str(abs(Q)/(abs(vv[0]*vv[2])+abs(vv[1])**2)),independent_newton_correction=str(abs(Q/Qp)),frequency_disagreement=str(abs(wi-w)),independent_nondegeneracy=enc(-1j*Qp/vv[0]**2),jet_relative_disagreements=[str(abs(vv[k]-v[k]*mp.exp(e))/max(1,abs(vv[k]))) for k in range(4)])
        s=mp.mpf('.5')+1j*w;N=max(100,int(abs(mp.im(s)))+80);a=em(s,N,dps+25);bb=em(s,N+40,dps+45);factor=s*(s-1)/2*mp.exp(-s/2*mp.log(mp.pi)+mp.loggamma(s/2));xi=factor*bb
        r.update(spectral_point=enc(s),xi_value=enc(xi),xi_magnitude=str(abs(xi)),xi_truncation_disagreement=str(abs(factor*(a-bb))),xi_native_disagreement=str(abs(factor*(bb-mp.zeta(s)))),status='ok')
    except Exception as ex:r.update(status='error',error=repr(ex))
    r['seconds']=time.monotonic()-start;save('check-%d-%d.json'%(idx,dps),r);return r
if __name__=='__main__':
    jobs=[(k,dps) for k in range(4) for dps in [100,160]];rows=[];start=time.monotonic()
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,j) for j in jobs]):
            r=f.result();rows.append(r);save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start));print(r['index'],r['dps'],r['status'],flush=True)
