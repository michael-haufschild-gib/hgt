"""Frozen K-test. Numerical mathematics runs only on the authorized Runpod."""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '4'
os.environ['OMP_NUM_THREADS'] = '4'
import sys, pathlib, json, time, concurrent.futures
import numpy as np
import mpmath as mp
ROOT = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent/'chronological-arithmetic-averaging-20260906'))
import kernel_reference as ex


def one_case(N):
    started = time.time()
    mp.mp.dps = 100
    M = N//2
    mu = ex.mobius(N)[1:]
    powers = [-1, 0] + list(range(1, 16, 2))
    xs = [mp.mpf(k)/N for k in range(1, N+1)]
    # High precision matrices formed before any conversion to binary64.
    columns = {p: [x**p for x in xs] for p in powers}
    gram = {(p,q): mp.fsum(columns[p][k]*columns[q][k] for k in range(M,N))
            for p in powers for q in powers if q >= p}
    head = {p: mp.fsum(int(mu[k])*columns[p][k] for k in range(M)) for p in powers}
    targets = {-1: mp.mpf(0), 0: mp.mpf(-2)}
    for j in range(1,9):
        targets[2*j-1] = -2*j/mp.bernoulli(2*j)/mp.mpf(N)**(2*j-1)
    vectors, records = [], []
    for m in range(9):
        ps = powers[:m+2]
        G = mp.matrix([[gram[min(p,q), max(p,q)] for q in ps] for p in ps])
        rhs = mp.matrix([targets[p]-head[p] for p in ps])
        c = mp.lu_solve(G, rhs)
        tail = [mp.fsum(c[i]*columns[p][k] for i,p in enumerate(ps)) for k in range(M,N)]
        ah = [mp.mpf(int(z)) for z in mu[:M]] + tail
        defect = max(abs(mp.fsum(ah[k]*columns[p][k] for k in range(N))-targets[p]) for p in ps)
        a = np.array([float(z) for z in ah])
        float_defect = max(abs(mp.fsum(mp.mpf(float(a[k]))*columns[p][k] for k in range(N))-targets[p]) for p in ps)
        vectors.append(a)
        records.append({'N':N,'M':M,'m':m,'powers':ps,
            'tail_basis_coefficients_mp100':[mp.nstr(z,102) for z in c],
            'max_abs_coefficient':float(np.max(np.abs(a))),
            'tail_max_abs_coefficient':float(np.max(np.abs(a[M:]))),
            'tail_coefficient_l2':float(np.linalg.norm(a[M:])),
            'mp100_scaled_moment_defect':mp.nstr(defect,8),
            'float_scaled_moment_defect':float(float_defect),
            'head_exact':bool(np.array_equal(a[:M],mu[:M]))})
    coeff = np.column_stack(vectors)
    A,e,_,delta = ex.design(N,24)
    train = A@coeff+e[:,None]
    del A
    V,v,t,_ = ex.design(N,60,True)
    residual = V@coeff+v[:,None]
    del V
    for j,row in enumerate(records):
        a = vectors[j]
        r = residual[:,j]
        regions = [t<1/N, (t>=1/N)&(t<1/M), (t>=1/M)&(t<1), t>=1]
        row.update({'norm':float(np.linalg.norm(r)),
            'training_norm':float(np.linalg.norm(train[:,j])),
            'region_energies_t_lt_1N__to_1M__to_1__above_1':[float(r[z]@r[z]) for z in regions],
            'left_tail_energy_bound':float(delta*(1+row['max_abs_coefficient']*N)**2),
            'harmonic_tail_energy':float(r[-1]**2)})
        diffs=[]
        for u in [mp.mpf('0.01'),mp.mpf(1),mp.mpf(10),mp.mpf(100)]:
            tt=u/N
            rr=mp.exp(-tt)+mp.fsum(mp.mpf(float(a[k-1]))*(1/(k*tt)-1/mp.expm1(k*tt)) for k in range(1,N+1))
            rf=np.exp(-float(tt))+ex.bose_h(float(tt)*np.arange(1,N+1))@a
            diffs.append(float(abs(rr-float(rf))))
        row['mp100_residual_spots']=4
        row['max_mp100_residual_difference']=max(diffs)
        np.savetxt(ROOT/('coeff_%d_%d.csv'%(N,j)),np.column_stack([np.arange(1,N+1),mu,a]),
            delimiter=',',header='k,mu,a',comments='',fmt=['%d','%d','%.17g'])
        print(json.dumps({k:row[k] for k in ['N','m','norm','max_abs_coefficient',
            'mp100_scaled_moment_defect','max_mp100_residual_difference']}),flush=True)
    np.savez_compressed(ROOT/('vectors_%d.npz'%N),a=coeff,t=t,residual=residual)
    out={'N':N,'precision':100,'results':records,'seconds':time.time()-started,
         'status':'exploratory_not_certified'}
    (ROOT/('results_%d.json'%N)).write_text(json.dumps(out,indent=2))
    return out


if __name__=='__main__':
    start=time.time()
    with concurrent.futures.ProcessPoolExecutor(max_workers=3) as pool:
        results=list(pool.map(one_case,[512,2048,8192]))
    (ROOT/'results.json').write_text(json.dumps({'cases':results,'seconds':time.time()-start},indent=2))
    print(json.dumps({'event':'complete','seconds':time.time()-start}),flush=True)
