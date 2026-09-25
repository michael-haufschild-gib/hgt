"""Independent coefficient-coordinate check of a canonical square witness. Runpod only."""
import os
for name in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[name] = '1'
import json
from concurrent.futures import ProcessPoolExecutor, as_completed
import mpmath as mp


def refine(row):
    mp.mp.dps = 230
    m = row['m']
    # Seed monomial coefficients from previously found roots; subsequent
    # equations contain coefficients and contacts, with no factor logarithms.
    coeff = [mp.mpf(1)]
    roots = [mp.mpf(x) for x in row['root_c']]
    for d in roots:
        r = d*(2-d)
        nxt = [mp.mpf(0)]*(len(coeff)+1)
        for j, a in enumerate(coeff):
            nxt[j] -= r*a
            nxt[j+1] += a
        coeff = nxt
    endpoint = mp.fprod((1-d)**2 for d in roots)
    coeff = mp.matrix([x/endpoint for x in coeff])
    contacts = [mp.mpf(x) for x in row['contacts']]

    def evaluate(c):
        x = c*(2-c)
        xp = 2*(1-c)
        powers = [x**j for j in range(m+1)]
        p = mp.fsum(coeff[j]*powers[j] for j in range(m+1))
        dp = mp.fsum(j*coeff[j]*powers[j-1] for j in range(1,m+1))
        ddp = mp.fsum(j*(j-1)*coeff[j]*powers[j-2] for j in range(2,m+1))
        val = c**m*p
        der = m*c**(m-1)*p + c**m*xp*dp
        second = m*(m-1)*c**(m-2)*p + 2*m*c**(m-1)*xp*dp + c**m*(xp*xp*ddp-2*dp)
        basis = [c**m*t for t in powers]
        dbasis = [m*c**(m-1)*powers[j] + (c**m*xp*j*powers[j-1] if j else 0)
                  for j in range(m+1)]
        return val, der, second, basis, dbasis

    for iteration in range(8):
        vals = [evaluate(c) for c in contacts]
        f = [v[0]-(-1)**(m-i) for i,v in enumerate(vals)]
        f.append(mp.fsum(coeff)-1)
        err = max([abs(v) for v in f] + [abs(v[1]) for v in vals])
        if err < mp.mpf('1e-180'):
            break
        mat = mp.matrix(m+1,m+1)
        rhs = mp.matrix(m+1,1)
        for i,v in enumerate(vals):
            ratio = v[1]/v[2]
            for j in range(m+1):
                mat[i,j] = v[3][j]-ratio*v[4][j]
            rhs[i] = -f[i]+ratio*v[1]
        for j in range(m+1):
            mat[m,j] = 1
        rhs[m] = -f[m]
        da = mp.lu_solve(mat,rhs)
        dc = [(-v[1]-mp.fsum(v[4][j]*da[j] for j in range(m+1)))/v[2] for v in vals]
        coeff += da
        contacts = [c+d for c,d in zip(contacts,dc)]
    if err >= mp.mpf('1e-180'):
        return {'m':m,'error':'coefficient refinement failed','residual':str(err)}
    delta = 1/(mp.power(4,m-1)*abs(coeff[m-1]))
    return {'m':m,'delta':str(delta),'equation_residual':str(err),
            'relative_disagreement':str(abs(delta/mp.mpf(row['delta'])-1)),
            'coefficients_x':list(map(str,coeff)), 'contacts':list(map(str,contacts))}


if __name__ == '__main__':
    old = json.load(open('extension-results.json'))
    results = []
    with ProcessPoolExecutor(max_workers=24) as pool:
        for future in as_completed([pool.submit(refine,row) for row in old['results'][:35]]):
            row = future.result()
            results.append(row)
            print('degree',row['m'],row.get('error','verified in coefficient coordinates'),flush=True)
    results.sort(key=lambda r:r['m'])
    out = {'results':results,'complete':all('delta' in r for r in results)}
    if out['complete']:
        mp.mp.dps = 200
        g = [mp.mpf(row['delta']) for row in results]
        scale = mp.mpf(3)/10000
        a = [(v/g[0])**2/scale**n for n,v in enumerate(g)]
        c = [(-1)**k*mp.binomial(17,k)*mp.binomial(18+k,k)/(k+1) for k in range(18)]
        value = mp.fsum(c[i]*c[j]*a[i+j] for i in range(18) for j in range(18))
        out['witness'] = {
            'scale':'3/10000', 'degree':17,
            'coefficient_formula':'(-1)^k binom(17,k) binom(18+k,k)/(k+1)',
            'coefficients':list(map(str,c)),
            'normalized_value':str(value),
            'unnormalized_value':str(value*g[0]**2),
            'max_relative_disagreement':str(max(mp.mpf(row['relative_disagreement']) for row in results))}
        print(json.dumps(out['witness'],indent=2),flush=True)
    json.dump(out,open('witness-results.json','w'),indent=2)
