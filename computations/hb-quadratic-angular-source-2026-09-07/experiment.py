"""Run on RunPod only. Exact exploratory algebra, never proof certificates."""
import functools
import json
import multiprocessing as mp
import os
import time
from pathlib import Path
import sympy as sp

s, r, y, B = sp.symbols('s r y B')
S, Sx, Sy, Sxx, Sxy, Sxxx, Sxxy = jets = sp.symbols('S Sx Sy Sxx Sxy Sxxx Sxxy')
lam = (s+1)*(s+2)
f = r*r-1
angular_x = (Sx, Sxx, Sxy, Sxxx, Sxxy)
angular_y = (Sy, Sxy, lam*S/y**2-Sxx, Sxxy, lam*Sx/y**2-Sxxx)

def partial(v, k):
    if k == 0:
        return sp.diff(v, B)*s*B
    if k == 1:
        return sp.diff(v, r)+sp.diff(v, B)*s*B/(r*f)
    vals = angular_x if k == 2 else angular_y
    return (sp.diff(v, y) if k == 3 else 0) + sum(
        sp.diff(v, q)*dq for q, dq in zip(jets[:5], vals))

def at(v):
    return sp.cancel(v.subs({y: 1, B: 1}))

def coefficient_list(v):
    poly = sp.Poly(sp.expand(v), *jets)
    return [{'powers': list(p), 'coefficient': str(sp.factor(c))}
            for p, c in poly.terms() if c != 0]

def run_sector(sector):
    start = time.monotonic()
    a, b = {'SS': (1, 0), 'VV': (0, 1), 'SUM': (1, 1)}[sector]
    T = s*(s-3)/2+s*(s+1)/(2*r*r)
    M = -s*(r*r-s)/(r*f)
    A = (-r*r-s*(s+1)/2)/y**2
    h = a*B*S*sp.Matrix([[T,M,0,0],[M,T/f**2,0,0],
                        [0,0,A,0],[0,0,0,A]])
    V = (Sy,-Sx)
    for j in range(2):
        h[0,j+2] = h[j+2,0] = -b*s*B*V[j]/r
        h[1,j+2] = h[j+2,1] = -b*s*B*V[j]/f
    g = sp.diag(-f, 1/f, r*r/y**2, r*r/y**2)
    metric = [g.applyfunc(at), h.applyfunc(at)]
    first = [[m.applyfunc(lambda v: at(partial(v,k))) for k in range(4)] for m in (g,h)]
    second = [[[m.applyfunc(lambda v: at(partial(partial(v,j),k)))
                for j in range(4)] for k in range(4)] for m in (g,h)]
    G0 = sp.diag(-1/f, f, 1/r**2, 1/r**2)
    G1 = (-G0*metric[1]*G0).applyfunc(sp.cancel)
    G2 = (-G1*metric[1]*G0).applyfunc(sp.cancel)
    inv = [G0,G1,G2]
    invd = [[(-sum((inv[a0]*first[b0][k]*inv[c0]
                   for a0 in range(n+1) for b0 in range(min(1,n-a0)+1)
                   for c0 in [n-a0-b0]), sp.zeros(4))).applyfunc(sp.cancel)
             for k in range(4)] for n in range(3)]
    @functools.lru_cache(maxsize=None)
    def connection(n,u,i,j):
        return sp.cancel(sum(inv[n-b0][u,m]*(first[b0][i][m,j]+
            first[b0][j][m,i]-first[b0][m][i,j])
            for b0 in range(min(1,n)+1) for m in range(4))/2)
    @functools.lru_cache(maxsize=None)
    def connection_d(n,k,u,i,j):
        return sum(invd[n-b0][k][u,m]*(first[b0][i][m,j]+
            first[b0][j][m,i]-first[b0][m][i,j])+
            inv[n-b0][u,m]*(second[b0][k][i][m,j]+
            second[b0][k][j][m,i]-second[b0][k][m][i,j])
            for b0 in range(min(1,n)+1) for m in range(4))/2
    @functools.lru_cache(maxsize=None)
    def ricci(n,i,j):
        val = sum(connection_d(n,u,u,j,i)-connection_d(n,j,u,u,i)+
            sum(connection(a0,u,u,m)*connection(n-a0,m,j,i)-
                connection(a0,u,j,m)*connection(n-a0,m,u,i)
                for a0 in range(n+1) for m in range(4)) for u in range(4))
        return sp.cancel(val)
    checks = {str(n): [str(sp.cancel(ricci(n,i,j)+3*metric[n][i,j]))
                      for i in range(4) for j in range(4)] for n in (0,1)}
    if any(v != '0' for row in checks.values() for v in row):
        raise AssertionError((sector, checks))
    diff = sp.cancel(ricci(2,2,2)-ricci(2,3,3))
    off = ricci(2,2,3)
    result = {'sector': sector, 'checks': checks, 'seconds': time.monotonic()-start,
              'difference': coefficient_list(diff), 'offdiagonal': coefficient_list(off),
              'difference_raw': str(diff), 'offdiagonal_raw': str(off)}
    Path(sector+'.json').write_text(json.dumps(result, indent=2)+'\n')
    print(sector, 'done', round(result['seconds'],2), flush=True)
    return result

if __name__ == '__main__':
    print('sympy', sp.__version__, 'cpus', os.cpu_count(), flush=True)
    start = time.monotonic()
    with mp.get_context('fork').Pool(3) as pool:
        results = pool.map(run_sector, ['SS','VV','SUM'])
    env = {str(v):v for v in (s,r,y,B,*jets)}
    mix = {'sector': 'SV', 'normalization': 'coefficient of aS*aV'}
    for key in ('difference','offdiagonal'):
        expressions = [sp.sympify(v[key+'_raw'], locals=env) for v in results]
        expr = sp.cancel(expressions[2]-expressions[0]-expressions[1])
        mix[key] = coefficient_list(expr)
        mix[key+'_raw'] = str(expr)
    Path('SV.json').write_text(json.dumps(mix, indent=2)+'\n')
    Path('metadata.json').write_text(json.dumps({'seconds': time.monotonic()-start,
        'sympy': sp.__version__, 'workers':3, 'cpu_count':os.cpu_count()},indent=2)+'\n')
    print('finished', round(time.monotonic()-start,2), flush=True)
