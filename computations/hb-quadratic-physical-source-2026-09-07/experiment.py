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
    C = s**2*((s+1)**2-4*r**2)/(8*r**4)
    k = sp.zeros(4)
    k[0,1] = k[1,0] = a*a*B**2*C*S**2
    k[1,1] = 2*k[0,1]/f
    for j in range(2):
        k[0,j+2] = k[j+2,0] = a*b*f*B**2*s*(s+1)*S*V[j]/(2*r**3)
    metric = [m.applyfunc(at) for m in (g,h,k)]
    first = [[m.applyfunc(lambda v: at(partial(v,k))) for k in range(4)] for m in (g,h,k)]
    second = [[[m.applyfunc(lambda v: at(partial(partial(v,j),k)))
                for j in range(4)] for k in range(4)] for m in (g,h,k)]
    G0 = sp.diag(-1/f, f, 1/r**2, 1/r**2)
    G1 = (-G0*metric[1]*G0).applyfunc(sp.cancel)
    G2 = (-G1*metric[1]*G0-G0*metric[2]*G0).applyfunc(sp.cancel)
    inv = [G0,G1,G2]
    invd = [[(-sum((inv[a0]*first[b0][k]*inv[c0]
                   for a0 in range(n+1) for b0 in range(min(2,n-a0)+1)
                   for c0 in [n-a0-b0]), sp.zeros(4))).applyfunc(sp.cancel)
             for k in range(4)] for n in range(3)]
    @functools.lru_cache(maxsize=None)
    def connection(n,u,i,j):
        return sp.cancel(sum(inv[n-b0][u,m]*(first[b0][i][m,j]+
            first[b0][j][m,i]-first[b0][m][i,j])
            for b0 in range(min(2,n)+1) for m in range(4))/2)
    @functools.lru_cache(maxsize=None)
    def connection_d(n,k,u,i,j):
        return sum(invd[n-b0][k][u,m]*(first[b0][i][m,j]+
            first[b0][j][m,i]-first[b0][m][i,j])+
            inv[n-b0][u,m]*(second[b0][k][i][m,j]+
            second[b0][k][j][m,i]-second[b0][k][m][i,j])
            for b0 in range(min(2,n)+1) for m in range(4))/2
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
    target = sp.Matrix(4,4,lambda i,j: sp.cancel(ricci(2,i,j)+3*metric[2][i,j]))
    trace = sp.cancel(sp.trace(G0*target))
    einstein = (target-trace*metric[0]/2).applyfunc(sp.cancel)
    jac = sp.eye(4)
    jac[0,1] = -1/f
    ingoing = (jac.T*einstein*jac).applyfunc(sp.cancel)
    angular_check = [sp.cancel(einstein[2,2]-einstein[3,3] -
        (b*b*s**2*(3*s*s+12*s+11)/(2*r**4)-a*a*C)*(Sx*Sx-Sy*Sy)),
        sp.cancel(einstein[2,3] -
        (b*b*s**2*(3*s*s+12*s+11)/(2*r**4)-a*a*C)*Sx*Sy)]
    assert angular_check == [0,0],angular_check
    result = {'sector': sector, 'checks': checks, 'angular_check':[str(v) for v in angular_check],
        'seconds': time.monotonic()-start,
        'einstein_raw': [str(v) for v in einstein],
        'einstein_terms': [coefficient_list(v) for v in einstein],
        'ingoing_raw': [str(v) for v in ingoing],
        'ingoing_horizon': [str(sp.factor(v.subs(r,1))) for v in ingoing]}
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
    for key in ('einstein_raw','ingoing_raw','ingoing_horizon'):
        mixed=[]
        for i in range(16):
            expressions = [sp.sympify(v[key][i], locals=env) for v in results]
            mixed.append(sp.cancel(expressions[2]-expressions[0]-expressions[1]))
        mix[key]=[str(v) for v in mixed]
        if key == 'einstein_raw':
            mix['einstein_terms']=[coefficient_list(v) for v in mixed]
    Path('SV.json').write_text(json.dumps(mix, indent=2)+'\n')
    Path('metadata.json').write_text(json.dumps({'seconds': time.monotonic()-start,
        'sympy': sp.__version__, 'workers':3, 'cpu_count':os.cpu_count()},indent=2)+'\n')
    print('finished', round(time.monotonic()-start,2), flush=True)
