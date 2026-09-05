import sympy as sp, time, sys, itertools
from engine import *
eps = sp.symbols('epsilon')
def moll_new(K, Lb, Q, R, order, avals, bvals, kpow=2):
    A = [eps * sp.Integer(k) for k in avals[:K]]; B = [eps * sp.Integer(k) for k in bvals[:Lb]]
    ws = sp.symbols('w1:%d' % (Q + R + 1)); C = list(ws[:Q]); D = list(ws[Q:])
    terms = {}
    for key, r in swap_terms(A, B, C, D):
        key = sp.expand(key + th * sum(ws))
        for w in ws: r = r / w ** kpow
        terms[key] = sp.cancel(sp.together(terms.get(key, 0) + r))
    n = len(ws); cvals = {ws[i]: sp.Integer(n - i) for i in range(n)}
    for w in order:
        terms = integrate_var(terms, w, cvals, log=False)
    total = sum(sp.exp(k) * v for k, v in terms.items())
    val = sp.series(total, eps, 0, 1).removeO()
    return sp.simplify(sp.simplify(val) / th ** (Q + R))
def moll_old(K, Lb, Q, R, order, avals, bvals, kpow=2):
    A = [eps * sp.Integer(k) for k in avals[:K]]; B = [eps * sp.Integer(k) for k in bvals[:Lb]]
    ws = sp.symbols('w1:%d' % (Q + R + 1)); C = list(ws[:Q]); D = list(ws[Q:])
    total = sum(sp.exp(k) * r for k, r in swap_terms(A, B, C, D))
    R0 = sp.simplify(sp.series(total, eps, 0, 1).removeO())
    integrand = R0
    for w in ws: integrand = integrand * sp.exp(th * w) / w ** kpow
    terms = {sp.expand(th * sum(ws)): sp.cancel(sp.together(R0 / sp.prod([w ** kpow for w in ws])))}
    n = len(ws); cvals = {ws[i]: sp.Integer(n - i) for i in range(n)}
    for w in order:
        terms = integrate_var(terms, w, cvals, log=False)
    total = sum(sp.exp(k) * v for k, v in terms.items())
    return sp.simplify(total / th ** (Q + R))
ws4 = sp.symbols('w1:5')
for name, fn in [("old(limit first)", moll_old), ("new(residues first)", moll_new)]:
    for order in [list(reversed(ws4)), list(ws4), [ws4[1], ws4[3], ws4[0], ws4[2]]]:
        for av, bv in [([1, 2], [3, 5]), ([1, 3], [2, 7])]:
            t0 = time.time()
            print(name, "order", order, "shifts", av, bv, "=>", fn(2, 2, 2, 2, order, av, bv), round(time.time() - t0, 1), flush=True)
print("ADJ DONE")
