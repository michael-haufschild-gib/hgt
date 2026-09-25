# Ratios-recipe residue engine with explicit representation  sum_key  exp(key) * rational(w),
# key = linear form in the w's (and theta).  Closure side per term = sign of d key / d w.
import sympy as sp, itertools, time, sys
th = sp.symbols("theta", positive=True)
TH0 = sp.Rational(3, 10)

def Yrat(A, B, C, D):
    num = sp.Integer(1); den = sp.Integer(1)
    for a in A:
        for b in B: den *= (a + b)
    for c in C:
        for d in D: den *= (c + d)
    for a in A:
        for d in D: num *= (a + d)
    for c in C:
        for b in B: num *= (c + b)
    return num / den

def swap_terms(A, B, C, D):
    K, Lb = len(A), len(B); out = []
    for j in range(min(K, Lb) + 1):
        for S in itertools.combinations(range(K), j):
            for U in itertools.combinations(range(Lb), j):
                A2 = [A[k] for k in range(K) if k not in S] + [-B[l] for l in U]
                B2 = [B[l] for l in range(Lb) if l not in U] + [-A[k] for k in S]
                expo = -(sum(A[k] for k in S) + sum(B[l] for l in U))
                out.append((sp.expand(expo), Yrat(A2, B2, C, D)))
    return out

def d_term(key, r, x):
    # d/dx [exp(key) r] = exp(key) (key_x r + r_x)
    return key, sp.together(sp.diff(key, x) * r + sp.diff(r, x))

def poles_in(r, w):
    den = sp.factor(sp.denom(sp.together(r))); roots = {}
    for fac, mult in sp.factor_list(den)[1]:
        if fac.has(w) and fac.is_polynomial(w) and sp.Poly(fac, w).degree() == 1:
            p = sp.solve(fac, w)[0]
            roots[p] = roots.get(p, 0) + mult
    return roots

def residue_term(key, r, w, p, m):
    # residue at w=p (order m) of exp(key) r ; key linear so d^k exp(key)/dw^k = c^k exp(key)
    c = sp.diff(key, w)
    g = sp.cancel(sp.together(r * (w - p) ** m))
    total = 0
    for k in range(m):
        dk = sp.diff(g, w, m - 1 - k) if m - 1 - k > 0 else g
        total += sp.binomial(m - 1, k) * c ** k * dk.subs(w, p)
    total = sp.cancel(sp.together(total / sp.factorial(m - 1)))
    return sp.expand(key.subs(w, p)), total

def integrate_var(terms, w, cvals, log=True):
    new = {}
    for key, r in terms.items():
        c = sp.diff(key, w)
        cnum = sp.N(c.subs(th, TH0))
        ps = poles_in(r, w)
        if cnum >= 0:
            keep = {p: m for p, m in ps.items() if sp.re(sp.N(p.subs(cvals))) < cvals[w]}; sign = 1
        else:
            keep = {p: m for p, m in ps.items() if sp.re(sp.N(p.subs(cvals))) > cvals[w]}; sign = -1
        if log: print("   ", w, "coeff", c, "close", "LEFT" if sign == 1 else "RIGHT", "poles", ps, "kept", list(keep), flush=True)
        for p, m in keep.items():
            k2, r2 = residue_term(key, r, w, p, m)
            new[k2] = sp.cancel(sp.together(new.get(k2, 0) + sign * r2))
    return {k: v for k, v in new.items() if v != 0}

def run(terms, ws, cvals):
    for w in reversed(ws):
        terms = integrate_var(terms, w, cvals)
    assert all(sp.simplify(k) == 0 for k in terms), terms.keys()
    return sp.simplify(sum(terms.values()))

def head_moment(k, kpow):
    al = sp.symbols('a1:%d' % (k+1)); be = sp.symbols('b1:%d' % (k+1))
    ws = sp.symbols('w1:%d' % (2*k+1)); C = list(ws[:k]); D = list(ws[k:])
    terms = swap_terms(list(al), list(be), C, D)
    out = []
    for key, r in terms:
        for a in al: key, r = d_term(key, r, a)
        for b in be: key, r = d_term(key, r, b)
        subs = {al[i]: C[i] for i in range(k)}; subs.update({be[j]: D[j] for j in range(k)})
        key = sp.expand(key.subs(subs) + th * sum(ws)); r = sp.cancel(sp.together(r.subs(subs)))
        for w in ws: r = r / w ** kpow
        out.append((key, r))
    terms = {}
    for key, r in out: terms[key] = sp.cancel(sp.together(terms.get(key, 0) + r))
    n = len(ws); cvals = {ws[i]: sp.Integer(n - i) for i in range(n)}
    val = run(terms, list(ws), cvals)
    return sp.simplify(val / th ** (2 * k * kpow))

