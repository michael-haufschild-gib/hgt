# Rigorous verification (Arb) of combined-family certificates: every lam with Weil form >= 0 on the cubic (P=4) AND
# order-8 (P=8) B-spline spans over [-L/2, L/2] satisfies the certified box for delta_n = lam(n) - Lambda(n).
import sys, os, json, numpy as np
from fractions import Fraction
from math import comb, factorial
from flint import arb, acb, ctx
import scipy.optimize as so
ctx.prec = int(sys.argv[2]) if len(sys.argv) > 2 else 400
D = json.load(open(sys.argv[1])); Lq = Fraction(D["L"]).limit_denominator(1000); hkf = D["hk"]; ns = D["ns"]

def frac_arb(s):
    f = Fraction(s); return arb(f.numerator)/f.denominator

def fam_mats(P, m):
    Q = 2*P; hkq = Lq/(m + P - 1); hka = arb(hkq.numerator)/hkq.denominator
    def Mp(u, q):
        s = 0
        for j in range(0, q + P + 1): s += (-1)**j*comb(Q, j)*(u + P - j)**(Q - 1)
        return s/factorial(Q - 1)
    def Mr(u):
        uf = float(u.mid()) if hasattr(u, "mid") else float(u)
        if abs(uf) >= P: return arb(0)
        q = int(np.floor(uf)); assert (u > q and u < q + 1) or u.is_exact(), "piece ambiguity"
        return Mp(u, q)
    G = [[hka*Mr(arb(i - j)) for j in range(m)] for i in range(m)]
    def S(n):
        t = arb(n).log()/hka
        return [[hka/2*(Mr(arb(i - j) - t) + Mr(arb(j - i) - t)) for j in range(m)] for i in range(m)]
    xs = [-arb(Lq.numerator)/Lq.denominator/2 + hka*P/2 + hka*i for i in range(m)]
    def Fv(a):
        z = a*hka/2; return [hka*(a*x).exp()*(z.sinh()/z)**P for x in xs]
    Fp, Fm = Fv(arb(1)/2), Fv(-arb(1)/2)
    Pm = [[Fp[i]*Fm[j] + Fm[i]*Fp[j] for j in range(m)] for i in range(m)]
    eul = arb.const_euler()
    def arch_lag(k):
        g0 = hka*Mr(arb(k))
        def gpiece(tz, p):
            val = 0
            for sg in (1, -1):
                q = sg*k - p - 1
                if -P <= q <= P - 1: val = val + Mp(sg*k - tz, q)
            return hka/2*val
        total = arb(0); eta = arb(10)**(-40); pmax = k + P
        for p in range(0, pmax):
            a = eta if p == 0 else arb(p)
            f = lambda z, an, p=p: hka*(g0*(-2*hka*z).exp() - (-hka*z/2).exp()*gpiece(z, p))/(1 - (-2*hka*z).exp())
            total += acb.integral(f, acb(a), acb(p + 1)).real
        X = hka*pmax; tail = -(g0/2)*(1 - (-2*X).exp()).log()
        head = arb(0, (hka*eta*(arb(10) + 10/hka)*(1 + abs(g0))).upper())
        return -eul*g0 + 2*(total + tail + head)
    K = [arch_lag(k) for k in range(m)]
    A = [[K[abs(i - j)] for j in range(m)] for i in range(m)]
    lp = arb.pi().log()
    Sn = {n: S(n) for n in ns}
    def Lam(n):
        for p in range(2, n + 1):
            if n % p == 0:
                k = n
                while k % p == 0: k //= p
                return arb(p).log() if k == 1 else arb(0)
        return arb(0)
    QL = [[Pm[i][j] - lp*G[i][j] + A[i][j] - sum(2*Lam(n)/arb(n).sqrt()*Sn[n][i][j] for n in ns) for j in range(m)] for i in range(m)]
    return QL, Sn

mats = {}
for P, m in zip((4, 8), D["m"]):
    mats[P] = fam_mats(P, m)
    print(json.dumps(dict(stage="mats", P=P, m=m, maxrad=max(float(mats[P][0][i][j].rad()) for i in range(m) for j in range(m)))), flush=True)

def quad(Mx, v):
    m = len(v); return sum(v[i]*Mx[i][j]*v[j] for i in range(m) for j in range(m))
ineqs = []
for c in D["certs"]:
    QL, Sn = mats[c["family"]]; q = arb(0); mm = {n: arb(0) for n in ns}
    for part in c["parts"]:
        w = frac_arb(part["w"])
        if not (w > 0): continue
        v = [frac_arb(x) for x in part["v"]]
        q += w*quad(QL, v)
        for n in ns: mm[n] += w*2/arb(n).sqrt()*quad(Sn[n], v)
    ineqs.append((mm, q))
print(json.dumps(dict(stage="ineqs", n=len(ineqs))), flush=True)

combos = []
for n0 in ns:
    for sgn in (1, -1):
        Aeq = np.array([[float(ineqs[j][0][n].mid()) for j in range(len(ineqs))] for n in ns])
        sc = np.abs(Aeq).max(axis=0) + 1e-300; Aeq_s = Aeq/sc; J = len(ineqs); R = len(ns)
        beq = np.array([sgn*(1.0 if n == n0 else 0.0) for n in ns])
        rs = np.abs(Aeq_s).max(axis=1) + 1e-300; Aeq_s = Aeq_s/rs[:, None]; beq = beq/rs
        cvec = np.array([float(ineqs[j][1].mid()) for j in range(J)])/sc
        # slack r+, r- on the non-target rows, penalized (bootstrap absorbs small residuals)
        mu = float(os.environ.get("MU", "1e3"))
        Sl = np.zeros((R, 2*R))
        for i, n in enumerate(ns):
            if n != n0: Sl[i, 2*i] = 1.0; Sl[i, 2*i + 1] = -1.0
        lp = so.linprog(np.concatenate([cvec, mu*np.ones(2*R)]), A_eq=np.hstack([Aeq_s, Sl]), b_eq=beq,
                        bounds=[(0, None)]*(J + 2*R), method="highs")
        if lp.status != 0: combos.append((n0, sgn, None)); continue
        ya = [arb(Fraction(float(v)/s).limit_denominator(10**30).numerator)/Fraction(float(v)/s).limit_denominator(10**30).denominator for v, s in zip(lp.x[:J], sc)]
        C = {n: sum((ya[j]*ineqs[j][0][n] for j in range(len(ineqs))), arb(0)) for n in ns}
        Qc = sum((ya[j]*ineqs[j][1] for j in range(len(ineqs))), arb(0))
        combos.append((n0, sgn, (C, Qc)))
print(json.dumps(dict(stage="combos", missing=[(c[0], c[1]) for c in combos if c[2] is None])), flush=True)
if all(c[2] is not None for c in combos):
    Mb = arb(0)
    for n0, sgn, (C, Qc) in combos:
        E = sum((abs(C[n]) for n in ns if n != n0), arb(0)); den = abs(C[n0]) - E
        assert float((sgn*C[n0]).lower()) > 0 and float(den.lower()) > 0, ("bootstrap fails", n0, sgn)
        v = abs(Qc)/den; Mb = v if float(v.upper()) > float(Mb.upper()) else Mb
    lo = {n: -arb(Mb.upper()) for n in ns}; hi = {n: arb(Mb.upper()) for n in ns}
    for it in range(200):
        ch = False
        for n0, sgn, (C, Qc) in combos:
            E = sum((abs(C[n])*arb(max(abs(float(lo[n].lower())), abs(float(hi[n].upper())))) for n in ns if n != n0), arb(0))
            bnd = arb(((Qc + E)/abs(C[n0])).upper())
            if sgn > 0 and float(bnd.upper()) < float(hi[n0].upper())*(1 - 1e-12): hi[n0] = bnd; ch = True
            if sgn < 0 and float((-bnd).lower()) > float(lo[n0].lower())*(1 - 1e-12): lo[n0] = arb((-bnd).lower()); ch = True
        if not ch: break
    print(json.dumps(dict(stage="box", L=D["L"], hk=hkf, M=str(Mb), iters=it,
                          box={n: [float(lo[n].lower()), float(hi[n].upper())] for n in ns})), flush=True)
