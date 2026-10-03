# Certified pinning (computer-assisted, interval arithmetic).
# Claim: every lam : N -> R whose Weil form (zeta's archimedean datum, pole weight 1, conductor 1) is >= 0 on the cubic
# B-spline span over [-L/2, L/2] (knot spacing hk = L/(m+3)) satisfies rigorous bounds on delta_n = lam(n) - Lambda(n).
# Certificates: PSD X = sum_k w_k v_k v_k^T with rational entries; producer => sum_n delta_n m_n(X) <= q(X).
import os; os.environ['OPENBLAS_NUM_THREADS'] = '4'
import numpy as np, cvxpy as cp, json, sys
from fractions import Fraction
from math import comb
from weilform import setup
from weilform import vonmangoldt
from flint import arb, acb, ctx
ctx.prec = 256

Lq = Fraction(sys.argv[1]); m = int(sys.argv[2]); L = float(Lq); hkq = Lq/(m + 3); hk = float(hkq)
Nmax = int(np.floor(np.exp(L))); ns = list(range(2, Nmax + 1)); lamv = vonmangoldt(Nmax)

# ---------------- Step A: double-precision certificates ----------------
S = setup(L, hk); assert S["m"] == m, (S["m"], m)
Ms = {n: 2/np.sqrt(n)*S["Sx"](np.log(n)) for n in ns}
QL = S["Q0"] - sum(lamv[n]*Ms[n] for n in ns)
Cl = np.linalg.cholesky(S["G"]); Ci = np.linalg.inv(Cl)
T = lambda X: (lambda Y: (Y + Y.T)/2)(Ci @ X @ Ci.T)
QLt = T(QL); mu, U = np.linalg.eigh(QLt); Dm = 1/np.sqrt(np.maximum(mu, 1e-16))
pre = lambda X: (lambda Y: (Y + Y.T)/2)((Dm[:, None]*(U.T @ T(X) @ U))*Dm[None, :])
Ns = {n: pre(Ms[n]) for n in ns}; sc = {n: np.linalg.norm(Ns[n], 2) for n in ns}
y = cp.Variable(len(ns))
cons = [np.eye(m) - sum(y[i]*Ns[n]/sc[n] for i, n in enumerate(ns)) >> 0]
certs = []
for i, n in enumerate(ns):
    for sense in (cp.Minimize, cp.Maximize):
        prob = cp.Problem(sense(y[i]), cons)
        ok = False
        for solver, kw in ((cp.CLARABEL, dict(max_iter=3000)), (cp.SCS, dict(eps=1e-11, max_iters=300000))):
            try:
                prob.solve(solver=solver, **kw); ok = cons[0].dual_value is not None; break
            except Exception:
                continue
        if not ok: continue
        Z = cons[0].dual_value; Z = (Z + Z.T)/2
        # map back: tr(Z pre(X)) = tr(B Z B^T X) with B = (Ci^T U D)
        B = Ci.T @ U @ np.diag(Dm)
        Xo = B @ Z @ B.T; Xo = (Xo + Xo.T)/2
        ev, V = np.linalg.eigh(Xo); keep = ev > 1e-10*ev.max()
        certs.append(dict(target=n, sense="min" if sense is cp.Minimize else "max", w=ev[keep], V=V[:, keep],
                          approx=float(prob.value)/sc[n]))
# also bottom eigenvectors of the generalized problem QL v = mu G v (rank-1 certificates)
evg, Vg = np.linalg.eigh(QLt); 
for k in range(min(12, m)):
    certs.append(dict(target=0, sense="eig", w=np.array([1.0]), V=(Ci.T @ Vg[:, [k]])))
print(json.dumps(dict(stage="A", L=L, m=m, hk=hk, ns=ns, ncerts=len(certs),
      approx=[(c["target"], c["sense"], c.get("approx")) for c in certs if c["target"]])), flush=True)

# ---------------- Step B: arb matrices ----------------
hka = arb(hkq.numerator)/hkq.denominator
def M8_piece(u, q):          # cardinal B-spline of order 8 on piece u in [q, q+1], valid for real or complex u
    s = 0
    for j in range(0, q + 5):
        s += (-1)**j*comb(8, j)*(u + 4 - j)**7
    return s/5040
def M8_real(u):              # rigorous for real arb u, piece chosen with a safety check
    uf = float(u.mid()) if hasattr(u, 'mid') else float(u)
    if abs(uf) >= 4: return arb(0)
    q = int(np.floor(uf))
    assert u > q and u < q + 1 or u.is_exact(), "piece ambiguity"
    return M8_piece(u, q)
G = [[hka*M8_real(arb(i - j)) for j in range(m)] for i in range(m)]
def S_arb(n):
    t = arb(n).log()/hka
    return [[hka/2*(M8_real(arb(i - j) - t) + M8_real(arb(j - i) - t)) for j in range(m)] for i in range(m)]
xs = [-arb(Lq.numerator)/Lq.denominator/2 + 2*hka + hka*i for i in range(m)]
def Fv(a):
    z = a*hka/2
    return [hka*(a*x).exp()*(z.sinh()/z)**4 for x in xs]
Fp, Fm = Fv(arb(1)/2), Fv(-arb(1)/2)
P = [[Fp[i]*Fm[j] + Fm[i]*Fp[j] for j in range(m)] for i in range(m)]
euler = arb.const_euler()
def arch_lag(k):
    # K = arch(g_k), g_k(x) = (hk/2)[M8(k - x/hk) + M8(-k - x/hk)];  x = hk*t
    g0 = hka*M8_real(arb(k))
    def gpiece(tz, p):
        val = 0
        for sgn in (1, -1):
            q = sgn*k - p - 1
            if -4 <= q <= 3:
                val = val + M8_piece(sgn*k - tz, q)
        return hka/2*val
    total = arb(0)
    eta = arb(10)**(-30)
    pmax = k + 4
    for p in range(0, pmax):
        a = eta if p == 0 else arb(p)
        f = lambda z, an, p=p: hka*(g0*(-2*hka*z).exp() - (-hka*z/2).exp()*gpiece(z, p))/(1 - (-2*hka*z).exp())
        total += acb.integral(f, acb(a), acb(p + 1)).real
    X = hka*pmax
    tail = -(g0/2)*(1 - (-2*X).exp()).log()
    head = arb(0, (hka*eta*(arb(2) + 4/hka)).upper())     # |integrand| <= 1.5 g0 + max|g'| on [0, eta*hk]
    return -euler*g0 + 2*(total + tail + head)
K = [arch_lag(k) for k in range(m)]
A = [[K[abs(i - j)] for j in range(m)] for i in range(m)]
logpi = arb.pi().log()
Sn = {n: S_arb(n) for n in ns}
Lam = {n: (arb(n).log() if lamv[n] > 0 and abs(lamv[n] - np.log(n)) < 1e-9 else (arb(int(round(np.exp(lamv[n])))).log() if lamv[n] > 0 else arb(0))) for n in ns}
QLa = [[P[i][j] - logpi*G[i][j] + A[i][j] - sum(2*Lam[n]/arb(n).sqrt()*Sn[n][i][j] for n in ns) for j in range(m)] for i in range(m)]
# cross-check vs double
dev = max(abs(float(QLa[i][j].mid()) - QL[i][j]) for i in range(m) for j in range(m))
print(json.dumps(dict(stage="B", max_dev_vs_double=dev, max_rad=max(float(QLa[i][j].rad()) for i in range(m) for j in range(m)))), flush=True)

# ---------------- Step C: rigorous inequalities and elimination ----------------
def quad(Mx, v):
    return sum(v[i]*Mx[i][j]*v[j] for i in range(m) for j in range(m) if v[i] != 0 and v[j] != 0)
ineqs = []
for c in certs:
    q = arb(0); mm = {n: arb(0) for n in ns}
    for k in range(c["V"].shape[1]):
        w = Fraction(max(float(c["w"][k]), 0.0)).limit_denominator(10**18)
        if w == 0: continue
        vr = [Fraction(float(x)).limit_denominator(10**18) for x in c["V"][:, k]]
        va = [arb(f.numerator)/f.denominator for f in vr]
        wa = arb(w.numerator)/w.denominator
        q += wa*quad(QLa, va)
        for n in ns:
            mm[n] += wa*2/arb(n).sqrt()*quad(Sn[n], va)
    ineqs.append((mm, q))
# for each target n0: Fourier-Motzkin over all other variables is costly; use 2-variable elimination when len(ns)<=2,
# otherwise LP with interval-safe post-check: take the LP multipliers (double), then evaluate the combination rigorously.
import scipy.optimize as so
res = {}
for n0 in ns:
    out = []
    for sgn in (1, -1):   # sgn=+1 -> upper bound on delta_n0, -1 -> lower bound
        # find y >= 0 with sum_j y_j m_{n,j} = sgn*e_{n0} (other n zero), minimize sum_j y_j q_j  (double)
        Aeq = np.array([[float(ineqs[j][0][n].mid()) for j in range(len(ineqs))] for n in ns])
        beq = np.array([sgn*(1.0 if n == n0 else 0.0) for n in ns])
        cvec = np.array([float(ineqs[j][1].mid()) for j in range(len(ineqs))])
        lp = so.linprog(cvec, A_eq=Aeq, b_eq=beq, bounds=[(0, None)]*len(ineqs), method="highs")
        if lp.status != 0:
            out.append(None); continue
        yv = [Fraction(float(v)).limit_denominator(10**18) for v in lp.x]
        ya = [arb(f.numerator)/f.denominator for f in yv]
        # rigorous: combined inequality sum_n delta_n C_n <= Qc with C_n = sum y_j m_{n,j}
        C = {n: sum(ya[j]*ineqs[j][0][n] for j in range(len(ineqs))) for n in ns}
        Qc = sum(ya[j]*ineqs[j][1] for j in range(len(ineqs)))
        # residual coefficients for other n are tiny but nonzero: report them; bound valid if |delta_n| for n!=n0
        # is controlled -> we return the raw combined inequality
        out.append(dict(C0=str(C[n0]), others=max([abs(float(C[n].mid())) for n in ns if n != n0] + [0.0]),
                        Qc=str(Qc), bound=float((Qc/C[n0]).mid()) * (1 if sgn == 1 else 1)))
    res[n0] = out
print(json.dumps(dict(stage="C", results=res), default=str), flush=True)

# ---------------- Step D (d=2): rigorous polygon from the four combined inequalities ----------------
if len(ns) == 2:
    rows = []
    for n0 in ns:
        for sgn in (1, -1):
            Aeq = np.array([[float(ineqs[j][0][n].mid()) for j in range(len(ineqs))] for n in ns])
            beq = np.array([sgn*(1.0 if n == n0 else 0.0) for n in ns])
            cvec = np.array([float(ineqs[j][1].mid()) for j in range(len(ineqs))])
            lp = so.linprog(cvec, A_eq=Aeq, b_eq=beq, bounds=[(0, None)]*len(ineqs), method="highs")
            yv = [Fraction(float(v)).limit_denominator(10**18) for v in lp.x]
            ya = [arb(f.numerator)/f.denominator for f in yv]
            C = [sum(ya[j]*ineqs[j][0][n] for j in range(len(ineqs))) for n in ns]
            Qc = sum(ya[j]*ineqs[j][1] for j in range(len(ineqs)))
            rows.append((C, Qc))
    # vertices of the polygon {d : C.d <= Q for each row}: intersect pairs, keep those satisfying all rows (outer, rigorous)
    verts = []
    for a in range(4):
        for b in range(a + 1, 4):
            (C1, Q1), (C2, Q2) = rows[a], rows[b]
            det = C1[0]*C2[1] - C1[1]*C2[0]
            if abs(float(det.mid())) < 1e-6: continue
            d0 = (Q1*C2[1] - Q2*C1[1])/det; d1 = (C1[0]*Q2 - C2[0]*Q1)/det
            # feasibility (allow interval overlap)
            feas = all(float((Cr[0]*d0 + Cr[1]*d1 - Qr).lower()) <= 1e-30 for (Cr, Qr) in rows)
            if feas: verts.append((d0, d1))
    d2lo = min(v[0].lower() for v in verts); d2hi = max(v[0].upper() for v in verts)
    d3lo = min(v[1].lower() for v in verts); d3hi = max(v[1].upper() for v in verts)
    print(json.dumps(dict(stage="D", nverts=len(verts), delta2=[str(d2lo), str(d2hi)], delta3=[str(d3lo), str(d3hi)])), flush=True)

# ---------------- Step E (any d): rigorous bootstrap box ----------------
combos = []
for n0 in ns:
    for sgn in (1, -1):
        Aeq = np.array([[float(ineqs[j][0][n].mid()) for j in range(len(ineqs))] for n in ns])
        beq = np.array([sgn*(1.0 if n == n0 else 0.0) for n in ns])
        cvec = np.array([float(ineqs[j][1].mid()) for j in range(len(ineqs))])
        lp = so.linprog(cvec, A_eq=Aeq, b_eq=beq, bounds=[(0, None)]*len(ineqs), method="highs")
        if lp.status != 0:
            combos.append((n0, sgn, None)); continue
        yv = [Fraction(float(v)).limit_denominator(10**18) for v in lp.x]
        ya = [arb(f.numerator)/f.denominator for f in yv]
        C = {n: sum(ya[j]*ineqs[j][0][n] for j in range(len(ineqs))) for n in ns}
        Qc = sum(ya[j]*ineqs[j][1] for j in range(len(ineqs)))
        combos.append((n0, sgn, (C, Qc)))
if all(c[2] is not None for c in combos):
    # |delta_n0| bound: sgn*C_n0 > 0;  sgn*delta_n0 * |C_n0| <= Qc + sum_{n!=n0} |C_n| M
    Mbound = arb(0)
    for n0, sgn, (C, Qc) in combos:
        Cabs = abs(C[n0]); E = sum((abs(C[n]) for n in ns if n != n0), arb(0))
        assert float((sgn*C[n0]).lower()) > 0
        den = Cabs - E
        assert float(den.lower()) > 0
        val = abs(Qc)/den
        Mbound = Mbound if float(Mbound.upper()) >= float(val.upper()) else val
    Mup = arb(Mbound.upper())
    box = {}
    for n0, sgn, (C, Qc) in combos:
        E = sum((abs(C[n]) for n in ns if n != n0), arb(0))
        bnd = (Qc + E*Mup)/abs(C[n0])        # sgn*delta_n0 <= bnd
        box.setdefault(n0, [None, None])[0 if sgn < 0 else 1] = (-bnd).lower() if sgn < 0 else bnd.upper()
    print(json.dumps(dict(stage="E", M=str(Mup), box={n: [float(v[0]), float(v[1])] for n, v in box.items()})), flush=True)
else:
    print(json.dumps(dict(stage="E", error="some LP infeasible (unbounded direction)", missing=[(c[0], c[1]) for c in combos if c[2] is None])), flush=True)

# ---------------- Step F: per-coordinate iterative refinement of the bootstrap box ----------------
if all(c[2] is not None for c in combos):
    B = {n: Mup for n in ns}                       # start: global bound (rigorous)
    lo = {n: -Mup for n in ns}; hi = {n: Mup for n in ns}
    for it in range(60):
        changed = False
        for n0, sgn, (C, Qc) in combos:
            E = sum((abs(C[n])*arb(max(abs(float(lo[n].lower())), abs(float(hi[n].upper())))) for n in ns if n != n0), arb(0))
            bnd = arb(((Qc + E)/abs(C[n0])).upper())
            if sgn > 0:
                if float(bnd.upper()) < float(hi[n0].upper()) - 1e-300: hi[n0] = bnd; changed = True
            else:
                nb = -bnd
                if float(nb.lower()) > float(lo[n0].lower()) + 1e-300: lo[n0] = arb(nb.lower()); changed = True
        if not changed: break
    print(json.dumps(dict(stage="F", iters=it, box={n: [float(lo[n].lower()), float(hi[n].upper())] for n in ns})), flush=True)
