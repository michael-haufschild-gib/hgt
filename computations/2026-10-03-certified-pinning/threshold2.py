# S6: positivity thresholds for degree-2 (and degree-1) archimedean data with/without poles.
# Datum: q^{s/2} prod_j Gamma_R(s+mu_j) L(s), pole order m at s=0,1.
# Weil form: m*(h(i/2)+h(-i/2)) + (log q - d log pi) g(0) + (1/2pi) int h sum_j Re psi((1/2+mu_j+ir)/2) dr - 2 sum lam_n n^{-1/2} g(log n)
import numpy as np, scipy.special as sp, cvxpy as cp, json, sys, time
from weilform import B8, Bhat, vonmangoldt

def setup(L, mus, hk=0.05):
    m = int(round(L/hk)) - 3; hk = L/(m + 3)
    xs = -L/2 + 2*hk + hk*np.arange(m)
    D = xs[:, None] - xs[None, :]
    G = hk*B8(D/hk)
    Sx = lambda x: 0.5*hk*(B8((D - x)/hk) + B8((-D - x)/hk))
    def Fvec(a):
        z = a*hk/2; return hk*np.exp(a*xs)*(np.sinh(z)/z)**4
    P = np.outer(Fvec(0.5), Fvec(-0.5)); P = P + P.T
    R = 120.0/hk; dr = min(0.002, 0.2/L); r = np.arange(0.0, R, dr) + dr/2
    psi = sum(np.real(sp.digamma(0.25 + mu/2 + 0.5j*r)) for mu in mus)
    wgt = Bhat(r*hk)**2*psi*dr*2
    K = np.array([(hk**2/(2*np.pi))*np.sum(wgt*np.cos(r*dl)) for dl in hk*np.arange(m)])
    A = K[np.abs(np.arange(m)[:, None] - np.arange(m)[None, :])]
    return dict(m=m, G=G, Sx=Sx, P=P, A=A)

def kstar(L, mus, pole, fixed=None, q=1.0, hk=0.05):
    S = setup(L, mus, hk)
    Ci = np.linalg.inv(np.linalg.cholesky(S["G"]))
    T = lambda M: (lambda X: (X + X.T)/2)(Ci @ M @ Ci.T)
    Q0 = T(S["A"] + (np.log(q) - len(mus)*np.log(np.pi))*S["G"] + pole*S["P"])
    Nmax = int(np.floor(np.exp(L)))
    Ms = [T(2/np.sqrt(n)*S["Sx"](np.log(n))) for n in range(2, Nmax + 1)]
    if fixed is not None:
        return float(np.linalg.eigvalsh(Q0 - sum(fixed[n]*Ms[n - 2] for n in range(2, Nmax + 1)))[0]), None
    lam = cp.Variable(len(Ms)); t = cp.Variable()
    cp.Problem(cp.Maximize(t), [Q0 - sum(lam[i]*Ms[i] for i in range(len(Ms))) - t*np.eye(S["m"]) >> 0]).solve(solver=cp.CLARABEL, max_iter=500)
    return float(t.value), [float(x) for x in lam.value]

def dedekind_weights(N, chi):
    # Lambda_K(n) for quadratic K: Lambda(n) * (1 + chi(n')) style: -zeta_K'/zeta_K = -zeta'/zeta - L'/L(chi)
    lam = vonmangoldt(N); return np.array([lam[n]*(1 + chi(n)) for n in range(N + 1)])

if __name__ == "__main__":
    chim3 = lambda n: [0, 1, -1][n % 3]
    chi5 = lambda n: [0, 1, -1, -1, 1][n % 5]
    data = [("GC_pole1", [0.0, 1.0], 1, 3.0, chim3), ("GR2_pole1", [0.0, 0.0], 1, 5.0, chi5),
            ("GR2_pole2", [0.0, 0.0], 2, 1.0, None), ("GC_nopole", [0.0, 1.0], 0, None, None),
            ("GR2_nopole", [0.0, 0.0], 0, None, None), ("GR_pole1", [0.0], 1, 1.0, None)]
    for L in [float(x) for x in sys.argv[1].split(",")]:
        t0 = time.time(); rec = dict(L=L)
        N = int(np.floor(np.exp(L)))
        for name, mus, pole, qa, chi in data:
            k, lam = kstar(L, mus, pole)
            entry = dict(qstar=round(float(np.exp(-k)), 5), lam=[round(x, 4) for x in lam[:6]])
            if qa is not None:
                w = dedekind_weights(N, chi) if chi else (2*vonmangoldt(N) if pole == 2 else vonmangoldt(N))
                kk, _ = kstar(L, mus, pole, fixed=w, q=qa)
                entry["arith_q"] = qa; entry["arith_mumin"] = float("%.3e" % kk)
                entry["arith_lam"] = [round(float(x), 4) for x in w[2:8]]
            rec[name] = entry
        rec["time"] = round(time.time() - t0, 1)
        print(json.dumps(rec), flush=True)
