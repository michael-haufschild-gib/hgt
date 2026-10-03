# S5: conductor threshold of prime-blind positivity for degree-1 archimedean data.
# Datum: Lambda(s) = (q/pi)^{s/2} Gamma((s+kappa)/2) L(s), kappa in {0 (even), 1 (odd)}, pole or not.
# Weil form (G-normalized): Q_lam = [P if pole] + (log q - log pi) I + A_kappa - sum lam_n M_n.
# kappa*_L = max_lam min eig(Q_lam at q=1); threshold q*_L = exp(-kappa*_L).
import numpy as np, scipy.special as sp, cvxpy as cp, json, sys, time
from weilform import B8, Bhat, vonmangoldt

def setup(L, kappa, hk=0.05):
    m = int(round(L/hk)) - 3; hk = L/(m + 3)
    xs = -L/2 + 2*hk + hk*np.arange(m)
    D = xs[:, None] - xs[None, :]
    G = hk*B8(D/hk)
    Sx = lambda x: 0.5*hk*(B8((D - x)/hk) + B8((-D - x)/hk))
    def Fvec(a):
        z = a*hk/2; return hk*np.exp(a*xs)*(np.sinh(z)/z)**4
    P = np.outer(Fvec(0.5), Fvec(-0.5)); P = P + P.T
    R = 120.0/hk; dr = min(0.002, 0.2/L); r = np.arange(0.0, R, dr) + dr/2
    wgt = Bhat(r*hk)**2*np.real(sp.digamma(0.25 + kappa/2 + 0.5j*r))*dr*2
    K = np.array([(hk**2/(2*np.pi))*np.sum(wgt*np.cos(r*dl)) for dl in hk*np.arange(m)])
    A = K[np.abs(np.arange(m)[:, None] - np.arange(m)[None, :])]
    return dict(m=m, hk=hk, G=G, Sx=Sx, P=P, A=A)

def chi_weights(N, chi):
    lam = vonmangoldt(N); return np.array([lam[n]*chi(n) for n in range(N + 1)])

HK = 0.05
def kappa_star(L, kappa, pole, hk=None, fixed=None, q=1.0):
    hk = HK if hk is None else hk
    S = setup(L, kappa, hk)
    Ci = np.linalg.inv(np.linalg.cholesky(S["G"]))
    T = lambda M: (lambda X: (X + X.T)/2)(Ci @ M @ Ci.T)
    Q0 = T(S["A"] + (np.log(q) - np.log(np.pi))*S["G"] + (S["P"] if pole else 0))
    Nmax = int(np.floor(np.exp(L)))
    Ms = [T(2/np.sqrt(n)*S["Sx"](np.log(n))) for n in range(2, Nmax + 1)]
    if fixed is not None:
        Q = Q0 - sum(fixed[n]*Ms[n - 2] for n in range(2, Nmax + 1))
        return float(np.linalg.eigvalsh(Q)[0]), None
    if not Ms:
        return float(np.linalg.eigvalsh(Q0)[0]), []
    lam = cp.Variable(len(Ms)); t = cp.Variable()
    prob = cp.Problem(cp.Maximize(t), [Q0 - sum(lam[i]*Ms[i] for i in range(len(Ms))) - t*np.eye(S["m"]) >> 0])
    prob.solve(solver=cp.CLARABEL, max_iter=500)
    return float(t.value), [float(x) for x in lam.value]

if __name__ == "__main__":
    Ls = [float(x) for x in sys.argv[1].split(",")]
    if len(sys.argv) > 2: HK = float(sys.argv[2])
    chi5 = lambda n: [0, 1, -1, -1, 1][n % 5]
    chim3 = lambda n: [0, 1, -1][n % 3]
    chim4 = lambda n: [0, 1, 0, -1][n % 4]
    chi8 = lambda n: [0, 1, 0, -1, 0, -1, 0, 1][n % 8]
    for L in Ls:
        t0 = time.time(); rec = dict(L=L)
        for name, kap, pole in (("even_nopole", 0, False), ("odd_nopole", 1, False), ("even_pole", 0, True)):
            k, lam = kappa_star(L, kap, pole)
            rec[name] = dict(kstar=round(k, 6), qstar=round(float(np.exp(-k)), 5),
                             lam=[round(x, 4) for x in (lam or [])[:8]])
        N = int(np.floor(np.exp(L)))
        for name, kap, chi, q in (("chi5", 0, chi5, 5.0), ("chi8", 0, chi8, 8.0), ("chi-3", 1, chim3, 3.0), ("chi-4", 1, chim4, 4.0)):
            k, _ = kappa_star(L, kap, False, fixed=chi_weights(N, chi), q=q)
            rec[name + "_mumin"] = float("%.3e" % k)
        k, _ = kappa_star(L, 0, True, fixed=vonmangoldt(N))
        rec["zeta_mumin"] = float("%.3e" % k)
        rec["time"] = round(time.time() - t0, 1)
        print(json.dumps(rec), flush=True)
