# Prime-blind extremal certificates: (A) universal optimality over completely monotone objectives,
# (B) real zero structure of the extremal spectrum h*(t) versus zeta zeros and 2pi k/log 2.
import numpy as np, cvxpy as cp, json, sys, time
import scipy.special as sp
from multiprocessing import Pool
from threshold2 import setup
from weilform import Bhat

TOL = dict(tol_gap_abs=1e-10, tol_gap_rel=1e-10, tol_feas=1e-10, max_iter=2000)
GAM = np.array([float(l) for l in open("zeros400.txt") if l.strip()])

def kernel(L, hk, wfun):
    m = int(round(L/hk)) - 3; hk2 = L/(m + 3)
    R = 120.0/hk2; dr = min(0.002, 0.2/L); r = np.arange(0.0, R, dr) + dr/2
    wgt = Bhat(r*hk2)**2*wfun(r)*dr*2
    K = np.array([(hk2**2/(2*np.pi))*np.sum(wgt*np.cos(r*dl)) for dl in hk2*np.arange(m)])
    return K[np.abs(np.arange(m)[:, None] - np.arange(m)[None, :])]

def objectives(L, hk):
    S0 = setup(L, [0.0], hk)
    objs = {}
    for mu in (0.0, 0.5, 1.0, 2.0, 4.0):
        S = setup(L, [mu], hk); objs["arch_mu%g" % mu] = S["A"] - np.log(np.pi)*S["G"]
    for al in (0.5, 2.0, 8.0):
        objs["lorentz_a%g" % al] = -kernel(L, hk, lambda r, a=al: 2*a/(a*a + r*r))
    return S0, objs

def solve(S, L, Q, extra=None):
    m = S["m"]; Nmax = int(np.floor(np.exp(L)))
    X = cp.Variable((m, m), PSD=True)
    cons = [cp.trace(S["G"] @ X) == 1] + [cp.trace(S["Sx"](np.log(n)) @ X) == 0 for n in range(2, Nmax + 1)]
    prob = cp.Problem(cp.Minimize(cp.trace(Q @ X)), cons); prob.solve(solver=cp.CLARABEL, **TOL)
    return float(prob.value), X.value

def partA(args):
    L, hk = args; t0 = time.time()
    S, objs = objectives(L, hk); names = list(objs)
    V, Xs = {}, {}
    for k in names:
        V[k], Xs[k] = solve(S, L, objs[k])
    gap = {i: {j: float("%.2e" % (np.sum(objs[j]*Xs[i]) - V[j])) for j in names} for i in names}
    m = S["m"]; Nmax = int(np.floor(np.exp(L)))
    X = cp.Variable((m, m), PSD=True); s = cp.Variable()
    cons = [cp.trace(S["G"] @ X) == 1] + [cp.trace(S["Sx"](np.log(n)) @ X) == 0 for n in range(2, Nmax + 1)]
    cons += [cp.trace(objs[k] @ X) - V[k] <= s for k in names]
    pj = cp.Problem(cp.Minimize(s), cons); pj.solve(solver=cp.CLARABEL, **TOL)
    # same joint test restricted to the arch family only
    X2 = cp.Variable((m, m), PSD=True); s2 = cp.Variable()
    cons2 = [cp.trace(S["G"] @ X2) == 1] + [cp.trace(S["Sx"](np.log(n)) @ X2) == 0 for n in range(2, Nmax + 1)]
    cons2 += [cp.trace(objs[k] @ X2) - V[k] <= s2 for k in names if k.startswith("arch")]
    pj2 = cp.Problem(cp.Minimize(s2), cons2); pj2.solve(solver=cp.CLARABEL, **TOL)
    H0 = np.outer(np.full(m, L/(m + 3)), np.full(m, L/(m + 3)))
    vt, Xt = solve(S, L, -H0)
    return dict(part="A", L=L, hk=hk, values={k: round(V[k], 8) for k in names}, qstar_even=float(np.exp(-V["arch_mu0"])),
                qstar_odd=float(np.exp(-V["arch_mu1"])), joint_all=float("%.3e" % s.value), joint_arch=float("%.3e" % s2.value),
                turan=round(-vt, 8), log2=round(np.log(2), 8), gaps=gap, time=round(time.time() - t0, 1))

def hgrid(S, X, L, tg):
    m = S["m"]; hk2 = L/(m + 3); xs = -L/2 + 2*hk2 + hk2*np.arange(m)
    out = np.empty(len(tg))
    for a in range(0, len(tg), 4000):
        r = tg[a:a + 4000]
        F = hk2*np.exp(1j*np.outer(r, xs))*Bhat(r*hk2)[:, None]
        out[a:a + 4000] = np.real(np.einsum("ri,ij,rj->r", F, X, F.conj()))
    return out

def partB(args):
    L, hk, mu, pole = args; t0 = time.time()
    S = setup(L, [mu], hk)
    Q = S["A"] - np.log(np.pi)*S["G"] + pole*S["P"]
    v, X = solve(S, L, Q)
    tg = np.arange(0.0, 120.0, 0.002); h = hgrid(S, X, L, tg); h0 = h[0]
    idx = np.where((h[1:-1] < h[:-2]) & (h[1:-1] < h[2:]))[0] + 1
    lat = 2*np.pi/np.log(2)
    mins = []
    for i in idx:
        t = tg[i]; dz = np.min(np.abs(GAM - t)); dl = abs(t - lat*round(t/lat))
        kind = "zeta" if dz < 0.05 else ("lattice" if dl < 0.05 else "EXTRA")
        mins.append([round(float(t), 3), round(float(np.log10(max(h[i], 1e-300)/h0)), 2), kind, round(float(min(dz, dl)), 3)])
    zeta_depth = [round(float(np.log10(max(np.min(h[np.abs(tg - g) < 0.05]), 1e-300)/h0)), 2) for g in GAM[GAM < 119.9]]
    ev = np.linalg.eigvalsh(X)[::-1]
    return dict(part="B", L=L, hk=hk, mu=mu, pole=pole, value=round(v, 8), eigs=[float("%.2e" % e) for e in ev[:4]],
                n_min=len(mins), minima=mins, zeta_depth=zeta_depth, h_typ=float("%.3e" % np.median(h[tg < 60]/h0)),
                time=round(time.time() - t0, 1))

if __name__ == "__main__":
    tasks = [("A", (2.5, 0.05)), ("A", (3.0, 0.05)),
             ("B", (2.5, 0.05, 0.0, 0)), ("B", (3.0, 0.05, 0.0, 0)), ("B", (3.5, 0.05, 0.0, 0)),
             ("B", (2.5, 0.035, 0.0, 0)), ("B", (3.0, 0.05, 1.0, 0)), ("B", (3.0, 0.05, 0.0, 1))]
    def run(t):
        return partA(t[1]) if t[0] == "A" else partB(t[1])
    with Pool(8) as pool:
        for r in pool.imap_unordered(run, tasks):
            print(json.dumps(r), flush=True)
