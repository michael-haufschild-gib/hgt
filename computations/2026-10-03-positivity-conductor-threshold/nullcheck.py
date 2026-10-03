# Is the no-pole extremal prime-blind certificate X* null for the zeta datum?  kappa*(w) on [0,1]; tr(Q_zeta X*); h*(gamma).
import numpy as np, cvxpy as cp, json, sys
from threshold2 import setup
from weilform import Bhat
from multiprocessing import Pool
L = float(sys.argv[1]); hk = 0.05
def dualX(w):
    S = setup(L, [0.0], hk); m = S["m"]
    Q0 = S["A"] - np.log(np.pi)*S["G"] + w*S["P"]
    Nmax = int(np.floor(np.exp(L)))
    X = cp.Variable((m, m), PSD=True)
    cons = [cp.trace(S["G"] @ X) == 1] + [cp.trace(S["Sx"](np.log(n)) @ X) == 0 for n in range(2, Nmax + 1)]
    prob = cp.Problem(cp.Minimize(cp.trace(Q0 @ X)), cons); prob.solve(solver=cp.CLARABEL, max_iter=3000)
    return w, float(prob.value), X.value
if __name__ == "__main__":
    ws = [0.0, 0.2, 0.5, 0.8, 0.9, 0.99, 1.0]
    with Pool(7) as pool:
        res = pool.map(dualX, ws)
    k0 = res[0][1]
    for w, v, X in res:
        print("w=%.2f kappa*=%+.7f  chord(1-w)*k0=%+.7f  diff=%.1e" % (w, v, (1 - w)*k0, v - (1 - w)*k0))
    S = setup(L, [0.0], hk); m = S["m"]; X0 = res[0][2]
    QZ = S["A"] - np.log(np.pi)*S["G"] + S["P"]
    print("tr(Q_zeta X*)=%.3e  tr(P X*)=%.6f  -k0=%.6f" % (np.sum(QZ*X0), np.sum(S["P"]*X0), -k0))
    hk2 = L/(m + 3); xs = -L/2 + 2*hk2 + hk2*np.arange(m)
    gam = np.load("zeros2000.npy")[:12]
    def h(r):
        F = hk2*np.exp(1j*np.outer(np.atleast_1d(r), xs))*Bhat(np.atleast_1d(r)*hk2)[:, None]
        return np.real(np.einsum("ri,ij,rj->r", F, X0, F.conj()))
    print("h*(0)=%.4f" % h(0.0)[0])
    print("h* at zeta zeros:", ["%.1e" % v for v in h(gam)])
    mid = (gam[:-1] + gam[1:])/2
    print("h* at midpoints:  ", ["%.1e" % v for v in h(mid)])
    print("h* at 2pi k/log2: ", ["%.1e" % v for v in h(2*np.pi*np.arange(1, 6)/np.log(2))])
