# Extremal prime-blind certificate: min tr(Q0 X) s.t. X >= 0, tr(G X) = 1, tr(S_n X) = 0 (2 <= n <= e^L).
# Compare even (mu=0) and odd (mu=1) data and the zeta pole datum. Output rank of X, overlap, g*(x) samples, spectrum h*(r).
import numpy as np, cvxpy as cp, json, sys
from threshold2 import setup
from weilform import B8, Bhat

def dual(L, mus, pole, hk=0.05):
    S = setup(L, mus, hk); m = S["m"]
    Q0 = S["A"] - len(mus)*np.log(np.pi)*S["G"] + pole*S["P"]
    Nmax = int(np.floor(np.exp(L)))
    X = cp.Variable((m, m), PSD=True)
    cons = [cp.trace(S["G"] @ X) == 1] + [cp.trace(S["Sx"](np.log(n)) @ X) == 0 for n in range(2, Nmax + 1)]
    prob = cp.Problem(cp.Minimize(cp.trace(Q0 @ X)), cons)
    prob.solve(solver=cp.CLARABEL, max_iter=500)
    return prob.value, X.value, S

if __name__ == "__main__":
    L = float(sys.argv[1]); hk = 0.05
    out = {}
    res = {}
    for name, mus, pole in (("even", [0.0], 0), ("odd", [1.0], 0), ("zeta", [0.0], 1)):
        val, X, S = dual(L, mus, pole, hk)
        ev, V = np.linalg.eigh(X)
        res[name] = (X, S)
        m = S["m"]; hk2 = L/(m + 3); xs = -L/2 + 2*hk2 + hk2*np.arange(m)
        # g*(x) = sum X_ij (phi_i * phi_j~)(x) on a grid
        xg = np.linspace(0, L, 201)
        gx = [float(np.sum(X*S["Sx"](x))) for x in xg]
        rg = np.linspace(0, 40, 161)
        F = hk2*np.exp(1j*np.outer(rg, xs))*Bhat(rg*hk2)[:, None]
        hr = np.real(np.einsum("ri,ij,rj->r", F, X, F.conj()))
        out[name] = dict(value=round(float(val), 6), qstar=round(float(np.exp(-val)), 5),
                         top_eigs=[float("%.3e" % e) for e in ev[::-1][:5]],
                         g_samples=[round(v, 5) for v in gx[::10]],
                         h_samples=[float("%.3e" % v) for v in hr[::8]])
    Xe, Xo = res["even"][0], res["odd"][0]
    out["overlap_even_odd"] = float(np.sum(Xe*Xo)/np.sqrt(np.sum(Xe*Xe)*np.sum(Xo*Xo)))
    Xz = res["zeta"][0]
    out["overlap_even_zeta"] = float(np.sum(Xe*Xz)/np.sqrt(np.sum(Xe*Xe)*np.sum(Xz*Xz)))
    print(json.dumps(out))
