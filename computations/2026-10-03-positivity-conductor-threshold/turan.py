# Discrete Turan problem on the log-integer set: max int g s.t. g PD, g(0)=1, g(log n)=0 (2<=n<=e^L), supp g in [-L,L].
# Also: precise int g* of the even/odd extremal certificates; objective value of the triangle (1-|x|/log2)_+ under the even/odd weights.
import numpy as np, cvxpy as cp, json, sys
from threshold2 import setup
from weilform import Bhat
import scipy.special as sp

def solve(L, objective, hk=0.05, mus=(0.0,)):
    S = setup(L, list(mus), hk); m = S["m"]
    hk2 = L/(m + 3); xs = -L/2 + 2*hk2 + hk2*np.arange(m)
    F0 = hk2*np.ones(m)                       # f-hat(0) vector:  int f = sum c_i hk  (Bhat(0)=1)
    H0 = np.outer(F0, F0)                     # h(0) = (int f)^2 = int g
    Nmax = int(np.floor(np.exp(L)))
    X = cp.Variable((m, m), PSD=True)
    cons = [cp.trace(S["G"] @ X) == 1] + [cp.trace(S["Sx"](np.log(n)) @ X) == 0 for n in range(2, Nmax + 1)]
    if objective == "turan":
        obj = cp.Maximize(cp.trace(H0 @ X))
    else:
        Q0 = S["A"] - len(mus)*np.log(np.pi)*S["G"]
        obj = cp.Minimize(cp.trace(Q0 @ X))
    prob = cp.Problem(obj, cons); prob.solve(solver=cp.CLARABEL, max_iter=500)
    Xv = X.value
    return dict(value=float(prob.value), intg=float(np.sum(H0*Xv)), rank_eigs=[float("%.2e" % e) for e in np.linalg.eigvalsh(Xv)[::-1][:4]])

if __name__ == "__main__":
    for L in (1.5, 2.5, 3.5):
        r = dict(L=L, turan=solve(L, "turan"), even=solve(L, "psi", mus=(0.0,)), odd=solve(L, "psi", mus=(1.0,)))
        print(json.dumps(r), flush=True)
    # triangle objective: int h(r) Re psi(1/4+mu/2+ir/2) dr/(2pi) with h = log2 * sinc^2-type: g=(1-|x|/a)_+, h(r)= a*(sin(ra/2)/(ra/2))^2
    a = np.log(2.0); r = np.arange(0, 4000, 0.001) + 0.0005
    h = a*(np.sin(r*a/2)/(r*a/2))**2
    for mu in (0.0, 1.0):
        val = 2*np.sum(h*np.real(sp.digamma(0.25 + mu/2 + 0.5j*r)))*0.001/(2*np.pi) - np.log(np.pi)
        print("triangle objective mu=%g: %.6f  -> q*=%.5f" % (mu, val, np.exp(-val)))
    print("log2 = %.8f" % np.log(2))
