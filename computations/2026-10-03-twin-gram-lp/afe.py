# Smoothed approximate functional equation for Dirichlet series with
# Lambda(s) = q^{s/2} Gamma_R(s)^d L(s) = Lambda(1-s)  (entire part, real coefficients).
# Weight g(w) = exp(a w^2 - i*beta*w), beta = d*pi/4*sign(Im s): removes the Gamma decay,
# so no cancellation; sharp cutoff for small a.
import numpy as np, scipy.special as sp

def logGR(s):
    return -0.5*s*np.log(np.pi) + sp.loggamma(s/2)

def Vmat(svals, n, d, logq, a=0.02, c=0.5, h=0.05, chunk=64, Ycut=40.0):
    """V[k, j] = (1/2πi)∫_{Re w=c} [ΓR(s_k+w)/ΓR(s_k)]^d q^{w/2} n_j^{-w} g_k(w) dw/w"""
    svals = np.atleast_1d(np.asarray(svals, complex)); n = np.asarray(n, float)
    Y = np.sqrt(Ycut/a); y = np.arange(-Y, Y + h/2, h); w = c + 1j*y
    E = np.exp(-np.outer(w, np.log(n)))           # (ny, N)
    out = np.empty((len(svals), len(n)), complex)
    for i in range(0, len(svals), chunk):
        s = svals[i:i+chunk]
        beta = d*np.pi/4*np.sign(s.imag)
        L = d*(logGR(s[:, None] + w[None, :]) - logGR(s[:, None])) + 0.5*w[None, :]*logq \
            + a*w[None, :]**2 - 1j*beta[:, None]*w[None, :]
        Q = np.exp(L)/w[None, :]*(h/(2*np.pi))
        out[i:i+chunk] = Q @ E
    return out

def theta_RS(t):
    t = np.asarray(t, float)
    return np.imag(sp.loggamma(0.25 + 0.5j*t)) - 0.5*t*np.log(np.pi)

def Zrows(t, n, d, logq, a=0.02, c=0.5, h=0.05):
    """Z_E(t) = rows @ e  for E in W (critical line), Theta = d*theta + (t/2)log q."""
    t = np.asarray(t, float); s = 0.5 + 1j*t
    V = Vmat(s, n, d, logq, a, c, h)
    Th = d*theta_RS(t) + 0.5*t*logq
    ph = np.exp(1j*(Th[:, None] - np.outer(t, np.log(n))))*n[None, :]**-0.5
    return 2*np.real(ph*V)

def defect_rows(t, n, d, logq, sigma0=1.25, a=0.02, c1=0.5, c2=0.75, h=0.05):
    """D(s) = sum e_n [ n^{-s}(1 - V(s,n)) - chi(s) n^{s-1} V(1-s,n) ],  s = sigma0 + i t.
    chi(s) = q^{1/2-s} ΓR(1-s)^d/ΓR(s)^d.  Returns complex rows."""
    t = np.asarray(t, float); s = sigma0 + 1j*t
    V1 = Vmat(s, n, d, logq, a, c1, h)
    V2 = Vmat(1 - s, n, d, logq, a, c2, h)
    logchi = (0.5 - s)*logq + d*(logGR(1 - s) - logGR(s))
    ln = np.log(n)
    A = np.exp(-np.outer(s, ln))*(1 - V1)
    B = np.exp(logchi[:, None] + np.outer(s - 1, ln))*V2
    return A - B
