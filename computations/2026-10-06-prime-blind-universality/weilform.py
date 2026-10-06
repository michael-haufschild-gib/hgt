# Weil quadratic form on cubic B-spline span over [-L/2, L/2].
# For f = sum c_i B((x-x_i)/hk), g = f*f~ (supp [-L,L]), h(r) = |fhat(r)|^2:
#   Q_lam(c) = h(i/2)+h(-i/2) - g(0) log pi + (1/2pi) int h(r) Re psi(1/4+ir/2) dr - 2 sum_n lam(n) n^{-1/2} g(log n)
# and Q_Lambda(c) = sum_gamma h(gamma)  (explicit formula, RH).
import numpy as np, scipy.special as sp

def B8(u):
    # centered cardinal B-spline of order 8 (support [-4,4]) = B4*B4
    u = np.abs(np.asarray(u, float)); out = np.zeros_like(u)
    # piecewise via truncated powers: M_k(x) = 1/(k-1)! sum_j (-1)^j C(k,j) (x+k/2-j)_+^{k-1}
    x = u + 4.0
    for j in range(9):
        out += (-1)**j*sp.comb(8, j)*np.clip(x - j, 0, None)**7
    out[u >= 4.0] = 0.0
    return out/5040.0

def Bhat(w):
    w = np.asarray(w, float); s = np.ones_like(w); nz = np.abs(w) > 1e-12
    s[nz] = (np.sin(w[nz]/2)/(w[nz]/2))**4
    return s

def setup(L, hk=0.05):
    m = int(round(L/hk)) - 3; hk = L/(m + 3)
    xs = -L/2 + 2*hk + hk*np.arange(m)
    D = (xs[:, None] - xs[None, :])
    G = hk*B8(D/hk)
    def Sx(x):
        return 0.5*hk*(B8((D - x)/hk) + B8((-D - x)/hk))
    def Fvec(a):
        z = a*hk/2
        return hk*np.exp(a*xs)*(np.sinh(z)/z)**4
    u, v = Fvec(0.5), Fvec(-0.5)
    P = np.outer(u, v) + np.outer(v, u)
    # arch Toeplitz kernel K(Delta) = (hk^2/2pi) int_R Bhat(r hk)^2 Re psi(1/4+ir/2) cos(r Delta) dr
    R = 120.0/hk; dr = min(0.002, 0.2/L)
    r = np.arange(0.0, R, dr) + dr/2
    wgt = Bhat(r*hk)**2*np.real(sp.digamma(0.25 + 0.5j*r))*dr*2  # even integrand: 2*int_0^R
    lags = hk*np.arange(m)
    K = np.array([(hk**2/(2*np.pi))*np.sum(wgt*np.cos(r*dl)) for dl in lags])
    idx = np.abs(np.arange(m)[:, None] - np.arange(m)[None, :])
    A = K[idx]
    Q0 = P - np.log(np.pi)*G + A
    return dict(L=L, m=m, hk=hk, xs=xs, G=G, Sx=Sx, Q0=Q0)

def vonmangoldt(N):
    lam = np.zeros(N + 1)
    for p in range(2, N + 1):
        if all(p % q for q in range(2, int(p**0.5) + 1)):
            pk = p
            while pk <= N:
                lam[pk] = np.log(p); pk *= p
    return lam
