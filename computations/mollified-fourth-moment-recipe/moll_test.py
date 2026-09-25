import numpy as np, time, sys
from math import log
rng = np.random.default_rng(1)
T = 1.0e6; NPTS = 400000
t = rng.uniform(T, 2*T, NPTS)

def theta(t):
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)

def Zrs(t):
    a = np.sqrt(t/(2*np.pi)); N = np.floor(a).astype(int); p = a - N
    th = theta(t); S = np.zeros_like(t); Nmax = int(N.max())
    n = np.arange(1, Nmax+1)
    for k in range(0, Nmax, 32):
        nn = n[k:k+32]
        mask = (nn[None,:] <= N[:,None])
        S += (mask * np.cos(th[:,None] - t[:,None]*np.log(nn)[None,:]) / np.sqrt(nn)[None,:]).sum(axis=1)
    C0 = np.cos(2*np.pi*(p*p - p - 1/16)) / np.cos(2*np.pi*p)
    return 2*S + (-1.0)**(N-1) * a**(-0.5) * C0, th

t0 = time.time()
Z, th = Zrs(t)
zeta = Z * np.exp(-1j*th)
print("RS done", time.time()-t0, "E|zeta|^2 =", np.mean(np.abs(zeta)**2), " expected ~", np.log(1.5*T/(2*np.pi)) + 2*0.5772156649 - 1, flush=True)

# arithmetic functions
def mobius_lambda(y):
    mu = np.ones(y+1, dtype=int); lam = np.zeros(y+1)
    isp = np.ones(y+1, dtype=bool); isp[:2] = False
    for p in range(2, y+1):
        if isp[p]:
            isp[p*p::p] = False
            mu[p::p] *= -1; mu[p*p::p*p] = 0
            q = p
            while q <= y:
                lam[q] = np.log(p); q *= p
    return mu, lam

def E1(x):
    # exponential integral via numerical integration
    u = np.linspace(x, x+60, 200001); return np.trapz(np.exp(-u)/u, u)

for theta_exp in [0.3, 0.4, 0.5]:
    y = int(T**theta_exp)
    mu, lam = mobius_lambda(y)
    ly = np.log(y)
    Psi = np.zeros(NPTS, dtype=complex); H = np.zeros(NPTS, dtype=complex)
    for h in range(1, y+1):
        if mu[h] != 0:
            Psi += mu[h] * (np.log(y/h)/ly) * h**-0.5 * np.exp(-1j*t*np.log(h))
        if lam[h] > 0:
            H += (lam[h]/ly) * h**-0.5 * np.exp(-1j*t*np.log(h))
    ZP = zeta * Psi; W = ZP - 1; Tail = W - H
    m2 = np.mean(np.abs(W)**2); m4 = np.mean(np.abs(W)**4)
    h2 = np.mean(np.abs(H)**2); h4 = np.mean(np.abs(H)**4)
    tl2 = np.mean(np.abs(Tail)**2); tl4 = np.mean(np.abs(Tail)**4)
    cross = np.mean(H*np.conj(Tail))
    print(f"theta={theta_exp} y={y}")
    print(f"  E[zetaPsi]={np.mean(ZP):.4f}   E|zetaPsi|^2={np.mean(np.abs(ZP)**2):.4f}  (1+1/theta={1+1/theta_exp:.4f})")
    print(f"  E W={np.mean(W):.4f}  E W^2={np.mean(W**2):.4f}  E|W|^2={m2:.4f}  E|W|^4={m4:.4f}  kurt=E|W|^4/(E|W|^2)^2={m4/m2**2:.4f} (Gauss 2)")
    print(f"  Gaussian pred E|zetaPsi|^4 = {1+4*m2+2*m2**2:.4f}   actual = {np.mean(np.abs(ZP)**4):.4f}")
    print(f"  E log|zetaPsi|^2 = {np.mean(np.log(np.abs(ZP)**2)):.4f}   E1(1/E|W|^2) = {E1(1/m2):.4f}   log E|zetaPsi|^2 = {np.log(np.mean(np.abs(ZP)**2)):.4f}")
    print(f"  E log|zeta|^2 = {np.mean(np.log(np.abs(zeta)**2)):.4f}   E log|Psi|^2 = {np.mean(np.log(np.abs(Psi)**2)):.4f}")
    print(f"  head: E|H|^2={h2:.4f} (1/2)  kurt={h4/h2**2:.4f} (Gauss 2)   E H^2={np.mean(H**2):.4f}")
    print(f"  tail: E|Tail|^2={tl2:.4f} (1/theta-1/2={1/theta_exp-0.5:.4f})  kurt={tl4/tl2**2:.4f}  E H conj(Tail)={cross:.4f}")
    # distribution shape of |W|^2/m2: fractions beyond thresholds vs exponential law
    r = np.abs(W)**2/m2
    for c in [1,2,4,8]:
        print(f"    P(|W|^2 > {c} E|W|^2) = {np.mean(r>c):.4f}   (Gauss exp(-{c}) = {np.exp(-c):.4f})")
    sys.stdout.flush()
print("ALL DONE")
