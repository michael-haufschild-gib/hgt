import numpy as np, time, sys
rng = np.random.default_rng(7)
def theta_rs(t):
    return t/2*np.log(t/(2*np.pi)) - t/2 - np.pi/8 + 1/(48*t) + 7/(5760*t**3)
def Zrs(t):
    a = np.sqrt(t/(2*np.pi)); N = np.floor(a).astype(int); p = a - N
    th = theta_rs(t); S = np.zeros_like(t); Nmax = int(N.max()); n = np.arange(1, Nmax+1)
    for k in range(0, Nmax, 32):
        nn = n[k:k+32]; mask = (nn[None,:] <= N[:,None])
        S += (mask * np.cos(th[:,None] - t[:,None]*np.log(nn)[None,:]) / np.sqrt(nn)[None,:]).sum(axis=1)
    C0 = np.cos(2*np.pi*(p*p - p - 1/16)) / np.cos(2*np.pi*p)
    return 2*S + (-1.0)**(N-1) * a**(-0.5) * C0, th
def mobius(y):
    mu = np.ones(y+1, dtype=int); isp = np.ones(y+1, dtype=bool); isp[:2] = False
    for p in range(2, y+1):
        if isp[p]:
            isp[p*p::p] = False; mu[p::p] *= -1; mu[p*p::p*p] = 0
    return mu
for T in [1e5, 1e6, 1e7]:
    NPTS = 300000 if T < 5e6 else 200000
    t = rng.uniform(T, 2*T, NPTS); t0 = time.time()
    Z, th = Zrs(t); zeta = Z*np.exp(-1j*th)
    for te in [0.4, 0.5]:
        y = int(T**te); mu = mobius(y); ly = np.log(y)
        Psi = np.zeros(NPTS, dtype=complex)
        for h in range(1, y+1):
            if mu[h] != 0: Psi += mu[h]*(np.log(y/h)/ly)*h**-0.5*np.exp(-1j*t*np.log(h))
        ZP = zeta*Psi; m2 = np.mean(np.abs(ZP)**2); m4 = np.mean(np.abs(ZP)**4)
        print(f"T={T:.0e} theta={te} y={y}  E|zP|^2={m2:.4f} (1+1/th={1+1/te:.3f})  E|zP|^4={m4:.4f}  ratio m4/m2^2={m4/m2**2:.4f}  (1+1/th)^2={(1+1/te)**2:.3f}  E log|zP|^2={np.mean(np.log(np.abs(ZP)**2)):.4f}  P(|zP|^2<0.1)={np.mean(np.abs(ZP)**2<0.1):.4f}", flush=True)
    print("  time", time.time()-t0, flush=True)
print("ALL DONE")
