import time
from multiprocessing import Pool
import mpmath as mp

NPROC = 60
DPS = 60

def xifn(s):
    return mp.mpf('0.5')*s*(s-1)*mp.pi**(-s/2)*mp.gamma(s/2)*mp.zeta(s)

def xic(w):
    return xifn(mp.mpf('0.5') + w)

def Xi_jets(tau):
    h = mp.mpf(10)**(-6)
    v = [xic(mp.mpc(0, tau + k*h)).real for k in range(-3, 4)]
    Xi = v[3]
    d1 = (45*(v[4]-v[2]) - 9*(v[5]-v[1]) + (v[6]-v[0]))/(60*h)
    d2 = (270*(v[4]+v[2]) - 27*(v[5]+v[1]) + 2*(v[6]+v[0]) - 490*v[3])/(180*h**2)
    d3 = (-13*(v[4]-v[2]) + 8*(v[5]-v[1]) - (v[6]-v[0]))/(8*h**3)
    d4 = (-39*(v[4]+v[2]) + 12*(v[5]+v[1]) - (v[6]+v[0]) + 56*v[3])/(6*h**4)
    return Xi, d1, d2, d3, d4

def slice_check(args):
    tau, eps = args
    mp.mp.dps = DPS
    w = mp.mpc(eps, tau)
    h = mp.mpf(10)**(-10)
    d = (8*(xic(w+h)-xic(w-h)) - (xic(w+2*h)-xic(w-2*h)))/(12*h)
    f = xic(w)
    u = (d*mp.conj(f)).real
    Xi, d1, d2, d3, d4 = Xi_jets(tau)
    L1 = d1*d1 - Xi*d2
    L2 = Xi*d4 - 4*d1*d3 + 3*d2*d2
    up = eps*L1 + eps**3*L2/6
    return (float(abs(u - up)/abs(u)) if u != 0 else None, float(u > 0))

def main():
    t0 = time.time()
    pts = [(2.0 + 3.7*k, 0.02) for k in range(15)] + [(2.0 + 3.7*k, 0.05) for k in range(15)] \
        + [(2.0 + 3.7*k, 0.10) for k in range(15)]
    with Pool(NPROC) as pool:
        out = pool.map(slice_check, pts, chunksize=1)
    for epsv in (0.02, 0.05, 0.10):
        errs = [e for (e, pos), (tau, ee) in zip(out, pts) if ee == epsv and e is not None]
        print(f"eps={epsv}: max rel err of u vs (eps L1 + eps^3 L2/6): {max(errs):.3e}"
              f"  (eps^4 = {epsv**4:.1e})", flush=True)
    upos = all(pos == 1.0 for (e, pos) in out)
    print("u > 0 at all sampled slice points:", upos)
    print("DONE", time.time()-t0)

if __name__ == "__main__":
    main()
