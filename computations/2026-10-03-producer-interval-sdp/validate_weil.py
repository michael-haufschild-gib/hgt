import numpy as np, mpmath as mp, sys
from multiprocessing import Pool
from weilform import *
def zz(ks):
    mp.mp.dps = 20
    return [float(mp.im(mp.zetazero(k))) for k in ks]
if __name__ == "__main__":
    with Pool(8) as pool:
        gam = np.array(sum(pool.map(zz, np.array_split(np.arange(1, 2001), 64)), []))
    np.save("zeros2000.npy", gam)
    for L in (1.0, 2.0, 3.5):
        S = setup(L)
        Nmax = int(np.floor(np.exp(L)))
        lam = vonmangoldt(Nmax)
        Q = S["Q0"].copy()
        for n in range(2, Nmax + 1):
            if lam[n]: Q -= 2*lam[n]/np.sqrt(n)*S["Sx"](np.log(n))
        rng = np.random.default_rng(1)
        for trial in range(3):
            c = rng.standard_normal(S["m"])
            lhs = c @ Q @ c
            fh = (S["hk"]*np.exp(1j*np.outer(gam, S["xs"]))*Bhat(gam*S["hk"])[:, None]) @ c
            rhs = 2*np.sum(np.abs(fh)**2)
            print("L=%.1f m=%d  Q_Lambda=%.10f  sum_gamma h=%.10f  rel=%.1e" % (L, S["m"], lhs, rhs, abs(lhs-rhs)/abs(rhs)))
        ev = np.linalg.eigvalsh(Q)
        print("   min eig Q_Lambda = %.3e   (G-normalized min: %.3e)" % (ev[0], np.min(np.linalg.eigvals(np.linalg.solve(S["G"], Q)).real)))
