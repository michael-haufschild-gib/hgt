"""Resolve Hankel signs for the shifted tower at dps 150 (300 zeros suffice for sizes <= 12)."""
import sys, json
sys.path.insert(0, "/root/precert")
import mpmath as mp
import theta_common as tc
from multiprocessing import Pool

def getz(k):
    mp.mp.dps = 150
    return mp.nstr(mp.im(mp.zetazero(k)), 140)

def main():
    with Pool(100) as pool:
        gs = pool.map(getz, range(1, 301), chunksize=1)
    mp.mp.dps = 150
    us = [1/(mp.mpf(g)**2 + mp.mpf(1)/4) for g in gs]
    m = [sum(2*u**(k+1) for u in us) for k in range(28)]
    out = {}
    for N in (4, 6, 8, 10, 12):
        H0 = mp.matrix(N, N); H1 = mp.matrix(N, N)
        for j in range(N):
            for k in range(N):
                H0[j,k] = m[j+k]; H1[j,k] = 4*m[j+k] - m[j+k+1]
        lo0, hi0, _ = tc.hermitian_min_max_eig(H0)
        lo1, hi1, _ = tc.hermitian_min_max_eig(H1)
        out[N] = {"H0_rel_log10": tc.log10_or_none(lo0/hi0), "H0_sign": int(mp.sign(lo0)),
                  "H1_rel_log10": tc.log10_or_none(lo1/hi1), "H1_sign": int(mp.sign(lo1))}
        print(N, json.dumps(out[N]), flush=True)
    json.dump(out, open("/root/precert/li_hankel_hi.json", "w"), indent=1)

if __name__ == "__main__":
    main()
