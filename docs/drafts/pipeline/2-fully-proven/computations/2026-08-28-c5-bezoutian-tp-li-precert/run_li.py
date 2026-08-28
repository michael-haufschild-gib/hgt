"""Experiment 4: LI route health check.

lambda_d margins for d <= 300 from the first M zeros (values equal the Lean
source germ by the proved landing theorems, so zero-side evaluation is a
legitimate value computation), plus Hankel spectra of the shifted moment
tower m_k = sum_q u_q^{k+1}, u_q = 1/(gamma^2 + 1/4)  (y = 1/4 shift).

Tail beyond gamma_M for lambda_d estimated by the RvM density integral;
reported as an uncertainty, not silently added.
"""

import json
import sys
import time
from multiprocessing import Pool

import mpmath as mp

sys.path.insert(0, ".")
import theta_common as tc

NPROC = 60
DPS = 30
NZEROS = 4000
DMAX = 300


def init():
    mp.mp.dps = DPS


def get_zero(k):
    mp.mp.dps = DPS
    return mp.nstr(mp.im(mp.zetazero(k)), DPS - 5)


def lam_partial(args):
    d, gammas_str = args
    mp.mp.dps = DPS
    s = mp.mpf(0)
    for g in gammas_str:
        gamma = mp.mpf(g)
        rho = mp.mpc(mp.mpf(1) / 2, gamma)
        s += 2 * mp.re(1 - (1 - 1 / rho) ** d)
    return d, mp.nstr(s, 30)


def main():
    t0 = time.time()
    with Pool(NPROC, initializer=init) as pool:
        gammas = pool.map(get_zero, range(1, NZEROS + 1), chunksize=8)
    print("zeros done", time.time() - t0, "last:", gammas[-1][:12], flush=True)

    with Pool(NPROC, initializer=init) as pool:
        lams = dict(pool.imap_unordered(lam_partial,
                                        [(d, gammas) for d in range(1, DMAX + 1)],
                                        chunksize=2))
    mp.mp.dps = DPS
    gM = mp.mpf(gammas[-1])
    # tail estimate: lambda tail ~ d * (log(gM/2pi) + 1) / (2 pi gM)
    tail_coeff = (mp.log(gM / (2 * mp.pi)) + 1) / (2 * mp.pi * gM)
    recs = []
    minratio = None
    for d in range(1, DMAX + 1):
        lam = mp.mpf(lams[d])
        asym = (mp.mpf(d) / 2) * (mp.log(d) - mp.log(2 * mp.pi) - 1 + mp.euler)
        tail = d * tail_coeff
        rec = {"d": d, "lambda": float(lam), "tail_est": float(tail),
               "asym": float(asym),
               "ratio": float(lam / asym) if asym > 0 else None,
               "positive_with_tail_uncertainty": bool(lam - tail > 0)}
        recs.append(rec)
        if lam <= 0:
            print("NONPOSITIVE lambda at d=", d, float(lam), flush=True)
        if asym > 0 and (minratio is None or rec["ratio"] < minratio):
            minratio = rec["ratio"]

    # shifted tower Hankel: m_k = sum 2 u^{k+1}, u = 1/(gamma^2+1/4)
    us = [1 / (mp.mpf(g) ** 2 + mp.mpf(1) / 4) for g in gammas]
    mmax = 26
    m = [sum(2 * u ** (k + 1) for u in us) for k in range(mmax + 2)]
    hankel = {}
    for N in (4, 6, 8, 10, 12):
        H0 = mp.matrix(N, N)
        H1 = mp.matrix(N, N)   # (4 m_{j+k} - m_{j+k+1}) : support-in-[0,4] side
        for j in range(N):
            for k in range(N):
                H0[j, k] = m[j + k]
                H1[j, k] = 4 * m[j + k] - m[j + k + 1]
        lo0, hi0, _ = tc.hermitian_min_max_eig(H0)
        lo1, hi1, _ = tc.hermitian_min_max_eig(H1)
        hankel[N] = {"H0_rel_log10": tc.log10_or_none(lo0 / hi0),
                     "H0_sign": int(mp.sign(lo0)),
                     "H1_rel_log10": tc.log10_or_none(lo1 / hi1),
                     "H1_sign": int(mp.sign(lo1))}
    summary = {"n_zeros": NZEROS, "gamma_max": float(gM),
               "min_ratio_lambda_over_asym": minratio,
               "all_lambda_positive": all(r["lambda"] > 0 for r in recs),
               "all_positive_with_tail": all(r["positive_with_tail_uncertainty"] for r in recs),
               "hankel": hankel, "lambda_head": recs[:12], "lambda_tail3": recs[-3:]}
    with open("li_summary.json", "w") as f:
        json.dump(summary, f, indent=1)
    with open("li_lambdas.jsonl", "w") as f:
        for r in recs:
            f.write(json.dumps(r) + "\n")
    print("DONE", time.time() - t0)
    print(json.dumps(summary)[:1500])


if __name__ == "__main__":
    main()
