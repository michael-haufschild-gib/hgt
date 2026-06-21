#!/usr/bin/env python3
"""STEP 8 HT transfer for hidden/overlapped intermediate misidentification.

Workflow change honored: three wildly different HT attempts are represented,
then the lowest-Levenshtein attempt is selected for the actual test.

Selected attempt:
    strip-rank spectroscopy of continuum differential readouts over
    (height t) x (sigma strip) matrices.
"""

import argparse
import math

import mpmath as mp
import numpy as np


ATTEMPTS = {
    "strip-rank": (
        "Replace wavelength by sigma and chemical time by height t; use SVD "
        "rank resolution on continuum matrices of log(1+|Gamma_infty+P|) and "
        "phase-defect readouts."
    ),
    "zero-shadow": (
        "Treat near-zero valleys as hidden transient species and test whether "
        "finite resolution misidentifies them as smooth background wells."
    ),
    "bohr-frequency": (
        "Treat log-prime frequencies as spectral lines and test whether finite "
        "Euler frequency peaks masquerade as a continuous analytic spectrum."
    ),
}


def levenshtein(a, b):
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[-1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def choose_attempt():
    node_core = (
        "spectroscopic matrix time wavelength hidden transient intermediate "
        "overlap detection limit blind second rank resolution"
    )
    scored = []
    for name, desc in ATTEMPTS.items():
        scored.append((levenshtein(node_core, desc.lower()), name, desc))
    scored.sort()
    return scored


def first_primes(n):
    primes = []
    candidate = 2
    while len(primes) < n:
        ok = True
        for p in primes:
            if p * p > candidate:
                break
            if candidate % p == 0:
                ok = False
                break
        if ok:
            primes.append(candidate)
        candidate += 1 if candidate == 2 else 2
    return tuple(primes)


def gamma_part(s):
    return complex(-0.5 * math.log(math.pi) + 0.5 * mp.fp.digamma(s / 2.0))


def dlog_zeta(s, h=1e-4):
    z0 = mp.fp.zeta(s)
    return complex((mp.fp.zeta(s + h) - mp.fp.zeta(s - h)) / (2.0 * h * (z0 + 1e-300)))


def dlog_finite_euler(s, primes):
    out = 0j
    for p in primes:
        q = mp.fp.power(p, -s)
        out -= math.log(p) * q / (1.0 - q)
    return complex(out)


def dlog_field(kind, s, primes):
    if kind == "true":
        return dlog_zeta(s)
    if kind == "finite":
        return dlog_finite_euler(s, primes)
    if kind == "gamma":
        return gamma_part(s)
    raise ValueError(kind)


def readout_value(g, p, readout):
    if readout == "amp":
        return math.log1p(abs(g + p))
    if readout == "phase":
        if abs(p) == 0:
            return 0.0
        defect = math.log(max(abs(g), abs(p)) + 1e-300) - math.log(abs(g + p) + 1e-300)
        return max(0.0, defect)
    if readout == "cos":
        if abs(g) * abs(p) == 0:
            return 0.0
        c = (g * p.conjugate()).real / (abs(g) * abs(p))
        return max(0.0, -float(c))
    raise ValueError(readout)


def build_matrix(kind, readout, sigmas, ts, prime_count, rng):
    primes = first_primes(prime_count)
    rows = []
    for t in ts:
        row = []
        for sigma in sigmas:
            s = complex(float(sigma), float(t))
            g = gamma_part(s)
            if kind == "gamma":
                p = 0j
            elif kind == "true":
                p = dlog_zeta(s)
            elif kind == "finite":
                p = dlog_finite_euler(s, primes)
            elif kind == "random-phase":
                base = dlog_zeta(s)
                theta = rng.uniform(-math.pi, math.pi)
                p = abs(base) * complex(math.cos(theta), math.sin(theta))
            else:
                raise ValueError(kind)
            row.append(readout_value(g, p, readout))
        rows.append(row)
    return np.array(rows, dtype=float)


def rank_stats(mat, noise=1e-6):
    centered = mat - np.median(mat, axis=0, keepdims=True)
    s = np.linalg.svd(centered, compute_uv=False)
    floor = noise * (math.sqrt(centered.shape[0]) + math.sqrt(centered.shape[1]))
    return {
        "s1": float(s[0]),
        "s2": float(s[1]) if len(s) > 1 else 0.0,
        "rank_ratio": float(s[1] / max(s[0], 1e-300)) if len(s) > 1 else 0.0,
        "rank2_snr": float(s[1] / max(floor, 1e-300)) if len(s) > 1 else 0.0,
    }


def matrix_cos(a, b):
    av = (a - np.mean(a)).ravel()
    bv = (b - np.mean(b)).ravel()
    den = float(np.linalg.norm(av) * np.linalg.norm(bv))
    if den < 1e-300:
        return 0.0
    return float(np.dot(av, bv) / den)


def selected_strip_rank(args):
    rng = np.random.default_rng(args.seed)
    sigmas = np.linspace(args.sigma_min, args.sigma_max, args.sigma_count)
    ts = np.linspace(args.t_min, args.t_max, args.t_count)
    labels = ["gamma", "true", "finite", "random-phase"]
    matrices = {}
    for readout in ["amp", "phase", "cos"]:
        for lab in labels:
            matrices[(lab, readout)] = build_matrix(lab, readout, sigmas, ts, args.prime_count, rng)

    print("STEP8 HT hidden-intermediate resolution")
    print("STEP9 method: 3 = Reverse it")
    print("Reverse question: when does finite/merged readout masquerade as the true analytic component?")
    print(f"window=[{args.t_min},{args.t_max}] sigma=[{args.sigma_min},{args.sigma_max}] prime_count={args.prime_count}")
    print("attempt distances:")
    for dist, name, desc in choose_attempt():
        marker = "SELECTED" if name == "strip-rank" else "not-selected"
        print(f"  {name}: levenshtein={dist} {marker}; {desc}")

    print("\nRank resolution by readout")
    for readout in ["amp", "phase", "cos"]:
        print(f"readout={readout}")
        for lab in labels:
            st = rank_stats(matrices[(lab, readout)], noise=args.noise)
            med = float(np.median(matrices[(lab, readout)]))
            p90 = float(np.quantile(matrices[(lab, readout)], 0.90))
            print(
                f"  {lab:12s} median={med:.5g} p90={p90:.5g} "
                f"rank_ratio={st['rank_ratio']:.5g} rank2_snr={st['rank2_snr']:.5g}"
            )

    print("\nTrue-vs-finite centered matrix cosine")
    for readout in ["amp", "phase", "cos"]:
        c_tf = matrix_cos(matrices[("true", readout)], matrices[("finite", readout)])
        c_tr = matrix_cos(matrices[("true", readout)], matrices[("random-phase", readout)])
        masquerade = c_tf > 0.80
        print(
            f"readout={readout}: cos(true,finite)={c_tf:.5g} "
            f"cos(true,random-phase)={c_tr:.5g} finite_masquerade={int(masquerade)}"
        )

    print("\nDetection-limit clipping of phase readout")
    for clip in [0.0, 0.02, 0.05, 0.10, 0.20]:
        true_clip = np.where(matrices[("true", "phase")] < clip, 0.0, matrices[("true", "phase")])
        fin_clip = np.where(matrices[("finite", "phase")] < clip, 0.0, matrices[("finite", "phase")])
        st_t = rank_stats(true_clip, noise=args.noise)
        st_f = rank_stats(fin_clip, noise=args.noise)
        frac_t = float(np.mean(true_clip > 0))
        frac_f = float(np.mean(fin_clip > 0))
        print(
            f"clip={clip:.2f}: true_frac={frac_t:.4f} true_rank2={st_t['rank2_snr']:.4g} "
            f"finite_frac={frac_f:.4f} finite_rank2={st_f['rank2_snr']:.4g}"
        )


def line_values(kind, sigma, ts, primes):
    vals = []
    for t in ts:
        s = complex(float(sigma), float(t))
        vals.append(math.log1p(abs(dlog_field(kind, s, primes))))
    return np.array(vals, dtype=float)


def nearest_distances(fine_ts, coarse_ts, mask):
    marked = fine_ts[mask]
    if len(marked) == 0:
        return np.array([], dtype=float)
    return np.min(np.abs(marked[:, None] - coarse_ts[None, :]), axis=1)


def selected_zero_shadow(args):
    primes = first_primes(args.prime_count)
    fine_ts = np.linspace(args.t_min, args.t_max, args.fine_count)
    coarse_ts = np.linspace(args.t_min, args.t_max, args.t_count)
    print("STEP8 HT hidden-intermediate resolution")
    print("STEP9 method: 3 = Reverse it")
    print("Selected lowest-Levenshtein attempt: zero-shadow")
    print("Reverse question: when do unresolved true zero/pole shadows make finite/smooth readout masquerade as true?")
    print(f"window=[{args.t_min},{args.t_max}] prime_count={args.prime_count} fine_count={args.fine_count} coarse_count={args.t_count}")
    print("attempt distances:")
    scored = choose_attempt()
    selected_name = scored[0][1]
    for dist, name, desc in scored:
        marker = "SELECTED" if name == selected_name else "not-selected"
        print(f"  {name}: levenshtein={dist} {marker}; {desc}")

    print("\nZero-shadow resolution")
    print("columns: sigma kind fine_q99 coarse_q99 fine_max coarse_max peak_capture finite_masquerade")
    for sigma in [0.3, 0.5, 0.7, 1.2]:
        true_fine = line_values("true", sigma, fine_ts, primes)
        true_coarse = line_values("true", sigma, coarse_ts, primes)
        fin_fine = line_values("finite", sigma, fine_ts, primes)
        fin_coarse = line_values("finite", sigma, coarse_ts, primes)
        for kind, fine, coarse, other_coarse in [
            ("true", true_fine, true_coarse, fin_coarse),
            ("finite", fin_fine, fin_coarse, true_coarse),
        ]:
            fine_q99 = float(np.quantile(fine, 0.99))
            coarse_q99 = float(np.quantile(coarse, 0.99))
            fine_max = float(np.max(fine))
            coarse_max = float(np.max(coarse))
            peak_capture = coarse_max / max(fine_max, 1e-300)
            # If coarse true distribution is closer to finite than its fine self, finite can masquerade.
            if kind == "true":
                grid = np.linspace(min(true_fine.min(), true_coarse.min(), fin_coarse.min()), max(true_fine.max(), true_coarse.max(), fin_coarse.max()), 80)
                hist_fine, _ = np.histogram(true_fine, bins=grid, density=True)
                hist_coarse, _ = np.histogram(true_coarse, bins=grid, density=True)
                hist_fin, _ = np.histogram(fin_coarse, bins=grid, density=True)
                d_self = float(np.linalg.norm(hist_coarse - hist_fine))
                d_fin = float(np.linalg.norm(hist_coarse - hist_fin))
                masquerade = d_fin < d_self
            else:
                masquerade = False
            print(
                f"sigma={sigma:.1f} {kind:6s} fine_q99={fine_q99:.5g} coarse_q99={coarse_q99:.5g} "
                f"fine_max={fine_max:.5g} coarse_max={coarse_max:.5g} "
                f"peak_capture={peak_capture:.5g} finite_masquerade={int(masquerade)}"
            )

        threshold = float(np.quantile(fin_fine, 0.99))
        mask = true_fine > threshold
        dists = nearest_distances(fine_ts, coarse_ts, mask)
        miss_frac = float(np.mean(dists > ((args.t_max - args.t_min) / max(args.t_count - 1, 1)) / 2.0)) if len(dists) else 0.0
        print(
            f"sigma={sigma:.1f} true_above_finite99_frac={float(np.mean(mask)):.5g} "
            f"median_nearest_coarse_dt={float(np.median(dists)) if len(dists) else 0.0:.5g} "
            f"miss_frac={miss_frac:.5g}"
        )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--t-min", type=float, default=100.0)
    parser.add_argument("--t-max", type=float, default=170.0)
    parser.add_argument("--sigma-min", type=float, default=0.2)
    parser.add_argument("--sigma-max", type=float, default=0.8)
    parser.add_argument("--sigma-count", type=int, default=22)
    parser.add_argument("--t-count", type=int, default=140)
    parser.add_argument("--fine-count", type=int, default=2400)
    parser.add_argument("--prime-count", type=int, default=160)
    parser.add_argument("--noise", type=float, default=1e-4)
    parser.add_argument("--seed", type=int, default=20260621)
    args = parser.parse_args()
    selected_name = choose_attempt()[0][1]
    if selected_name == "zero-shadow":
        selected_zero_shadow(args)
    elif selected_name == "strip-rank":
        selected_strip_rank(args)
    else:
        selected_zero_shadow(args)


if __name__ == "__main__":
    main()
