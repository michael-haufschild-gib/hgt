#!/usr/bin/env python3
import math

import mpmath as mp
import numpy as np

mp.mp.dps = 35


def levenshtein(a, b):
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (ca != cb)))
        prev = cur
    return prev[-1]


def node_validation():
    rng = np.random.default_rng(20260621)
    rows = []
    for coupling in [0.0, 0.15, 0.35, 0.60, 0.90]:
        n = 140
        x = rng.normal(0, 0.15, size=n)
        noise = 0.62
        for _ in range(700):
            force = x - x**3
            lap = np.roll(x, 1) + np.roll(x, -1) - 2 * x
            x += 0.04 * (force + coupling * lap) + noise * math.sqrt(0.04) * rng.normal(size=n)
            x = np.clip(x, -2.5, 2.5)
        signs = np.sign(x)
        mabs = abs(float(np.mean(signs)))
        domains = int(np.sum(signs != np.roll(signs, 1)))
        corr = float(np.mean(signs * np.roll(signs, 1)))
        rows.append((coupling, mabs, domains, corr))
    return rows


def xi(s):
    return mp.mpf("0.5") * s * (s - 1) * mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def Xi(t):
    return xi(mp.mpf("0.5") + 1j * t)


def cubic_discriminant(a, b, c, d):
    return 18 * a * b * c * d - 4 * b**3 * d + b * b * c * c - 4 * a * c**3 - 27 * a * a * d * d


def jensen3_coeffs(t):
    tc = mp.taylor(lambda z: Xi(z), mp.mpf(t), 3)
    # J_3(X;t) = sum_j binom(3,j) Xi^(j)(t)/j! X^j ; taylor gives Xi^(j)/j!
    return np.array([float(mp.binomial(3, j) * mp.re(tc[j])) for j in range(4)], dtype=float)


def margin_field(nsites):
    ts = np.linspace(5.0, 80.0, nsites)
    coeffs = np.array([jensen3_coeffs(t) for t in ts])
    discs = []
    for row in coeffs:
        discs.append(cubic_discriminant(row[3], row[2], row[1], row[0]))
    discs = np.asarray(discs, dtype=float)
    # positive = hyperbolic; use log margin to keep dynamic range sane.
    margins = np.log10(np.maximum(discs, 1e-300))
    margins = (margins - np.percentile(margins, 10)) / (np.percentile(margins, 90) - np.percentile(margins, 10) + 1e-12)
    margins = np.clip(margins, 0.0, 1.0)
    return ts, coeffs, margins


def smooth_noise(rng, n, length):
    raw = rng.normal(size=n)
    if length <= 0:
        return raw / (np.std(raw) + 1e-12)
    sm = raw.copy()
    for _ in range(length):
        sm = 0.25 * np.roll(sm, 1) + 0.5 * sm + 0.25 * np.roll(sm, -1)
    return sm / (np.std(sm) + 1e-12)


def defect_count(coeffs, margins, eps, length, trials=90, shuffle_margin=False):
    rng = np.random.default_rng(9100 + int(100 * eps) + 37 * length + len(coeffs))
    n = len(coeffs)
    m = np.array(margins, copy=True)
    if shuffle_margin:
        rng.shuffle(m)
    counts = []
    domains = []
    for _ in range(trials):
        eta = smooth_noise(rng, n, length)
        # Low-margin sites get amplified perturbation; coupling length controls whether defects become domains.
        amp = eps * (0.25 + 1.75 * (1.0 - m))
        defect = []
        for i, row in enumerate(coeffs):
            pert = np.array([1.0, 1.0 + 0.45 * amp[i] * eta[i], 1.0 - 0.30 * amp[i] * eta[i], 1.0 + 0.20 * amp[i] * eta[i]])
            p = row * pert
            disc = cubic_discriminant(p[3], p[2], p[1], p[0])
            defect.append(disc < 0)
        defect = np.asarray(defect, dtype=bool)
        counts.append(int(np.sum(defect)))
        if np.any(defect):
            edges = int(np.sum(defect != np.roll(defect, 1)))
            domains.append(max(1, edges // 2))
        else:
            domains.append(0)
    return float(np.mean(counts)), float(np.mean(domains)), float(np.mean(np.asarray(counts) >= 2))


def transfer_experiment():
    rows = []
    for nsites in [12, 24, 48]:
        ts, coeffs, margins = margin_field(nsites)
        for eps in [0.8, 1.1, 1.4]:
            for length in [0, 2, 5]:
                c, d, p2 = defect_count(coeffs, margins, eps, length, shuffle_margin=False)
                cs, ds, p2s = defect_count(coeffs, margins, eps, length, shuffle_margin=True)
                rows.append((nsites, eps, length, c, d, p2, cs, ds, p2s))
    return rows


if __name__ == "__main__":
    print("NODE VALIDATION: spatial coupling turns local noise bistability into collective domains")
    for coupling, mabs, domains, corr in node_validation():
        print(f"coupling={coupling:.2f} abs_mean_sign={mabs:.4f} domains={domains} nn_corr={corr:.4f}")

    target = "spatial_coupling_noise_bistability_collective_phase_transition"
    attempts = [
        "coupled_jensen_defect_lattice_kappaminus",
        "noise_induced_jensen_tp_domain_transition",
        "spatially_coupled_nonreal_jensen_roots",
    ]
    print("\nSTEP 8 LEVENSHTEIN")
    for a in attempts:
        print(f"{a}: {levenshtein(target, a)}")
    print(f"chosen={min(attempts, key=lambda a: levenshtein(target, a))}")

    print("\nTARGET TOPIC: Jensen TP-defect = 2 kappa_minus")
    print("STEP 9 method 9: small finite Jensen-section lattices")
    print("cols: nsites eps length true_count true_domains true_p_ge2 shuffled_count shuffled_domains shuffled_p_ge2")
    for row in transfer_experiment():
        print(
            "nsites=%d eps=%.1f length=%d true_count=%.3f true_domains=%.3f true_p_ge2=%.3f "
            "shuf_count=%.3f shuf_domains=%.3f shuf_p_ge2=%.3f" % row
        )
