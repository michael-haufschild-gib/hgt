#!/usr/bin/env python3
import math
import random
from statistics import mean

import mpmath as mp
import numpy as np

mp.mp.dps = 35


def trapz(y, x):
    return float(np.trapezoid(np.asarray(y, dtype=float), np.asarray(x, dtype=float)))


def node_gl_partition(r, beta=1.0):
    xs = np.linspace(-6.0, 6.0, 2401)
    v = 0.5 * r * xs * xs + 0.25 * xs**4
    return trapz(np.exp(-beta * v), xs)


def node_validation():
    rng = np.random.default_rng(20260621)
    rows = []
    for disorder in [0.0, 0.15, 0.35, 0.70, 1.10]:
        masses = 0.35 + disorder * rng.normal(size=600)
        masses = np.clip(masses, -1.5, 2.5)
        zs = np.array([node_gl_partition(r) for r in masses])
        annealed = math.log(float(np.mean(zs)))
        quenched = float(np.mean(np.log(zs)))
        rows.append(
            {
                "disorder": disorder,
                "annealed_logZ": annealed,
                "quenched_ElogZ": quenched,
                "jensen_gap": annealed - quenched,
                "sd_logZ": float(np.std(np.log(zs))),
            }
        )
    return rows


def levenshtein(a, b):
    prev = list(range(len(b) + 1))
    for i, ca in enumerate(a, 1):
        cur = [i]
        for j, cb in enumerate(b, 1):
            cur.append(
                min(
                    prev[j] + 1,
                    cur[j - 1] + 1,
                    prev[j - 1] + (ca != cb),
                )
            )
        prev = cur
    return prev[-1]


def first_primes(limit):
    primes = []
    n = 2
    while len(primes) < limit:
        for p in primes:
            if p * p > n:
                break
            if n % p == 0:
                break
        else:
            primes.append(n)
            n += 1
            continue
        if all(n % p for p in primes if p * p <= n):
            primes.append(n)
        n += 1
    return primes


PRIMES = first_primes(140)


def zeta_logder(s):
    h = mp.mpf("1.0e-5")
    z0 = mp.zeta(s)
    dz = (mp.zeta(s + h) - mp.zeta(s - h)) / (2 * h)
    return complex(dz / z0)


def finite_logder(s, pcount=80, phases=None):
    total = 0j
    for idx, p in enumerate(PRIMES[:pcount]):
        logp = math.log(p)
        phase = 1.0 if phases is None else phases[idx]
        x = phase * complex(mp.e ** (-s * logp))
        total += -logp * x / (1.0 - x)
    return total


def gamma_part(s):
    return complex(0.5 * mp.digamma(s / 2.0) - 0.5 * mp.log(mp.pi))


def robust_z(values):
    arr = np.asarray(values, dtype=float)
    med = float(np.median(arr))
    q25, q75 = np.percentile(arr, [25, 75])
    scale = float(q75 - q25)
    if scale < 1e-9:
        scale = float(np.std(arr) + 1e-9)
    return (arr - med) / scale


def phase_defect_grid(kind, sigmas, ts, pcount=80, seed=0):
    phases = None
    if kind == "random":
        rng = random.Random(seed)
        phases = [complex(math.cos(rng.random() * 2 * math.pi), math.sin(rng.random() * 2 * math.pi)) for _ in PRIMES]
    raw = []
    for sigma in sigmas:
        row = []
        for t in ts:
            s = mp.mpc(sigma, t)
            g = gamma_part(s)
            if kind == "true":
                p = zeta_logder(s)
            elif kind == "finite":
                p = finite_logder(s, pcount=pcount)
            elif kind == "random":
                p = finite_logder(s, pcount=pcount, phases=phases)
            else:
                raise ValueError(kind)
            eps = 1e-14
            defect = max(math.log(abs(g) + eps), math.log(abs(p) + eps)) - math.log(abs(g + p) + eps)
            row.append(defect)
        raw.append(row)
    arr = np.asarray(raw, dtype=float)
    z = robust_z(arr.ravel()).reshape(arr.shape)
    return np.clip(z, -6, 6)


def aq_gap(values, beta=1.0, axis=0):
    # Axis names the disorder samples. For axis=0, sigma lanes are samples and t is the internal partition coordinate.
    arr = np.asarray(values, dtype=float)
    if axis == 0:
        samples = arr
    else:
        samples = arr.T
    zs = np.mean(np.exp(beta * samples), axis=1)
    annealed = math.log(float(np.mean(zs)))
    quenched = float(np.mean(np.log(zs)))
    return annealed - quenched, annealed, quenched, float(np.std(np.log(zs)))


def ht_experiment():
    sigmas = [0.30, 0.40, 0.50, 0.60, 0.70, 1.20]
    windows = [(100.0, 170.0), (500.0, 570.0)]
    betas = [0.7, 1.0, 1.4]
    rows = []
    for w0, w1 in windows:
        ts = np.linspace(w0, w1, 84)
        grids = {
            "true": phase_defect_grid("true", sigmas, ts),
            "finite80": phase_defect_grid("finite", sigmas, ts, pcount=80),
            "finite30": phase_defect_grid("finite", sigmas, ts, pcount=30),
            "finite130": phase_defect_grid("finite", sigmas, ts, pcount=130),
            "random": phase_defect_grid("random", sigmas, ts, pcount=80, seed=int(w0)),
        }
        for beta in betas:
            for kind, grid in grids.items():
                lane_gap, lane_a, lane_q, lane_sd = aq_gap(grid, beta=beta, axis=0)
                time_gap, time_a, time_q, time_sd = aq_gap(grid, beta=beta, axis=1)
                center = float(np.mean(grid[2]))
                edge = float((np.mean(grid[0]) + np.mean(grid[4])) / 2.0)
                rows.append(
                    {
                        "window": f"{int(w0)}-{int(w1)}",
                        "beta": beta,
                        "kind": kind,
                        "lane_gap": lane_gap,
                        "time_gap": time_gap,
                        "view_ratio": lane_gap / (time_gap + 1e-12),
                        "lane_logZ_sd": lane_sd,
                        "center_minus_edge": center - edge,
                    }
                )
    return rows


def xi_logder(s):
    return gamma_part(s) + zeta_logder(s)


def period_proxy_matrix(values):
    vals = np.asarray(values, dtype=complex)
    amp = np.log1p(np.abs(vals))
    phase = np.unwrap(np.angle(vals))
    amp = (amp - np.mean(amp)) / (np.std(amp) + 1e-9)
    dphase = np.gradient(phase)
    dphase = (dphase - np.mean(dphase)) / (np.std(dphase) + 1e-9)
    x = np.vstack([amp, dphase])
    return (x @ x.T) / x.shape[1]


def period_domain_experiment():
    # Target from docs/consolidated/08-conjectures-required.md:
    # C-2026-06-18-001 (`D_∞` period-domain): RH iff F_zeta is elliptic with
    # period point in the interior of D_∞; off-line zero = hyperbolic/boundary direction.
    zeros = [float(mp.im(mp.zetazero(n))) for n in [20, 21, 22, 60, 61, 62]]
    delta = 0.14
    half_width = 0.30
    rows = []
    for field in ["xi", "bare", "finite_gamma", "random_gamma"]:
        mats = []
        for idx, z0 in enumerate(zeros):
            ts = np.linspace(z0 - half_width, z0 + half_width, 28)
            vals = []
            rng = random.Random(9100 + idx)
            phases = [complex(math.cos(rng.random() * 2 * math.pi), math.sin(rng.random() * 2 * math.pi)) for _ in PRIMES]
            for sign in [-1, 1]:
                sigma = 0.5 + sign * delta
                lane = []
                for t in ts:
                    s = mp.mpc(sigma, t)
                    if field == "xi":
                        lane.append(xi_logder(s))
                    elif field == "bare":
                        lane.append(zeta_logder(s))
                    elif field == "finite_gamma":
                        lane.append(gamma_part(s) + finite_logder(s, pcount=90))
                    elif field == "random_gamma":
                        lane.append(gamma_part(s) + finite_logder(s, pcount=90, phases=phases))
                vals.extend(lane)
            mats.append(period_proxy_matrix(vals))
        mat_avg = sum(mats) / len(mats)
        eig_avg = np.linalg.eigvalsh(mat_avg)
        annealed_logdet = float(np.log(np.linalg.det(mat_avg) + 1e-18))
        quenched_logdet = float(np.mean([np.log(np.linalg.det(m) + 1e-18) for m in mats]))
        quenched_min = float(np.mean([np.min(np.linalg.eigvalsh(m)) for m in mats]))
        worst_min = float(np.min([np.min(np.linalg.eigvalsh(m)) for m in mats]))
        rows.append(
            {
                "field": field,
                "annealed_logdet": annealed_logdet,
                "quenched_logdet": quenched_logdet,
                "aq_logdet_gap": annealed_logdet - quenched_logdet,
                "annealed_min_eig": float(eig_avg[0]),
                "quenched_mean_min_eig": quenched_min,
                "worst_sample_min_eig": worst_min,
            }
        )
    return rows


def summarize(rows):
    out = []
    for window in sorted(set(r["window"] for r in rows)):
        for beta in [0.7, 1.0, 1.4]:
            sub = [r for r in rows if r["window"] == window and abs(r["beta"] - beta) < 1e-9]
            t = next(r for r in sub if r["kind"] == "true")
            finite_max = max(r["lane_gap"] for r in sub if r["kind"].startswith("finite"))
            finite_min_time = min(r["time_gap"] for r in sub if r["kind"].startswith("finite"))
            rnd = next(r for r in sub if r["kind"] == "random")
            out.append(
                {
                    "window": window,
                    "beta": beta,
                    "true_lane_gap": t["lane_gap"],
                    "finite_max_lane_gap": finite_max,
                    "random_lane_gap": rnd["lane_gap"],
                    "true_time_gap": t["time_gap"],
                    "finite_min_time_gap": finite_min_time,
                    "random_time_gap": rnd["time_gap"],
                    "true_view_ratio": t["view_ratio"],
                    "true_center_minus_edge": t["center_minus_edge"],
                }
            )
    return out


if __name__ == "__main__":
    print("NODE VALIDATION: finite GL partition, annealed log E Z vs quenched E log Z")
    for r in node_validation():
        print(
            "disorder={disorder:.2f} annealed={annealed_logZ:.6f} quenched={quenched_ElogZ:.6f} "
            "gap={jensen_gap:.6f} sd_logZ={sd_logZ:.6f}".format(**r)
        )

    target = "annealed_quenched_gl_partition_disorder"
    attempts = [
        "annealed_quenched_phase_partition_zeta_logderivative",
        "replica_free_energy_random_phase_euler_weld",
        "sample_window_selfaveraging_phase_defect",
    ]
    print("\nSTEP 8 LEVENSHTEIN")
    for a in attempts:
        print(f"{a}: {levenshtein(target, a)}")
    chosen = min(attempts, key=lambda a: levenshtein(target, a))
    print(f"chosen={chosen}")

    print("\nTARGET TOPIC")
    print("docs/consolidated/08-conjectures-required.md line 134: C-2026-06-18-001 (`D_∞` period-domain): RH iff F_zeta elliptic with period point in the interior of D_infty; off-line zero = hyperbolic/boundary direction.")

    print("\nHT TRANSFER A: quenched/annealed gap of phase-defect partition")
    rows = ht_experiment()
    for s in summarize(rows):
        print(
            "window={window} beta={beta:.1f} true_lane={true_lane_gap:.6f} "
            "finite_max_lane={finite_max_lane_gap:.6f} random_lane={random_lane_gap:.6f} "
            "true_time={true_time_gap:.6f} finite_min_time={finite_min_time_gap:.6f} "
            "random_time={random_time_gap:.6f} ratio={true_view_ratio:.2f} "
            "center_edge={true_center_minus_edge:.4f}".format(**s)
        )

    print("\nHT TRANSFER B (target-specific): D_infty period-proxy interior score, annealed vs quenched")
    for r in period_domain_experiment():
        print(
            "field={field} annealed_logdet={annealed_logdet:.6f} quenched_logdet={quenched_logdet:.6f} "
            "gap={aq_logdet_gap:.6f} annealed_min={annealed_min_eig:.6f} "
            "quenched_mean_min={quenched_mean_min_eig:.6f} worst_min={worst_sample_min_eig:.6f}".format(**r)
        )
