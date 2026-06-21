import cmath
import math
import random

import mpmath as mp


mp.mp.dps = 40


def primes_upto(n):
    out = []
    for x in range(2, n + 1):
        for p in out:
            if p * p > x:
                break
            if x % p == 0:
                break
        else:
            out.append(x)
            continue
        if all(x % p for p in out if p * p <= x):
            out.append(x)
    return out


PRIMES = primes_upto(421)
RNG = random.Random(20260621)


def principal(x):
    return math.atan2(math.sin(x), math.cos(x))


def zeta_ld(s):
    s = mp.mpc(s)
    return mp.diff(mp.zeta, s) / mp.zeta(s)


def gamma_part(s):
    s = mp.mpc(s)
    return 1 / s + 1 / (s - 1) - mp.log(mp.pi) / 2 + mp.digamma(s / 2) / 2


def xi_ld(s):
    return gamma_part(s) + zeta_ld(s)


def finite_prime_ld(s, nprimes=60):
    s = complex(s)
    total = 0j
    for p in PRIMES[:nprimes]:
        q = p ** (-s)
        total += -math.log(p) * q / (1 - q)
    return total


def mirror_metrics(left, right):
    # For completed xi, FE + real symmetry gives H(1-conj(s)) = -conj(H(s)).
    # With s_L=1-conj(s_R), the anti-phase target is left ~= -conj(right).
    left = complex(left)
    right = complex(right)
    phase_diff = principal(cmath.phase(left) - cmath.phase(right.conjugate()))
    anti_phase_defect = abs(abs(phase_diff) - math.pi)
    mag_gap = abs(math.log(abs(left) + 1e-300) - math.log(abs(right) + 1e-300))
    vector_residual = abs(left + right.conjugate()) / (abs(left) + abs(right) + 1e-300)
    return anti_phase_defect, mag_gap, vector_residual


def node_phase_slip_validation():
    # Synthetic phase slips: true slips have amplitude dips; smooth diffusion and
    # wrapping artifacts create phase jumps without an independent observable.
    n = 800
    dt = 0.01
    phase = []
    unwrapped = []
    amp = []
    truth = set()
    phi = 0.0
    for i in range(n):
        t = i * dt
        phi += 0.03 + 0.015 * math.sin(2.3 * t)
        a = 1.0 + 0.03 * math.sin(7 * t)
        if i in [180, 420, 610]:
            phi += 2 * math.pi
            truth.add(i)
        if any(abs(i - j) <= 3 for j in truth):
            a *= 0.18
        # A wrapping artifact without amplitude support.
        if i == 300:
            phi += 1.7 * math.pi
        unwrapped.append(phi)
        phase.append(math.atan2(math.sin(phi), math.cos(phi)))
        amp.append(a)
    jumps = []
    for i in range(1, n):
        # Candidate detector has access to an unwrapped phase estimate; modulo
        # phase alone would hide exact 2pi slips, which is the point of the
        # independent observable check.
        jump = abs(unwrapped[i] - unwrapped[i - 1])
        if jump > 2.4:
            jumps.append(i)
    validated = [i for i in jumps if min(amp[max(0, i - 4) : min(n, i + 5)]) < 0.45]
    return len(jumps), len(validated), sorted(jumps), sorted(validated)


def evaluate_channel(name, fn, t_values, delta=0.12, phase_thr=0.18, mag_thr=0.18):
    phase_hits = 0
    mag_hits = 0
    co_hits = 0
    resid = []
    phase_only_fake = 0
    mag_only_fake = 0
    for t in t_values:
        s_left = complex(0.5 - delta, t)
        s_right = complex(0.5 + delta, t)
        left = fn(s_left)
        right = fn(s_right)
        pdef, mgap, vres = mirror_metrics(left, right)
        phase = pdef < phase_thr
        mag = mgap < mag_thr
        phase_hits += phase
        mag_hits += mag
        co_hits += phase and mag
        phase_only_fake += phase and not mag
        mag_only_fake += mag and not phase
        resid.append(vres)
    total = len(t_values)
    return {
        "name": name,
        "phase": phase_hits,
        "mag": mag_hits,
        "co": co_hits,
        "phase_only": phase_only_fake,
        "mag_only": mag_only_fake,
        "mean_resid": sum(resid) / total,
        "max_resid": max(resid),
        "total": total,
    }


def main():
    print("NODE: phase-slip detection / independent observable validation")
    jumps, validated, jump_list, valid_list = node_phase_slip_validation()
    print(f"NODE phase-only jumps={jumps} validated_by_amplitude={validated}")
    print(f"NODE jumps={jump_list}")
    print(f"NODE validated={valid_list}")
    print()
    print("TRANSFER: ResearchNode 35 Berry switch")
    print("minimal change: phase slip -> anti-phase mirror switch; independent observable -> mirror magnitude balance")
    print("method #3 reverse: test phase->magnitude and magnitude->phase, not only one direction")
    t_values = [14.02 + k * (0.28 / 80) for k in range(81)]
    t_values += [20.90 + k * (0.35 / 80) for k in range(81)]
    t_values += [25.00 + k * (0.35 / 80) for k in range(81)]
    finite_fn = lambda s: complex(gamma_part(s)) + finite_prime_ld(s, 60)
    true_fn = lambda s: xi_ld(s)
    bare_fn = lambda s: zeta_ld(s)
    gamma_fn = lambda s: gamma_part(s)

    true_rows = [
        evaluate_channel("completed_xi", true_fn, t_values),
        evaluate_channel("bare_zeta", bare_fn, t_values),
        evaluate_channel("gamma_only", gamma_fn, t_values),
        evaluate_channel("finite60_completed", finite_fn, t_values),
    ]

    # Phase-scrambled control preserves per-point |P| but breaks mirror phase.
    cache = {}

    def scrambled(s):
        key = (round(s.real, 6), round(s.imag, 6))
        if key not in cache:
            p = complex(zeta_ld(s))
            cache[key] = abs(p) * complex(math.cos(RNG.random() * 2 * math.pi), math.sin(RNG.random() * 2 * math.pi))
        return complex(gamma_part(s)) + cache[key]

    true_rows.append(evaluate_channel("phase_scrambled_completed", scrambled, t_values))

    for row in true_rows:
        print(
            "ROW",
            row["name"],
            f"phase_hits={row['phase']}/{row['total']}",
            f"mag_hits={row['mag']}/{row['total']}",
            f"co_hits={row['co']}/{row['total']}",
            f"phase_only={row['phase_only']}",
            f"mag_only={row['mag_only']}",
            f"mean_resid={row['mean_resid']:.4f}",
            f"max_resid={row['max_resid']:.4f}",
        )


if __name__ == "__main__":
    main()
