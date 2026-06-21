#!/usr/bin/env python3
import itertools
import math
import random
from statistics import median, quantiles


def gcd3(a, b, c):
    return math.gcd(math.gcd(abs(a), abs(b)), abs(c))


def greedy_balanced_prefix(atoms):
    remaining = atoms[:]
    s = 0.0
    max_abs = 0.0
    order = []
    while remaining:
        j = min(range(len(remaining)), key=lambda i: abs(s + remaining[i]))
        x = remaining.pop(j)
        order.append(x)
        s += x
        max_abs = max(max_abs, abs(s))
    return max_abs, s, order


def clustered_prefix(atoms):
    s = 0.0
    max_abs = 0.0
    for x in atoms:
        s += x
        max_abs = max(max_abs, abs(s))
    return max_abs, s


def random_prefix_stats(atoms, trials=300, seed=0):
    rng = random.Random(seed)
    vals = []
    for _ in range(trials):
        xs = atoms[:]
        rng.shuffle(xs)
        vals.append(clustered_prefix(xs)[0])
    qs = quantiles(vals, n=20)
    return min(vals), median(vals), qs[18], max(vals)


def atomize(coeffs, values):
    atoms = []
    for c, v in zip(coeffs, values):
        atoms.extend([math.copysign(v, c)] * abs(c))
    return atoms


def enumerate_best(values, H=60, keep=8):
    best = []
    for a in range(-H, H + 1):
        for b in range(-H, H + 1):
            for c in range(-H, H + 1):
                if (a, b, c) == (0, 0, 0):
                    continue
                if gcd3(a, b, c) != 1:
                    continue
                r = a * values[0] + b * values[1] + c * values[2]
                item = (abs(r), (a, b, c), r)
                if len(best) < keep:
                    best.append(item)
                    best.sort()
                elif item < best[-1]:
                    best[-1] = item
                    best.sort()
    return best


def rounded_best(true_values, H=60, digits=8, keep=5):
    rounded = [round(v, digits) for v in true_values]
    out = []
    for abs_r_round, coeffs, _ in enumerate_best(rounded, H=H, keep=keep):
        true_r = sum(c * v for c, v in zip(coeffs, true_values))
        out.append((abs_r_round, abs(true_r), coeffs))
    return out


def architectural_closed_panel():
    # Five directions at 72 degrees close exactly as roots of unity.
    dirs = [(math.cos(2 * math.pi * k / 5), math.sin(2 * math.pi * k / 5)) for k in range(5)]
    atoms = []
    for d in dirs:
        atoms.extend([d] * 20)

    def max_prefix(seq):
        x = y = 0.0
        m = 0.0
        for dx, dy in seq:
            x += dx
            y += dy
            m = max(m, math.hypot(x, y))
        return m, math.hypot(x, y)

    clustered = atoms[:]
    balanced = []
    for i in range(20):
        for k in range(5):
            balanced.append(dirs[k])
    rng = random.Random(20260621)
    random_debts = []
    for _ in range(300):
        xs = atoms[:]
        rng.shuffle(xs)
        random_debts.append(max_prefix(xs)[0])
    q = quantiles(random_debts, n=20)
    return {
        "clustered": max_prefix(clustered),
        "balanced": max_prefix(balanced),
        "random_min": min(random_debts),
        "random_median": median(random_debts),
        "random_p95": q[18],
        "random_max": max(random_debts),
    }


def relation_debt_report(label, values, H=60):
    best = enumerate_best(values, H=H, keep=6)
    rows = []
    for rank, (abs_r, coeffs, r) in enumerate(best, start=1):
        atoms = atomize(coeffs, values)
        grouped_atoms = []
        for c, v in zip(coeffs, values):
            grouped_atoms.extend([math.copysign(v, c)] * abs(c))
        clustered_m, _ = clustered_prefix(grouped_atoms)
        balanced_m, _, _ = greedy_balanced_prefix(atoms)
        rnd = random_prefix_stats(atoms, trials=300, seed=rank + 17)
        rows.append(
            {
                "rank": rank,
                "coeffs": coeffs,
                "final_abs": abs_r,
                "clustered_prefix": clustered_m,
                "balanced_prefix": balanced_m,
                "ratio": clustered_m / max(balanced_m, 1e-300),
                "random_min_med_p95_max": rnd,
            }
        )
    rounded = {d: rounded_best(values, H=H, digits=d, keep=3) for d in (6, 8, 10, 12)}
    return label, rows, rounded


def main():
    print("NODE test: assembly sequencing in a closed aperiodic-like architectural panel")
    panel = architectural_closed_panel()
    print(f"  same final closure, clustered max-prefix={panel['clustered'][0]:.6f}, final={panel['clustered'][1]:.3e}")
    print(f"  same final closure, balanced  max-prefix={panel['balanced'][0]:.6f}, final={panel['balanced'][1]:.3e}")
    print(
        "  random max-prefix min/median/p95/max="
        f"{panel['random_min']:.6f}/{panel['random_median']:.6f}/{panel['random_p95']:.6f}/{panel['random_max']:.6f}"
    )
    print(f"  order-debt ratio clustered/balanced={panel['clustered'][0] / panel['balanced'][0]:.3f}")

    l2 = math.log(2.0)
    l3 = math.log(3.0)
    corank2 = [l2 * l2, l2 * l3, l3 * l3]
    dep = [l2 * l2, l2 * l3, l2 * l2 + l2 * l3]

    for label, rows, rounded in [
        relation_debt_report("corank2(log2,log3)", corank2, H=70),
        relation_debt_report("dependent-control", dep, H=20),
    ]:
        print()
        print(f"ResearchNode mutation: {label}")
        for row in rows[:4]:
            mn, med, p95, mx = row["random_min_med_p95_max"]
            print(
                f"  rank={row['rank']} coeffs={row['coeffs']} final_abs={row['final_abs']:.3e} "
                f"clustered={row['clustered_prefix']:.3e} balanced={row['balanced_prefix']:.3e} "
                f"ratio={row['ratio']:.2f} random_min/med/p95/max={mn:.3e}/{med:.3e}/{p95:.3e}/{mx:.3e}"
            )
        print("  rounded-value top candidates: rounded_residual -> true_residual coeffs")
        for digits, rr in rounded.items():
            text = "; ".join(f"{a:.2e}->{b:.2e} {c}" for a, b, c in rr)
            print(f"    digits={digits}: {text}")

    print()
    print("Finding:")
    print("  Prefix-debt is an assembly-order artifact: it changes by large factors for the same final closure.")
    print("  For corank^(2) searches this means any path/streaming relation detector needs an assembly-order")
    print("  invariance passport; final residual belongs to the unordered coefficient vector, not to one build path.")
    print("  The dependent control has exact relations but still exhibits order debt, so low prefix debt is not")
    print("  evidence of algebraic independence and high prefix debt is not evidence against a relation.")


if __name__ == "__main__":
    main()
