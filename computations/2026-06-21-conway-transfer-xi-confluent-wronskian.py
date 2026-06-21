#!/usr/bin/env python3
"""
Step 8 transfer script.

NODE script:
  coalescing y-nodes in a TP kernel determinant.

Minimal transfer selected by Levenshtein:
  coalescing t-nodes in a critical-line Xi derivative/evaluation determinant.

This tests a continuum/differential object on C, not discrete zeta values.
The raw multi-node determinant is expected to collapse at the Vandermonde
rate; the normalized determinant should tend to the confluent Wronskian.
"""

import mpmath as mp

mp.mp.dps = 70


def xi_completed(s):
    return mp.mpf("0.5") * s * (s - 1) * mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def Xi_line(t):
    return mp.re(xi_completed(mp.mpf("0.5") + 1j * t))


def deriv(order, t):
    return mp.diff(Xi_line, t, order)


def det_matrix(mat):
    return mp.det(mp.matrix(mat))


def vandermonde(vals):
    prod = mp.mpf(1)
    for i in range(len(vals)):
        for j in range(i + 1, len(vals)):
            prod *= vals[j] - vals[i]
    return prod


def evaluation_derivative_matrix(t_nodes, n):
    return [[deriv(i, t) for t in t_nodes] for i in range(n)]


def confluent_target(t0, n):
    return det_matrix([[deriv(i + j, t0) / mp.factorial(j) for j in range(n)] for i in range(n)])


def slope(xs, ys):
    xbar = sum(xs) / len(xs)
    ybar = sum(ys) / len(ys)
    return sum((x - xbar) * (y - ybar) for x, y in zip(xs, ys)) / sum((x - xbar) ** 2 for x in xs)


def run_case(t0, n=4):
    offsets = [mp.mpf(0), mp.mpf(1), mp.mpf(2), mp.mpf(4)]
    target = confluent_target(t0, n)
    exponent = n * (n - 1) // 2
    offset_v = vandermonde(offsets)
    print(f"case t0={mp.nstr(t0, 10)} n={n}")
    print(f"  expected Vandermonde exponent={exponent}")
    print(f"  confluent Wronskian target={mp.nstr(target, 16)}")
    print("  eps raw_abs normalized rel_error")
    log_eps = []
    log_abs = []
    last_raw = None
    last_eps = None
    for eps in [mp.mpf("1e-1"), mp.mpf("5e-2"), mp.mpf("2e-2"), mp.mpf("1e-2"), mp.mpf("5e-3")]:
        nodes = [t0 + eps * r for r in offsets]
        raw = det_matrix(evaluation_derivative_matrix(nodes, n))
        normalized = raw / vandermonde(nodes)
        rel = abs(normalized - target) / max(abs(target), mp.mpf("1e-80"))
        print(f"  {mp.nstr(eps, 3):>6} {mp.nstr(abs(raw), 12):>16} {mp.nstr(normalized, 16):>22} {mp.nstr(rel, 6)}")
        log_eps.append(mp.log(eps))
        log_abs.append(mp.log(abs(raw)))
        last_raw = raw
        last_eps = eps
    print(f"  estimated raw slope={mp.nstr(slope(log_eps, log_abs), 10)}")
    wrong_low = last_raw / (last_eps ** (exponent - 1) * offset_v)
    correct = last_raw / (last_eps ** exponent * offset_v)
    wrong_high = last_raw / (last_eps ** (exponent + 1) * offset_v)
    print("  nearby false normalizations at smallest eps:")
    print(f"    exponent {exponent - 1}: {mp.nstr(wrong_low, 12)}  (false -> 0)")
    print(f"    exponent {exponent}: {mp.nstr(correct, 12)}  (correct)")
    print(f"    exponent {exponent + 1}: {mp.nstr(wrong_high, 12)}  (false -> blows up)")
    print()


def main():
    print("Step 8 transfer: critical-line Xi confluent Wronskian")
    print("function: Xi_line(t)=xi(1/2+i t), real part")
    print("matrix rows: derivatives order 0..n-1; columns: coalescing t-nodes")
    print()
    for t0 in [mp.mpf("10.0"), mp.mpf("14.13"), mp.mpf("20.0")]:
        run_case(t0)
    print("Interpretation key:")
    print("  If the only effect is Vandermonde collapse with a stable Wronskian limit,")
    print("  then the transfer reduces to classical confluent determinant calculus.")
    print("  A non-reducing signal would have to appear in the Wronskian target landscape,")
    print("  not in the raw coalescing determinant.")


if __name__ == "__main__":
    main()
