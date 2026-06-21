#!/usr/bin/env python3
import cmath
import math

import numpy as np


def winding(vals):
    total = 0.0
    for a, b in zip(vals, vals[1:] + vals[:1]):
        total += cmath.phase(b / a)
    return total / (2 * math.pi)


def nematic_charge_demo(samples=720):
    theta = np.linspace(0, 2 * math.pi, samples, endpoint=False)
    polar_half = np.exp(0.5j * theta)
    nematic_tensor = np.exp(1.0j * theta)  # exp(i 2 phi), with phi=theta/2
    polar_jump = abs(polar_half[-1] / polar_half[0] - 1)
    line_closure = abs(polar_half[-1] / polar_half[0] + 1)
    return {
        "polar_lift_charge": 0.5,
        "tensor_winding": winding(list(nematic_tensor)),
        "polar_nonclosure": polar_jump,
        "line_closure_error": line_closure,
    }


def contour(radius=0.8, n=2000):
    return [radius * cmath.exp(2j * math.pi * k / n) for k in range(n)]


def integrate_connection(gauge_strength):
    pts = contour()
    total = 0j
    proxy_vals = []
    for a, b in zip(pts, pts[1:] + pts[:1]):
        z = 0.5 * (a + b)
        dz = b - a
        source = 1.0 / z
        dq = gauge_strength * 2.0 * z  # exact derivative of gauge_strength*z^2
        H = source + dq
        total += H * dz
        # A deliberately representative-sensitive "carrier proxy": antiphase cancellation score.
        proxy_vals.append(max(math.log(abs(source)), math.log(abs(dq) + 1e-300)) - math.log(abs(H)))
    return total / (2j * math.pi), float(np.mean(proxy_vals)), float(np.max(proxy_vals))


def main():
    print("NODE test: nematic half-charge is a quotient-manifold fact")
    d = nematic_charge_demo()
    print(f"  polar-vector lifted charge={d['polar_lift_charge']:.6f} (not a closed vector loop)")
    print(f"  tensor/order-parameter winding={d['tensor_winding']:.6f}")
    print(f"  polar representative nonclosure error={d['polar_nonclosure']:.6f}")
    print(f"  line-field closure error under n~-n={d['line_closure_error']:.6f}")
    print("  The same visual defect is well-defined only after declaring the order-parameter quotient.")

    print()
    print("ResearchNode mutation: carrier status under exact representative changes")
    print("  Synthetic source connection H=1/z + d(q), q=a z^2.")
    print("  Winding/source charge should stay 1; representative-sensitive carrier proxies may move.")
    rows = []
    for a in [0.0, 0.2, 0.5, 0.78, 1.0, 2.0, 5.0]:
        charge, mean_proxy, max_proxy = integrate_connection(a)
        rows.append((a, charge.real, abs(charge - 1), mean_proxy, max_proxy))
        print(
            f"    gauge={a:4.2f} charge={charge.real:.12f} charge_err={abs(charge-1):.2e} "
            f"mean_proxy={mean_proxy:+.6f} max_proxy={max_proxy:+.6f}"
        )
    drift = max(r[4] for r in rows) - min(r[4] for r in rows)
    print(f"  max-proxy drift across exact gauges={drift:.6f}")

    print()
    print("Finding:")
    print("  The carrier-status statement needs an order-parameter/quotient passport. Source charge and")
    print("  contour moments are invariant under exact representative changes, so they are geometry diagnostics.")
    print("  Any representative-sensitive phase proxy must be demoted unless it first proves quotient invariance;")
    print("  if it is quotient-invariant, it still detects source geometry rather than HT.")


if __name__ == "__main__":
    main()
