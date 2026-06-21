import importlib.util
import pathlib

import mpmath as mp


mp.mp.dps = 50

BASE = pathlib.Path(__file__).with_name("2026-06-21-conway-poincare-contour-root-gate.py")
spec = importlib.util.spec_from_file_location("root_gate", BASE)
root_gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(root_gate)


def main():
    zero1 = mp.mpf("14.134725141734693790457251983562")
    print("STEP12 battery: contour root/event gate distance sweep")
    print("ResearchNode 21: contour certification")
    print("fixed mesh tests use true off-line rectangles just to the right of the critical line")
    print("true winding is 0 in every row; transport_count should be 0")
    print()
    for eps in [mp.mpf("0.1"), mp.mpf("0.03"), mp.mpf("0.01"), mp.mpf("0.003"), mp.mpf("0.001"), mp.mpf("0.0005")]:
        rect = (float(mp.mpf("0.5") + eps), 0.62, float(zero1 - mp.mpf("0.11")), float(zero1 + mp.mpf("0.11")))
        row_bits = [f"eps={float(eps):.4g}"]
        for n in [8, 32, 64]:
            pts = root_gate.boundary(rect, n)
            wind, max_jump, min_abs, _ = root_gate.winding_from_points(pts)
            count = root_gate.transport_count_from_points(pts)
            row_bits.append(
                f"n{n}:wind={wind:+.1f},tc={float(mp.re(count)):+.3f},jump={max_jump:.3f},minxi={min_abs:.1e}"
            )
        adap_pts = root_gate.adaptive_boundary(rect, coarse_n=6, tol=0.05)
        adap_count = root_gate.transport_count_from_points(adap_pts)
        row_bits.append(f"adap_pts={len(adap_pts)},adap_tc={float(mp.re(adap_count)):+.4f}")
        print(" | ".join(row_bits))


if __name__ == "__main__":
    main()
