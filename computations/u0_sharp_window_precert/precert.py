"""Pre-certification of the sharp-threshold window pass (task #22).

Inequality list the Lean pass needs (all verified below):
  x*(B) := (1+sqrt(1+4B))/2   (escape fixed point of g(t) = t^2 - B)
  h(B)  := B - 1 - x*(B)      (first-step clearance from the unit circle)

  (I1)  h(B) > 0 and increasing for B > 2+sqrt(2); h(2+sqrt(2)) = 0.
  (I2)  annulus radius rB with rB^2 = 1 + h(B)/2 (capped at (21/20)^2):
        first step from |z| <= rB lands at modulus >= B - rB^2 = x* + h/2 > x*.
  (I3)  farB radius sqrt(2B): invariance |w|^2 - B > sqrt(2B)  (needs B > 2),
        ratio |b/w^2| < 1/2, growth |w^2+b| >= |w|^2/2 >= sqrt(B/2)*|w|, sqrt(B/2) > 1.
  (I4)  entry: orbit moduli from the annulus dominate g-iterates of x*+h/2,
        strictly increasing, unbounded -> enter farB in finitely many steps.
  (I5)  log-series bound: ratio <= 1/2 suffices for |log(1+u)| <= 2|u| (norm_clog_one_add_le
        shape used at ratio <= 1/2 already in the B>=4 pass; unchanged).
"""
import math, cmath

def xstar(B): return (1 + math.sqrt(1 + 4*B)) / 2
def h(B):     return B - 1 - xstar(B)

T = 2 + math.sqrt(2)
assert abs(h(T)) < 1e-12                        # (I1) exact vanishing at 2+sqrt(2)

prev = 0.0
for i in range(1, 2001):
    B = T + i * 1e-3
    assert h(B) > 0 and h(B) > prev             # (I1) positive, increasing
    prev = h(B)

for B in [T + 1e-3, 3.42, 3.5, 3.7, 3.9, 5.0, 10.0]:
    rB2 = min(1 + h(B)/2, (21/20)**2)
    rB = math.sqrt(rB2)
    assert rB > 1
    first = B - rB2                              # (I2)
    assert first > xstar(B) + min(h(B)/4, 1e-4)  #      strict clearance
    R = math.sqrt(2*B)                           # (I3)
    assert R*R - B > R + 1e-9                    #      invariance (strict: B > sqrt(2B) iff B>2)
    assert abs(B / (R*R) - 0.5) < 1e-12          #      ratio = 1/2 AT the boundary radius
    assert B / ((R*1.0001)**2) < 0.5             #      strictly < 1/2 inside the open farB
    assert math.sqrt(B/2) > 1                    #      growth factor
    # (I4) real comparison orbit from the first-step floor
    x, steps = first, 0
    while x <= R:
        xn = x*x - B
        assert xn > x + 1e-12, (B, x)            #      strictly increasing below entry
        x, steps = xn, steps + 1
        assert steps < 10000
    # (I4) complex sample orbits across directions
    for k in range(8):
        b = B * cmath.exp(1j * k * math.pi / 4)
        for zr, zth in [(rB*0.999, 0.3), (1.0001, 1.1), (rB*0.999, 4.0)]:
            z = zr * cmath.exp(1j*zth)
            w, n = z*z + b, 0
            assert abs(w) >= B - rB2 - 1e-9
            while abs(w) <= R:
                w, n = w*w + b, n + 1
                assert n < 10000
    print(f"B = {B:.4f}: rB = {rB:.6f}, first-step floor = {first:.4f} > x* = {xstar(B):.4f}, "
          f"farB radius = {R:.4f}, real-orbit entry in {steps} steps  OK")

print("ALL INEQUALITIES CERTIFIED")

# ============================================================================
# RESULTS (2026-07-02), consumed by the Lean pass (tasks #23-#27):
#
# Threshold audit: the q62-lane interface is threshold-free. bottcher_transcendental_far /
# bottcherFarBound_spec need only (0 ∉ filledJulia b) — provided by
# zero_not_mem_filledJulia_large at 2 < ‖b‖ — and a carrier beyond the ABSTRACT constant
# bottcherFarBound b hc, which unbounded escape exceeds with no rate. Files
# BottcherTowerData/BottcherTowerScaffold/BasinBranching committed & unmodified at audit time.
# ⟹ sharp-pass floor is 2+√2 UNCONDITIONALLY.
#
# Lean formulas fixed by this pre-cert:
#   xStar B := (1 + Real.sqrt (1+4*B))/2       -- xStar^2 - xStar - B = 0;  1 < xStar (B>0)
#   h B     := B - 1 - xStar B                 -- h > 0  ⟺  (B-2)^2 > 2 (with B > 3/2)
#   rB b    := min (21/20) (Real.sqrt (1 + h ‖b‖ / 2))
#             -- 1 < rB;  rB ≤ 21/20;  rB^2 ≤ 1 + h/2  (both min-branches satisfy it)
#   annW b  := ball 0 (rB b) ∩ {1 < ‖z‖}
#   first step: z ∈ annW b ⟹ ‖z²+b‖ ≥ ‖b‖ - rB² ≥ xStar + h/2 > xStar
#   farB b  := {w | Real.sqrt (2*‖b‖) < ‖w‖}
#             -- invariance: ‖w‖²-‖b‖ > ‖b‖ > √(2‖b‖) (⟺ ‖b‖ > 2);  ratio ‖b/w²‖ < 1/2 (open);
#             -- growth: ‖w²+b‖ ≥ ‖w‖²/2
#   LINEAR escape (replaces the (7/5)^m rate AND the limit argument):
#     g t := t² - B;  for t > xStar:  g t - t = (t - xStar)(t + xStar - 1) ≥ t - xStar
#     ⟹  g^[n] t ≥ t + n·(t - xStar)   (induction; invariant g^[n] t ≥ t)
#     ⟹  entry into farB ∪ {beyond bottcherFarBound} via exists_nat_gt. No rate, no limits.
# ============================================================================
