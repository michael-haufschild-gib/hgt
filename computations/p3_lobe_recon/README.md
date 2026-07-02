# Period-3 locus of z²+b — exact parameterization + mid-angle obstruction recon (task #41)

## The result (novel, exact, verified)

Derived — NOT looked up — the rational parameterization of the period-3 dynatomic locus of the
quadratic family `f_b(z) = z² + b`.  Two forms, both machine-verified in sympy (`verify_param.py`,
`build_param.py`):

**Trace form.**  A 3-cycle with trace `σ = γ₀+γ₁+γ₂` exists for
    b = −(σ² + σ + 2),
and the three cycle points are the roots of
    Q(z) = z³ − σ z² − (σ²+2σ+3) z + (σ³+2σ²+3σ+1).
Verified: `f_b³(z) − z ≡ 0 (mod Q)` and `gcd(f_b(z)−z, Q) = 1` (genuine period 3, not fixed
points).  Sum of roots `= σ` (Vieta).  Derivation: Lagrange resolvent on the cyclic order-3
automorphism `T:(γ₀,γ₁,γ₂)↦(γ₁,γ₂,γ₀)`, giving `uv = 4σ²+6σ+9`, `u³=(4σ²+6σ+9)(3ω−2σ)`, and
`b = (3σ−σ²−2uv)/9 = −(σ²+σ+2)`.

**Rational-point form.**  The marked-point curve `X₁(3)` (pairs `(b, marked period-3 point)`) is a
plane cubic `P(σ,r)=0` with a rational singular point at infinity `[1:1:0]` (leading form
`(X−Y)²(X+Y)`).  Projecting lines `r = σ + t` of slope 1 through it gives the genus-0
parameterization by `t ∈ ℚ(i)`:
    σ(t) = (−t³+3t−1)/(2t(t−1)),
    r(t) = (t³−2t²+3t−1)/(2t(t−1)),
    b(t) = −(t⁶−2t⁵+4t⁴−8t³+9t²−4t+1)/(4t²(t−1)²).
Verified `f_{b(t)}³(r(t)) = r(t)` and `f(r)−r = −(t²−t+1)/t ≠ 0`.  For `t ∈ ℚ(i)`, `r(t)` and
`b(t)` are exact Gaussian rationals — an on-demand generator of exact rational 3-cycles.

## Recon finding on the mid-angle lobe

Direct 3-cycle entry (`‖γ − b‖ ≤ 1`, one square-root step from a cycle point into the closed unit
disk) forces **small `‖b‖`**: sweeping `t` over Gaussian rationals, every period-3 point with a
cycle point within distance 1 of `b` had `‖b‖ < 1.6`.  So the numerically-obstructed mid-angle
lobe in the window RING `2 < ‖b‖ ≤ 2+√2` (e.g. `‖b‖ ≈ 2.2`, `arg ≈ 90°`) is NOT obstructed by a
direct-entry cycle point — the disk witness there is a **deep preimage** of a 3-cycle.  Exact
Gaussian-rational deep-preimage points are rare (each preimage step needs a square in ℚ(i)); this
is the located open sub-problem for a fully-rational deep-lobe certificate.

## Instances shipped to Lean (`formal/.../U0LobeInstances.lean`)

- `lobe_obstructed_112`: `t = 1−i` → `b = −1/4 + 5i/8` (arg 111.8°, `‖b‖=√29/8`), 3-cycle
  `−1/4+3i/4 → −3/4+i/4 → 1/4+i/4`, entry `‖y−b‖² = 1/64`.  Period-3 obstruction at a mid-angle
  (inside the main region, small `‖b‖`).
- `lobe_obstructed_ring_127`: `b = −33/25 + 44i/25` (`‖b‖ = 11/5 ∈ (2, 2+√2)`, arg 126.9°),
  2-cycle at Pythagorean `γ = −8/5 + 4i/5` (`‖γ+1‖ = 1`).  Ring obstruction at a mid-angle.
- `lobe_radial_bracket`: obstructed at `‖b‖ = 11/5`, viable at `‖b‖ = 22/5` (colinear ray).

P1/P2 checked NOT to fire at the deep interior point `b = 2.2·e^{i·90°}` (confirms it is a
genuinely period-≥3 lobe); P2 DOES reach `arg ≈ 127°` at `‖b‖ = 2.2` (its boundary curve
`b = −1+w−w²`, `‖w‖=1`), which is the ring instance above.

Scripts: `verify_param.py` (resolvent form), `param_cubic.py` (singular point), `build_param.py`
(the t-parameterization), `pick.py` / `verify_instances.py` (the shipped instances).
