# The twin pairs have a quarter floor (AGT open question 1)

- **ID:** agt-twin-quarter
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ArithmeticGaugeTheory README §7 Q1 (infimum of the Möbius exponent over the gauge torus)
- **Statement:** for a gauge point `x`, its Liouville twin `y` (`χ_y(p) = −χ_x(p)`) and its double `z` (`χ_z(p) = χ_x(p)²`),
  `F_x(s)F_y(s) = F_z(2s)`; if both twins have Möbius sums `O(N^θ)` then `F_z(2s)` continues to `Re s > θ`; at order-two
  points `Θ ≤ 2 max(θ_μ(x), θ_μ(y))`, so `max ≥ 1/4`.

## Paper proof
1. Euler factors: `Σ_e μ(p^e)χ(p^e)p^{−es} = 1 − χ(p)p^{−s}`; `(1 − χ(p)p^{−s})(1 + χ(p)p^{−s}) = 1 − χ(p)²p^{−2s}`, which is the
   factor of `F_z` at `2s`. Uniqueness of infinite products gives the doubling law on `Re s > 1`.
2. Abel summation: partial sums `O(N^θ)` make `Σ a_n (n+1)^{−s}` converge, locally uniformly, on `Re s > θ`.
3. Order two: `F_0(2s)ζ(2s) = 1`. `H(s) = (2s−1)ζ(2s)F_x(s)F_y(s)` is holomorphic on `Re s > θ` and equals `2s − 1` on
   `Re s > 1`; the half-plane is connected, so they agree. At `s = ρ/2` (a zero with `Re ρ > 2θ`) `H = 0 ≠ ρ − 1`.

## Lean
Module `ArithmeticGaugeTheory/TheTwinPairsHaveAQuarterFloor.lean`: `hasProd_moebiusLSeries`, `moebiusLSeries_mul_twin`,
`moebiusLSeries_zero_mul_riemannZeta`, `exists_continuation_of_gaugePowerBound`, `exists_continuation_double`,
`zetaZeroAbscissa_le_two_mul_of_twins`, `zetaZeroAbscissa_le_two_mul_max_gaugeExponent`, `quarter_le_max_gaugeExponent`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## What it says
The Liouville translation exchanges the sides of `1/2` (twin duality), but a twin pair of order-two points must carry the
poles of `1/ζ(2s)` on `Re s = Θ/2` between them. The bound `1/4` is not known to be attained: every known pair has
`max ≥ 1/2` (a real character and its twin). Open: is `inf_x θ_μ(x) ≥ 1/4` for single points.
