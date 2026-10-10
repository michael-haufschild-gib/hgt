# Weighted separation-free Turán power-sum lower bound (TG infrastructure)

- **ID:** TG-TUR-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean; classical Turán second main theorem with coefficients, separation-free form)
- **Statement:** z, b : ι → ℂ on a finite set s (N = #s), some |z_i| ≥ 1, and every top group
  {i : t ≤ |z_i|}, 1 − 1/(M+2N+2) ≤ t ≤ 1, has |Σ b_i| ≥ β > 0. Then some M+1 ≤ ν ≤ M+N has
  |Σ_i b_i z_i^ν| ≥ β/(2eN(6(N+1)(M+2N+2))^N). Scaled form with |z_i| ≥ Z.

## Proof
Corpus separating polynomial (unit-weight Turán, HTGeometry/PowerSumTuranLowerBound): vanishes on the inner
group, = Π_j(1 − (z_j/z_o)^{J+1}) on outer points. Weighted value sum = Σ_O b_o + E, |E| ≤ ((1+ρ^{J+1})^N − 1)Σ_O|b_o|,
and the coefficient mass bound is independent of J, so J large gives |E| ≤ β/4.

## Lean
`HTGeometry/PowerSumTuranWeightedLowerBound.lean` (236 lines), wired after PowerSumTuranLowerBound in HTGeometry.
`norm_weighted_sum_sepPoly_values_ge`, `exists_norm_weightedPowerSum_ge`, `exists_norm_weightedPowerSum_ge_scaled`.
Axioms [propext, Classical.choice, Quot.sound].

## Use
Needed by TG's remaining reading items: localized Ω (windows) for non-extremal / unattained Θ, and the
converse "finite-range Gaussian budget ⇒ zero-free wedge". Also general wall-3 (local zero clustering) tool.
