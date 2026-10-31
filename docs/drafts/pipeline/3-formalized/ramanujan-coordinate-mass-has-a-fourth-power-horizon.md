# Ramanujan coordinate mass has a fourth-power horizon

- **ID:** ramanujan-coordinate-mass-has-a-fourth-power-horizon
- **Stage:** 3-formalized
- **Statement:** For `Q≥2`, `N≥Q⁴`, the normalized Ramanujan family
  through conductor `Q` has lower frame constant `1/2`. A unit vector
  approximated within squared error `1/4` has squared coordinate mass
  at least `1/18` against that family.

## Proof

The proved harmonic frame bound is
`(log(N+1)−2log Q)Σa_m²≤‖Σa_m r_m‖²`.
At `Q⁴≤N`, its left factor is at least `log N/2`. Divide by
`log N>0` to normalize the vectors.

Write `z=Σa_m r̂_m`, `‖x‖=1`, `‖x−z‖≤1/2`. Then `‖z‖≤3/2`,
so the lower frame gives `Σa_m²≤9/2`. Also `⟨x,z⟩≥1/2`.
Cauchy–Schwarz gives
`1/4≤⟨x,z⟩²≤(9/2)Σ⟨x,r̂_m⟩²`, proving the stated constant.

An approximation by raw modes through `R≤Q` gives the same bound:
multiply its coefficients by `√log N` and extend them by zero through `Q`.

## Lean

`CriticalArithmeticCorrelationTheory/RamanujanFamiliesHaveExplicitCoordinateMass.lean`:
`half_sum_sq_le_normalizedRamanujan_synthesis_sq`,
`normalizedRamanujan_coordinate_mass_ge_of_explicit_approximation`,
`normalizedRamanujan_coordinate_mass_ge_of_raw_approximation`.
Direct Lean check passed. All three transitive axiom audits contain only
`propext`, `Classical.choice`, `Quot.sound`. Umbrella wired.
