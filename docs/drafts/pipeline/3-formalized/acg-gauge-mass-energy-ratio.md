# The gauge mass of an escape state is its energy ratio

- **ID:** acg-gauge-mass-2026-10-26
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ArithmeticCorrelationGeometry README §9 topic 6 (continued from the spectral-measure card)
- **Statement:** For the damped Möbius receiver, `E(M−1)/E(T+1) ≤ d·K_T(d,d) ≤ E(M)/E(T+1)` with
  `M = ⌊(T+2)/d⌋`; the gauge spectral mass of an escape state `L` is `inf_d d·K(d,d)`; bounded
  energy (admission) gives mass one; energy trapped between `cN^κ` and `CN^κ`, `κ > 0`, gives mass
  zero.

## Proof
Pronic self-similarity: the fibre `jm..jm+j−1` has mass `1/(j m(m+1))`; complete fibres give the
exact identity `‖D_jv‖²_{jK+j−1} = (1/j)E_v(K)` (induction), truncation plus the sharp contraction
the upper bound. Diagonal limits squeezed by energy ratios along the horizons of `L`.

## Lean
`formal/GaloisForLFunctions/ArithmeticCorrelationGeometry/TheGaugeMassOfAnEscapeStateIsItsEnergyRatio.lean`:
`pronicNorm_rowDilate_sq_eq`, `pronicNorm_rowDilate_sq_le/ge`, `mul_cofactorGram_le_energyRatio`,
`energyRatio_sub_one_le_mul_cofactorGram`, `gaugeMass_eq_iInf`,
`ActualCofactorLimitMass.gaugeMass_eq_one_of_admits`, `ActualCofactorLimitMass.gaugeMass_eq_zero_of_powerGrowth`.

## Insight
The gauge torus sees exactly the scale-invariant part of the escaping energy: power-type escape
(the signature of an off-line zero) carries no gauge spectrum. Open: RH ⇔ every escape state has
positive gauge mass (needs subpower energy ⇒ zero-freeness).
