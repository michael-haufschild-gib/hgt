# Exact main terms of the averaged Narain source

- **ID:** W11-NAP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Fixed averaged source](../3-formalized/ads3-narain-average-pole-decay-boundary.md)
- **Statement:** The averaged Mellin continuation has a removable zero at
  `s=1/2` and principal part `(3/π)/(s−1)²+B_YZ/(s−1)` at one.
  Every positive-power expansion of the actual averaged heat source forces
  both main coefficients, including `b=B_YZ`.

## Proof

The entire filled numerator `T_Y` vanishes at zero. Its entire divided
quotient removes the apparent denominator `u=0` from
`A_YZ=T_Y T_Z/[2u(1+2u)ξ(1+2u)]`. The resulting function is analytic
where `(1+2u)ξ(1+2u)≠0`, equals `3/π` at `u=1/2`, and has
`B_YZ=A_YZ′(1/2)`. Two analytic divided differences give the exact
principal-part decomposition.

A positive-power rate makes the subtracted Mellin transform analytic at
`u=1/2`. The cleared source identity then agrees near that point with
`A_YZ(u)=(u−1/2)² Mellin(remainder)(1/2+u)−a+b(u−1/2)`.
Evaluation forces `a=−3/π`; differentiation forces `b=B_YZ`.
Differentiating the explicit filled constant term gives

`B_YZ=Y+Z+(3/π)[−1+8ξ′(1)−log Y−log Z−2ξ′(2)/ξ(2)]`.

Thus all height dependence is elementary. The inverse-Mellin weighted
residue at `s=1` is exactly
`y⁻¹[B_YZ−(3/π)log y]`, by the corpus's double-pole residue theorem.
This identifies the contour main term without asserting a remainder rate.

## Lean

Namespace `GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap`:

- `analyticAt_narainMellinMean_zero` and `narainMellinMean_zero` in
  `NarainMeanPrincipalPart`: central removal with value zero.
- `narainMellinMean_principalPart` and
  `differentiableOn_narainMellinMeanRegularPart`: exact principal part
  and holomorphic remainder wherever `(1+2u)ξ(1+2u)≠0`.
- `narainAverageConstant_explicit`: the displayed elementary height dependence.
- `narainAverageRate_constant_coefficient` in `NarainAverageCoefficient`:
  every positive-power expansion forces `b=B_YZ`.
- `narainMellinMean_weighted_residue` in `NarainMeanResidue`:
  the exact inverse-Mellin logarithmic and constant contribution.

All three modules pass final direct Lean checks. Six endpoint axiom
checks use only `propext`, `Classical.choice`, and `Quot.sound`.
Umbrella imports are wired. No small-height rate is asserted.

## Gates

- [x] 0 → 1: exact source and divided-difference mechanism identified.
- [x] 1 → 2: mean central removal, principal part and coefficient rigidity proved.
- [x] 2 → 3: direct Lean checks, axiom audits and umbrella imports.
