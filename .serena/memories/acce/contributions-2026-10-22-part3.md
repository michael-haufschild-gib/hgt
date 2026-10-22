# ACCE — contributions 25–40 of 2026-10-22 (continues part2)

25. `TheSecondTangentIsAnIteratedDilation` — `pmul_log_mul` (log is a derivation for Dirichlet
    convolution), `(μ log²)*1 = Λ*Λ − Λ log`, `dampedChebyshevSecond_eq_dilation`.
26. `TheFunctionFieldCalibration` — the `F_q[T]` model; centred prefix is exactly `q^{-ε}`;
    uniform admission with budget zero; one extra degree destroys it.
27. `SecondTangentControlGivesTheAngle` — pronic mean value theorem; `riemannHypothesis_of_second_tangent_majorant`.
28. `TheWorkIsACorrelationWithWindowMeans` — the pronic adjoint of a dilation is a fibre average;
    the work is the source's correlation with its own window means.
29. `ReadingsOfTheSignCriterion` — Markov reading (flux ≥ jump + forcing), dyadic reading,
    `dampedMobiusEnergy_pos` (nonvacuity).
30. `ThePositiveCoreOfTheDilationForm` — the constant row has a positive core; complete split at the
    constant row with all cross terms.
31. `TheTangentFactorsThroughTheMoebiusDilation` — `Λ_ε = μ_ε * (log)_ε`; the tangent is the Möbius
    dilation of a Möbius-free row.
32. `AntiCorrelatedDampingsAreFew` — `card_le_of_pairwise_anticorrelated` (≤ 1 + 1/δ).
33. `TheEscapeIsAnOutAndBackExcursion` — `∫‖E_x‖ ≥ 2√E_T(ε) − two paid ends`.
34. `TheApertureFloorUnderAbsoluteDecay` — additive aperture transport + window positivity.
35. `TheEscapeIsATailPhenomenon` — `|A_ε(n) − 1| ≤ ε Σ_{d≤n}(log d)⌊n/d⌋ + n m₀(ε)` (uses
    `RHTower.moebius_floor_summatory`); the escape is beyond every fixed horizon.
36. `TheCompleteAccountingOfTheWork` — core + two explicit linear functionals + quadratic term
    (≤ prime-dilation series × energy) + polar; congruence lemmas on the observed range.
37. `TheCoreDominanceCriterion` — `riemannHypothesis_of_core_dominance` in explicit units.
38. `TheQuadraticTermIsTheResidualEnergy` — deviation energy = dual residual; quadratic term in
    residual/energy units.
39. `TheCoreGrowsLikeTheInverseDamping` — `ψ_ε(n) ≥ K log2 (2^{-ε})^K` for `2^K ≤ n`, hence
    `≥ log2/(4ε)` beyond `2^{1/ε}`.
40. `TheAveragedCriterionOnSparseHorizons` — per-horizon transport; dyadic averaged criterion.

## Current obligation
Control the signed anti-correlation of the deviation: in the accounting, everything is explicit
except `workQuadratic = rowDilationForm ε T (deviationRow ε)`, bounded by
`Σ_{j≤T} Λ(j)j^{-(ε+1/2)}` times the residual energy. The core it must not overcome is of order
`1/ε` beyond `2^{1/ε}` and `O(1)` before.

## Lean notes
- `ring` that falls back to `ring_nf` prints an info "Try this" with exit code 0 — replace with
  `ring_nf` to keep the build silent (recorded trap).
- `abs_add_le`, `ArithmeticFunction.vonMangoldt_apply_pow`, `vonMangoldt_apply_prime`,
  `Finset.sum_le_sum_of_subset_of_nonneg`, `Finset.card_nsmul_le_sum`, `pow_le_pow_of_le_one`,
  `Real.rpow_intCast`, `geom_sum_eq` are the names that work here.
- `field_simp` frequently closes the goal; a trailing `ring` then errors with "no goals".
- Beta-redexes from `rowDilationPairing`-style defs: use `simp only [def, pronicPairing]`, not `unfold`.
