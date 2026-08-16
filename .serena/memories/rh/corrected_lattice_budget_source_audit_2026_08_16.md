# Corrected lattice prime–Gamma budget source audit (2026-08-16)

User requested unconditional pre-divisor bound `correctedBudget ≤ (4/25) N` for 75% critical-line zeros.

## Exact finding

`criticalFeaturePrimeGammaOffLineExcess t` is not pre-divisor: it equals `Re criticalFeaturePrimeGammaSourceDiagonal t - criticalLineCriticalFeatureEnergyTrace t`, and second term is explicitly Xi-zero indexed with predicate `Re rho = 1/2`. Abel approximants remain zero-indexed.

New Lean results in `formal/GaloisForLFunctions/RHTower/HedenmalmCriticalFeatureLatticePrimeGammaBudget.lean`:
- `re_criticalFeaturePrimeGammaSourceDiagonal_le_hermitianEnergyTrace`
- `primeGammaOffLineExcess_le_offLineCriticalFeatureEnergyTrace`
- existing converse `offLineCriticalFeatureEnergyTrace_le_two_primeGammaOffLineExcess`
- `criticalFeaturePrimeGammaOffLineExcess_eq_zero_iff_rh`
- `primeGammaOffLineLatticeBudget_le_offLineEnergy`
- `primeGammaOffLineLatticeBudget_eq_zero_iff_rh` for nonempty lattice.

Thus `(1/2) offLineEnergy ≤ excess ≤ offLineEnergy`; corrected budget is post-divisor off-line spectral energy up to factor 2. Desired `(4/25)N` upper bound remains exact 75%-level arithmetic core, not an existing pole–Gamma–von-Mangoldt consequence.

## Fresh corpus audit

- `HedenmalmPrimeGammaExteriorReflectionProjector.lean` has finite reflection Cesaro landing but is parameterized by a selected divisor packet.
- `HedenmalmCoefficientFaithfulExteriorSourceContour` source subquantum endpoint is formalized RH-equivalent; interpolation has no uniform arithmetic norm.
- fixed-line `xiWardInteriorSourceArithmeticBound` diverges vertically due Gamma baseline (`XiWardInteriorSourceBudgetDivergence.lean`).
- local submicroscopic separators exist but global source sampling/covariance is open.

## Verification

Direct Lean and targeted 12,986-job build pass. Axiom audit: `propext`, `Classical.choice`, `Quot.sound` only. Lint remains red only on unrelated umbrella reachability modules (`FrankensteinThetaTerminalGammaSharedGhost`, `HedenmalmThetaDirectCayleyReflectionPortDefect`, `QuadraticRateSecondVariation`).

Card updated: `docs/drafts/pipeline/1-in-progress/critical-feature-lattice-prime-gamma-budget.md`.
