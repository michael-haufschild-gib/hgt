# Audit of docs/reports/chmd-revisit.md against the Lean corpus — 2026-10-17

Report = Phase 1 (naive synthesis: Pillars I–III, Paths A–C) + Phase 2 (hostile review: Holes 1–4, Perron–Frobenius dead end, Summary). Plan file docs/reports/cmhd-plan.md Phases 1–3 (Step A = MUST-1572, Step B = MUST-1573 done).

## Verified in Lean (all receiver layer)
- RH ⟺ R ≤ ½ on 1^⊥: `CHMDSpectralRiemannCriterion.riemannHypothesis_iff_resolventHalfBound`, `_no_primitive_bound_state`.
- RH ⟺ odd sector: `CHMDOddSectorCriterion.riemannHypothesis_iff_odd_half_bound`, `_no_odd_bound_state`.
- RH ⟺ odd Doob Poincaré `cosh mass(v²) ≤ archJump + Σ primeJump`: `WeilPhiDoobArchimedeanJumpAndHalfLineFolding.riemannHypothesis_iff_forall_odd_phiDoob_dirichlet_poincare` (line 701).
- σ_ess(R) ⊆ [0,½], ½ attained: `CHMDNoWeylAboveThreshold.weyl_value_le_half`, `CHMDThresholdWeylSequence.half_mem_spectrum_resolvent`; localization uses J_arch only (prime part dropped by positivity).
- `CHMDPurePointAboveThreshold.eigenvalue_le_one` (μ ≤ 1); `resolvent_oneL` (R1 = 1).
- Cardinal frames per off-line zero: `CHMDCardinalGraphGeometry.exists_cardinalGraphFrame` (energies +K₊/−K₋, primitive, zero cross pairing); inertia both ways (`CHMDBoundStateInertia`, `CHMDQuarterZeroBound`, `CHMDBoundStateDimension`: RH ⟺ dim P = 1).
- `CHMDPrimeChainSourceFactorization.doob_source_eq_chain_variances_sub_cosh`; docstring: "No domination of that mass or RH is asserted."
- `CHMDOddWindowCrossSign.weilLevyForm_abs_le` (diamagnetic, any f); `CHMDOddCrossSignBonus.weilLevyForm_eq_abs_add_bonus` (one-signed f only); `CHMDOddPrimeCrossSignBonusAndWindowPositivity.sourceEnergy_eq_levy_abs_add_bonus_add_primes`.
- Hole 3 confirmed: `PrimeBlindLevelCertificateSqueeze.tendsto_levelCertificates_apply` hypothesis `∀ L, μ L ∈ levelCertificates L` is RH.

## Overclaims in "Summary of the Hostile Review"
1. "1 is a simple eigenvalue of R (CHMDStationaryKernelRigidity / CHMDEvenSectorPointSpectrum)" — NOT unconditional. Corpus has μ ≤ 1 only; simplicity of 1 appears only inside `riemannHypothesis_iff_point_spectrum_above_half`. `CHMDStationaryKernelRigidity.stationaryGenerator_strictly_positive` is about the stationary theta-pullback generator ("no uniform spectral gap").
2. "+4ΘΘ|v||v| bonus on odd v" — only on the one-signed odd cone (f ≤ 0 left, ≥ 0 right).
3. "every eigenvalue of L in (0,1) spanned by divisorCardinalSource packets" — corpus has existence + counts + algebraic finite-sample inverse (`CHMDAlgebraicSpectralInverse`), no spanning/closed range (see mem:rh/chmd-algebraic-spectral-inverse-2026-10-16).

## Verdict
The review's own §3 mechanism (Markov contraction v ↦ |v|, Perron–Frobenius) reaches at most ground-state simplicity (μ < 1 on 1^⊥), never μ ≤ ½: |v| leaves 1^⊥ and the odd sector. This is Wall 13 (pointwise vs Bochner/primitive cone) in Doob coordinates; Hole 4 is Wall 12. Plan Step A item 4 (coercivity on windows ≤ 2 log 2, one-signed odd cone = nonneg even Θ|v| on (−log 2, log 2)) is window-sector positivity, marked non-RH by walls rows 272–277. No next step in the report passes a named wall.

## What remains open and producer-shaped
Only the review's Survivor Candidate 1: on the odd sector the archimedean Doob form alone leaves finitely many sub-threshold modes in a compact window (MUST-1546/1548 confinement + prime-free failure CANNOT-15 / OddSectorPoleDensityLaw); the prime jump energy with the actual Λ must lift them to ≥ cosh mass. Any attempt must name the input beyond the linear explicit formula (multiplicativity, Wall 11) and pass the fake-weight countermodel first.
