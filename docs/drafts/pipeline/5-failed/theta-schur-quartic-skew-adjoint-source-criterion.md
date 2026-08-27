# Theta Schur quartic skew-adjoint source criterion

- **ID:** GTA-PQ4-SAD
- **Stage:** 5-failed
- **Type:** FALSIFIED (producer); THEOREM (Lean) positive survivor
- **Source:** `rh-current-frontier-map.md` · route GTA (`ORIENT`); corpus-led continuation of
  `GTA-PQ4-QD`
- **Statement:** The root-free quadratic defect is exactly half squared Hilbert--Schmidt distance
  from Hermitian matrices, so cofinally vanishing stage skew energy would imply RH.  This producer
  is impossible: actual stage energies converge to a strictly positive, explicitly detected
  anti-Hermitian energy of the fixed signed theta kernel.

## Goal
Replace spectral Schur data by one coefficient-faithful scalar on actual corrected theta matrices,
then decide whether that scalar can vanish cofinally or is obstructed by the fixed theta source
inverse.

## Gates
- [x] 0 → 1  in-progress: corpus search, exact conjecture, scratch proof
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: exact Lean modules/builds and axiom audit
- [ ] 3 → 4  publication-ready: standalone proof and literature audit

## Conjecturing loop
- `[GTA-PQ4-SAD.1]` `HS²(M) − Re tr(M²)` may admit a source-entrywise adjoint-defect normal form.
  Scratch Lean proves
  `HS²(M) − Re tr(M²) = ½‖M−Mᴴ‖²_HS`.
- `[GTA-PQ4-SAD.2]` Combining `.1` with the Schur quartic bound should give
  `Q₄ ≤ 575 HS²(M) ‖M−Mᴴ‖²_HS` without roots or Schur data on the right.
- `[GTA-PQ4-SAD.3]` Uniform theta-stage HS ceiling should turn cofinal skew-energy smallness into
  cofinal quartic smallness, hence RH.
- `[GTA-PQ4-SAD.4]` Test whether actual theta skew energy can approach zero.  Because corrected
  kernels converge in HS norm to the fixed signed theta kernel, continuity should reduce this to
  ordinary self-adjointness of that fixed kernel; prove a source-side positive floor if possible.

## Current status
- `.1–.3` closed in Lean.  They give an unconditional source-only implication to RH.
- `.4` falsifies the premise for actual corrected theta stages.  The fixed theta inverse is
  ordinarily non-selfadjoint, detected on the pinned coordinate vector.  Exact finite-support
  transfer and Hilbert--Schmidt convergence give a positive limiting floor.

## Positive survivor `[PROVED HERE]`

Write `Kₖ` for the actual trace-zero corrected finite-support theta kernel, `L = -K_θ` for the
fixed signed theta kernel, and

`Aₖ = ‖Kₖ - Kₖ*‖²_HS = ‖Mₖ - Mₖᴴ‖²_HS`.

Then

`Aₖ → A∞ := ‖L - L*‖²_HS > 0`.

More precisely, on the pinned coordinate `c(t)=t`,

`⟨c, Bc⟩ = -i ∫₀¹ q(t)t²(1-t)/2 dt`,

and the real integral is strictly positive because `q(t)>0` and `t²(1-t)>0` on `(0,1)`.  Hence
`B` is not self-adjoint, so the unitarily transported signed matrix kernel has `A∞>0`.  Since
adjoint is an isometry in Hilbert--Schmidt norm,

`‖(Kₖ-Kₖ*)-(L-L*)‖_HS ≤ 2‖Kₖ-L‖_HS → 0`,

which proves exact energy convergence.  Consequently every sufficiently late stage satisfies
`Aₖ > A∞/2`, and cofinal smallness is false.

This is the strongest positive statement exposed by the obstruction: exact asymptotic
classification with a source-side strict witness, not only a negative result.

## Lean status

- `formal/GaloisForLFunctions/HTGeometry/FiniteMatrixSchurQuarticSkewAdjointDefect.lean`
  proves the finite quadratic identity and quartic majorant.
- `formal/GaloisForLFunctions/RHTower/HedenmalmThetaSkewAdjointDefectCriterion.lean`
  proves cofinal skew-energy smallness implies RH.
- `formal/GaloisForLFunctions/RHTower/HedenmalmThetaSkewAdjointDefectFloorNoGo.lean`
  proves the coordinate expectation, strict limit energy, exact stage-energy convergence,
  eventual half-limit floor, and negation of the cofinal premise.
- Direct `lake env lean` checks and targeted `lake build` calls pass.
- `#print axioms` for the strict expectation, positive limit, convergence, and no-go reports only
  `propext`, `Classical.choice`, and `Quot.sound`.

## Literature audit (2026-08-27)

- Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494, studies a theta
  differential eigenproblem and pair self-adjointness, not this quantile Hilbert--Schmidt kernel or
  its finite-stage ordinary adjoint-defect floor:
  https://arxiv.org/abs/2606.17494
- Gallo--Zweck--Latushkin, *Numerical Fredholm determinants for matrix-valued kernels on the real
  line*, arXiv:2507.22875, studies truncation/quadrature convergence of Fredholm determinants, not
  the source-specific anti-Hermitian energy identity:
  https://arxiv.org/abs/2507.22875
- Exact-phrase and concept searches for the pinned coordinate expectation, quantile-speed density,
  and positive skew-adjoint floor found no matching source.  Novelty remains **UNVERIFIED** pending
  expert/bibliographic review; theorem status is independent and fully Lean-checked.

## Log
- 2026-08-27 — card frozen before tree implementation.  Frontier map treated read-only.
- 2026-08-27 — `.1–.3` formalized.  `.4` solved: exact positive asymptotic floor proves producer
  impossible.  Positive survivor formalized; card retired without modifying frontier map.
