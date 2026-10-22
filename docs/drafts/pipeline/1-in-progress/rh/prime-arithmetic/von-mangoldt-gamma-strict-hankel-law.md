# Von Mangoldt–Gamma strict Hankel law

- **ID:** von-mangoldt-gamma-strict-hankel-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** Lean-only closure of `RHTower/VonMangoldtGammaBivariateMoment.lean` with `HTGeometry/MomentHankelStrict.lean` and positive-density support
- **Statement:** Every nonempty finite von Mangoldt–Gamma bivariate moment row has positive-definite Hankel matrices and strictly positive determinants in every finite size.

## Goal

Upgrade source moment nonnegativity and Hankel semidefiniteness to all-order strictness.  Strictness
rules out every hidden finite-support collapse of the Taylor-remainder coordinate and identifies a
continuum Hausdorff invariant shared by all finite Gamma depths.

## Gates

- [x] 0 → 1 in-progress: theorem-first closure, source-pure, exact proof found
- [x] Paper proof dependency-closed and `[PROVED HERE]`
- [ ] 2 → 3 formalized: direct Lean check, axiom audit, and final module build green
- [ ] 3 → 4 publication-ready: standalone treatment and priority audit

## Parent theorem closure

1. `finiteExponentialGammaBivariateMoment_eq_integral` represents every rate-degree row by a
   positive Hausdorff measure on `(0,1]`.
2. `exponentialRemainderMeasure` has density `exp(-rate(1-u))`, strictly positive throughout the
   interval.
3. `HTGeometry.momentHankelMatrix_posDef_of_infiniteSupport` converts a representing measure that
   charges every cofinite set into strict positive definiteness and positive determinant.
4. Every nonempty actual aperture contains index `0`, i.e. the von Mangoldt channel at `2`, with
   positive weight `log(2)/2` and positive rate `log(2)`.

## Paper proof

`[PROVED HERE]` Removing a finite set from `(0,1]` leaves Lebesgue mass one.  Reweighting by the
strictly positive Taylor-remainder density preserves null sets, hence every single channel measure
charges the complement of every finite set.  If one source weight is positive, its positive scalar
multiple is dominated by the finite mixture, so the mixture also has infinite support.  The
strict-moment theorem then makes every finite Hankel block positive definite, hence gives positive
determinant.  For the actual finite von Mangoldt source with `M>0`, the `2`-channel supplies the
required positive weight and rate for all displacement `x`, rate degree `a`, and matrix size `n`.

No limiting argument, RH assumption, or computation occurs.

## Occupancy and novelty audit

- Exact Lean search found only `finiteVonMangoldtGammaBivariateMoment_hankel_posSemidef`; no strict
  or determinant theorem for this bivariate array.
- `VonMangoldtGammaFactorialNormalizationNoGo.lean` concerns a different infinite raw-moment block
  and shows factorial normalization can destroy positivity; it does not occupy this Hausdorff row.
- Infinite-support strict Hankel positivity is classical.  Berg–Szwarc,
  *A determinant characterization of moment sequences with finitely many mass-points*
  (arXiv:1405.7267), and Salazar, *Order-Moment Transport and Hankel Determinants in
  Special-Function Inequalities* (arXiv:2606.31647), cover generic parent mechanisms.
- Targeted searches found no von Mangoldt–Gamma Taylor-remainder bivariate array or this all-row
  strict determinant hierarchy.  This is a noncollision finding, not a priority claim.

## Lean target

- Module: `GaloisForLFunctions.RHTower.VonMangoldtGammaStrictHankelLaw`
- Principal theorem: `det_finiteVonMangoldtGammaBivariateMoment_hankel_pos`
- General connector: `finiteExponentialGammaBivariateMoment_hankel_posDef`

## Log

- 2026-07-21 — Derived bottom-up from actual RHTower representation theorem and HTGeometry strict
  Hankel consumer; exact corpus search clean.
- 2026-07-21 — Paper proof closed; standard abstract parents found in literature, exact arithmetic
  law not found; Lean source written pending process-safe verification.
