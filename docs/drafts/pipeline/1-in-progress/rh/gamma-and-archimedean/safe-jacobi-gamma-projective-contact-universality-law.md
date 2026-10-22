# Safe Jacobi--Gamma projective-contact universality law

- **ID:** `safe-jacobi-gamma-projective-contact-universality-law`
- **Law:** LAW515
- **Stage:** 1-in-progress
- **Type:** THEOREM (dependency-closed paper proof)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
- **Target:** `formal/GaloisForLFunctions/RHTower/SafeJacobiGammaProjectiveContactUniversalityLaw.lean`

## Theorem

Fix any real base aperture `x ≥ 1/2`.  For every positive pair of integral aperture increments
`a,b`, the ratio of actual Jacobi--Gamma recovered boundary-coordinate increments is independent
of `x` and is exactly the Xi transverse-source projective aperture ratio:

```text
(R_x(p)-R_{x+a}(p)) / (R_x(p)-R_{x+b}(p))
  = (1-p^{-a}) / (1-p^{-b}).
```

Consequently all positive recovered increment columns collapse to one cofinite-prime projective
ray.  If `a ≠ b`, their first normalized projective defect occurs at grade `min(a,b)` and has
orientation `-1` for `a<b`, `+1` for `b<a`.

## Theorem-generated derivation

Whole-corpus leaf comparison exposed:

- `xiSafeHalfPlaneJacobiGammaRecovery_eq_coefficient`;
- `xiSafeHalfPlanePrimeCoefficient_sub_natShift_eq_transverseSource`;
- `xiTransversePrimeApertureRatio_eq_source_ratio`;
- `tendsto_xiTransversePrimeApertureRatio_cofinite_one`;
- `tendsto_xiTransversePrimeApertureRatio_firstDefect`.

The recovery module identifies each actual Jacobi--Gamma boundary output with the safe
von-Mangoldt coefficient.  Its integral aperture increment is a common nonzero diagonal factor
`p^{-x}` times the transverse Xi source.  The projective-tangent module identifies the quotient
of two transverse sources and proves its cofinite first-defect law.  Corpus contains no theorem
transporting that projective geometry back through the actual safe-side recovery.

## Dependency-closed paper proof

Write `R_x(p)` for the recovered valuation-zero Jacobi--Gamma boundary output and
`N_x(p)=p^{-x}`.  Existing recovery and source-exposure laws give, for every natural `a`,

```text
R_x(p)-R_{x+a}(p) = N_x(p) S_a(p),
```

where `S_a` is the transverse Xi-shift source.  If `b>0`, then both `N_x(p)` and `S_b(p)` are
nonzero, hence division cancels the base aperture:

```text
(R_x-R_{x+a})/(R_x-R_{x+b}) = S_a/S_b
  = (1-p^{-a})/(1-p^{-b}).
```

The existing cofinite-prime limit of the right side is one.  For distinct positive `a,b`, divide
its defect from one by `p^{-min(a,b)}`; the existing transverse first-defect theorem gives the
ordered sign.  No numerical computation is used.

## Strict corpus delta

Existing files separately prove safe Jacobi--Gamma source recovery and projective tangent
geometry of abstract transverse-source columns.  New law shows the observable, actually
recovered boundary increments carry exactly the same base-aperture-independent projective
contact filtration and order orientation.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean`
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit

## Lean result

`formal/GaloisForLFunctions/RHTower/SafeJacobiGammaProjectiveContactUniversalityLaw.lean`
proves:

- `xiSafeHalfPlaneRecoveredBoundaryIncrement_eq_transverseSource`;
- `xiSafeHalfPlaneRecoveredBoundaryIncrement_ratio_eq`;
- `tendsto_xiSafeHalfPlaneRecoveredBoundaryIncrement_ratio_cofinite_one`;
- `tendsto_xiSafeHalfPlaneRecoveredBoundaryIncrement_firstDefect`.

Direct exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/SafeJacobiGammaProjectiveContactUniversalityLaw.lean`

The module is imported by `GaloisForLFunctions/RHTower.lean`.

## Post-proof novelty audit

Performed only after dependency-closed Lean proof passed.  Exact-phrase and concept searches
returned Barnes-beta/Xi, Jensen-polynomial, generic projective-representation, and unrelated
Jacobi/von-Mangoldt literature.  No source stated that actual safe Jacobi--Gamma recovered
von-Mangoldt boundary increments have a base-aperture-independent transverse-Xi projective ratio
whose cofinite contact grade is `min(a,b)` with order orientation.

Verdict: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`.  Novelty is claimed for the exact
recovery-to-projective-contact transport, not for cancellation of a common factor or elementary
asymptotics of `(1-p^{-a})/(1-p^{-b})`.

## Log

- 2026-07-26 — LAW515 generated from declaration-leaf comparison; dependency-closed paper proof.
- 2026-07-26 — direct Lean check passed; wired into RHTower umbrella; post-proof audit plausible.
