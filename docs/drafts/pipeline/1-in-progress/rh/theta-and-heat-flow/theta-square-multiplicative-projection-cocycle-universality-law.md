# Theta-square multiplicative projection-cocycle universality law

- **ID:** `theta-square-multiplicative-projection-cocycle-universality-law`
- **Law:** LAW519
- **Stage:** 1-in-progress
- **Type:** THEOREM (dependency-closed paper proof)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
- **Target:** `formal/GaloisForLFunctions/RHTower/ThetaSquareMultiplicativeProjectionCocycleUniversalityLaw.lean`

## Theorem

Let the weighted positive-half boundary charge of square index `m` be

```text
C_m(u) = m^(-1/2) B_(2 log m)(thetaLogMother)(u),
```

where `B_a` is the moving logarithmic boundary.  For `m,n>1`, this charge obeys an exact
multiplicative-index cocycle:

```text
C_(mn)(u)
  = m^(-1/2)n^(-1/2)
      [B_(2 log m)(T_(2 log n) thetaLogMother)(u)
       + T_(2 log m)(B_(2 log n) thetaLogMother)(u)].
```

Moreover each `C_m` is exactly the `m^(-1/2)`-weighted conjugation coboundary of the fixed
positive-half projection, and the positive truncation seam of the actual `m`-th theta atom is
obtained by adding this same charge.

## Theorem-generated derivation

Whole-corpus declaration comparison exposed:

- `thetaSquareLogAtom_eq_shifted_mother`;
- `positiveThetaSquareLogAtom_translation_seam`;
- `forwardTranslationBoundary_add`;
- `thetaSquareForwardBoundary_eq_conjugationDefect`;
- `positiveProjectionConjugationDefect_curvature_zero`.

The corpus proves translation additivity and square-atom weighting separately.  It does not
transport the additive cocycle through `m ↦ 2 log m`, where multiplication of square indices
becomes addition of translation lengths.

## Dependency-closed paper proof

For positive natural indices, `log(mn)=log m+log n`, hence
`2 log(mn)=2 log m+2 log n`.  Also real powers give
`(mn)^(-1/2)=m^(-1/2)n^(-1/2)`.  Substitute these identities into the definition of `C_(mn)` and
apply `forwardTranslationBoundary_add` to obtain the displayed multiplicative-index cocycle.

The existing square-boundary theorem identifies the unweighted boundary with the positive
projection conjugation defect; multiplication by `m^(-1/2)` gives the weighted identification.
The existing theta-atom seam theorem then says this charge is precisely the correction needed to
intertwine positive truncation with the actual weighted square atom.  Flatness follows from the
generic conjugation-defect curvature theorem.  No numerical computation is used.

## Strict corpus delta

Existing modules separately describe one square atom, additive translation boundaries, and flat
projection coboundaries.  LAW519 proves the missing semigroup statement: composite square indices
carry one exact multiplicative-index boundary cocycle with the physical `m^(-1/2)` theta weight.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean`
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit

## Lean result

`formal/GaloisForLFunctions/RHTower/ThetaSquareMultiplicativeProjectionCocycleUniversalityLaw.lean`
defines `thetaSquarePositiveBoundaryCharge` and proves:

- `thetaSquarePositiveBoundaryCharge_eq_projectionConjugationDefect`;
- `positiveThetaSquareLogAtom_add_boundaryCharge`;
- `thetaSquarePositiveBoundaryCharge_mul`.

Direct exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/ThetaSquareMultiplicativeProjectionCocycleUniversalityLaw.lean`

The module is imported by `GaloisForLFunctions/RHTower.lean`.

## Post-proof novelty audit

Performed only after dependency-closed Lean proof passed.  Searches found half-space projection
commutators in translation-invariant quantum walks, scaling representations with `|λ|^(1/2)`
weights, and unrelated theta/cyclic-cocycle constructions.  No source identified the exact
`m ↦ 2 log m` square-rate theta boundary charge as a multiplicative-index cocycle of the
positive-half projection.

Relevant comparisons:

- https://arxiv.org/abs/1804.04520
- https://arxiv.org/abs/1910.14368
- https://arxiv.org/abs/math/0209142

Verdict: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`.  Novelty is claimed for the exact
theta-square weighted projection-cocycle identity, not for generic group cocycles, theta
translation, or half-space commutators separately.

## Log

- 2026-07-26 — LAW519 generated from theta square-atom translation, boundary additivity, and
  projection-coboundary closure.
- 2026-07-26 — direct Lean check passed; wired into RHTower umbrella; post-proof audit plausible.
