# Rational-coordinate cyclic fixed-field universality law

- **ID:** ratfunc-cyclic-fixed-field-universality
- **Stage:** 5-failed
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of projective cyclic normal form with scale and translation
  fixed-field classifications
- **Statement:** Every coefficient-fixing automorphism of `K(X)` over an algebraically closed
  characteristic-zero field is identity, finite scaling type with a conjugated power-field fixed
  locus, or infinite scaling/translation type with only conjugated constants fixed.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [ ] 2 → 3 formalized: exact-file Lean passed; final axiom audit pending
- [x] 3 → 5 failed: post-proof literature audit found the classical cyclic `PGL₂` fixed-field
  classification

## Corpus inputs

- `ratFuncAlgEquiv_cyclicNormalForm`
- `fixedField_zpowers_ratFuncUnitScaleAction`
- `fixedField_zpowers_ratFuncUnitScaleAction_of_infinite_order`
- `fixedField_zpowers_ratFuncTranslationAction`
- `mem_fixedField_zpowers_iff`

## Proof

`[PROVED HERE]` Conjugate fixedness through the normalizing coordinate `h`: `e(r)=r` iff the
normal-form generator fixes `h⁻¹(r)`.  In the finite scale branch of order `N≥2`, the fixed field
is exactly `K(X^N)`.  Infinite-order scaling fixes only the base field.  In characteristic zero,
unit translation also has infinite additive order and fixes only the base field.  Transport these
three exact descriptions back through `h`; the identity branch is unchanged.  No computation is
used.

## Lean certificate

- Module: `GaloisForLFunctions.HTGeometry.RatFuncCyclicFixedFieldUniversalityLaw`
- Main theorem: `GaloisForLFunctions.HTGeometry.ratFuncAlgEquiv_cyclicFixedFieldUniversality`
- Exact source check:
  `lake env lean GaloisForLFunctions/HTGeometry/RatFuncCyclicFixedFieldUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Imported by `GaloisForLFunctions/HTGeometry.lean`.

## Novelty protocol

No literature search before exact Lean proof.

## Post-proof literature audit

Performed only after exact Lean source check passed.

- Beauville, *Finite Subgroups of PGL₂(K)*
  ([author PDF](https://math.univ-cotedazur.fr/u/beauvill/pubs/PGL%282%29.pdf)), classifies finite
  `PGL₂` subgroups up to conjugacy; over an algebraically closed field the cyclic branch is the
  standard diagonal class.
- Proposition 9 of Ferraguti--Micheli,
  *Exceptional rational functions of degree 5 over finite fields: classification by monodromy,
  ramification, and the Riemann--Hurwitz formula*
  ([arXiv:2607.05075](https://arxiv.org/abs/2607.05075)), explicitly conjugates a cyclic
  order-`N` rational action to `X ↦ ζX` and states that its fixed field is `K(X^N)`.
- Bell--Moosa--Satriano, *On invariant rational functions under rational transformations*
  ([arXiv:2306.11108](https://arxiv.org/abs/2306.11108)), places translation dynamics and fixed
  rational functions in a more general invariant-fibration theory.

The finite branch is an exact literature collision; the infinite scaling and characteristic-zero
translation branches are the standard infinite-order complements.  Combining them into one Lean
four-way theorem is useful formal consolidation but not a new mathematical law.

## Retirement

`LITERATURE COLLISION.`  Keep the warning-free Lean consolidation wired, but do not count it as a
literature-novel survivor.

## Log

- 2026-07-23 — Unconsumed projective cyclic normal form connected to independently formalized
  scale and translation fixed fields during terminal-mechanism exhaustion.
- 2026-07-23 — Exact-file Lean passed warning-free; post-proof audit found the finite fixed-field
  branch explicitly in literature, so novelty failed.
