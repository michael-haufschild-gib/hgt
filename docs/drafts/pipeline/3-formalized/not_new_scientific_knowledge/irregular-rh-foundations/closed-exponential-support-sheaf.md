# Closed exponential-support sheaf

## Stage

3 — formalized

## Claim

For a universe-0 topological space `X`, a closed subset `S ⊆ X`, and an additive coefficient group
`A`, the constant sheaf on `S` has an ordinary direct image along the closed inclusion `S ↪ X`.
Direct image obeys the exact composition law for nested supports.  For continuous
`φ : X → ℝ`, this applies to the closed exponential epigraph `{(x,t) | φ x ≤ t}`.

This is an ordinary sheaf-theoretic support object.  It is not an enhanced ind-sheaf, derived
proper direct image, open extension by zero, or irregular Riemann--Hilbert correspondence.

## Dependency audit

- Existing corpus: exponential epigraph and its closedness are in
  `StokesEnhancedEpigraphConvolution.lean`.
- Existing corpus: direct-image composition appears in the Deninger tower, but no generic
  HTGeometry closed-support construction exists.
- Mathlib: `TopCat.Sheaf.pushforward`, `CategoryTheory.constantSheaf`, and
  `TopCat.Presheaf.Pushforward.comp` provide underived sheaf machinery.
- Toolchain boundary: available `AddCommGrpCat` filtered-colimit/sheafification instances force
  this construction to universe-0 spaces.

## Paper proof

Let `i_S : S → X` be subtype inclusion and `A_S` the constant sheaf with value `A` on `S`.
Define the closed-support object as `(i_S)_* A_S`.  If `S ⊆ T ⊆ X`, subtype inclusions satisfy
`i_S^X = i_S^T ∘ i_T^X` pointwise.  Functoriality of direct image therefore gives a canonical
isomorphism

`(i_S^X)_* A_S ≅ (i_T^X)_* (i_S^T)_* A_S`.

For continuous `φ`, its epigraph is closed, so the same construction gives the claimed
exponential-support sheaf.

## Lean status

- [x] definitions in `StokesClosedSupportSheaf.lean`
- [x] nested-support composition theorem
- [x] exponential specialization
- [x] direct file check
- [x] targeted module build
- [x] axiom audit of new declarations only: `propext`, `Classical.choice`, `Quot.sound`

Direct module check, targeted module build, umbrella wiring, prior new-declaration axiom audit, and
authoritative repository lint pass.

## RH status

No implication for RH.  This closes one support-level prerequisite only.

## Promotion log

- 2026-08-27 — Exact support/factorization surface re-audited and all Stage 3 gates passed.
