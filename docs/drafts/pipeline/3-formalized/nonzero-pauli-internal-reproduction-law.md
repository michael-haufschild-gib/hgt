# Nonzero Pauli internal-reproduction law

- **ID:** nonzero-pauli-internal-reproduction-law
- **Stage:** 3-formalized
- **Type:** THEOREM (bridge)
- **Parent:** `first-order-clifford-interpolation-law.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL] [NOVELTY NOT CLAIMED]`
- **Lean certificate:** `nonzero-pauli-internal-reproduction-law-formalized.md`

## Exact theorem

Let `U_*` be the canonical greatest maximum-defect subspace of the complete
weight-at-most-`q` two-replica collective Pauli family on any finite linearly
ordered qubit register. Resolve its exact nonzero paired-Pauli character
sector as

\[
 U_{\ne0}=\sum_{P\ne0}
   \left(U_*\cap\mathcal X_P\right),
\]

where `X_P` is the simultaneous character subspace labelled by `P`. Then

\[
 \boxed{U_{\ne0}\subseteq
   \sum_{\operatorname{wt}Q\le1}\operatorname{ad}^{(2)}_Q(U_{\ne0}).}
                                                               \tag{1}
\]

Thus the entire resolved nonzero-character input is reproduced internally by
literal weight-one collective Pauli commutators. The statement is stronger
than rank nondecrease.

## Proof

For each nonzero character `P`, the existing first-defect selector chooses a
weight-one label `Q(P)`. Its commutator is injective on
`U_* cap X_P`, and the target-character permutation is collision-free.
First-order Clifford interpolation now shows this selected commutator is a
linear combination of two product-Clifford conjugations. Product-Clifford
invariance of `U_*` therefore puts every selected image back inside `U_*`.
Character covariance puts it in the corresponding nonzero target grade, so
the direct sum of all selected images lies inside `U_(ne0)`.

Injectivity preserves each source-grade dimension, and collision-free target
grades make those image dimensions add. Their sum equals `dim U_(ne0)`.
Hence the selected-image subspace is an internal subspace of equal dimension
and must equal `U_(ne0)`. Every selected image is literal one-step weight-one
output, proving (1).

## Hostile audit

- Product-Clifford invariance is used only after exact first-order
  interpolation; no false inference from finite invariance to Lie invariance
  occurs.
- The theorem concerns the resolved sum of nonzero exact character pieces.
  Completeness of the zero/nonzero character decomposition for the whole
  canonical obstruction is a separate obligation.
- Zero-character anisotropic directions are not covered by (1). They remain
  the only target-reproduction channel not closed by this theorem.
- No claim about full Hall, anti-concentration, complexity growth, plateau,
  or recurrence scales follows yet.

## Formal status

Closed, unconditionally.

`HTGeometry/TwoReplicaNonzeroPauliInternalReproduction.lean` proves a general
internal graded-selector reproduction theorem and instantiates (1) for any
subspace satisfying the greatest-maximizer condition.

`HTGeometry/LinearFamilyGreatestMaximizer.lean` removes that condition.
Supermodularity of linear-family deficiency already gave existence *and*
uniqueness of the greatest defect maximizer
(`existsUnique_linearFamilyDefect_greatestMaximizer`), so the maximizer is a
function of the family alone: `linearFamilyGreatestMaximizer`. Both defining
properties are recorded, together with the characterisation that no other
subspace has them, and the Hall criterion is restated as the vanishing of this
one subspace's deficiency.

`HTGeometry/NonzeroPauliInternalReproductionCanonical.lean` names the card's
`U_*` — `canonicalTwoReplicaQLocalObstruction` — and states (1) there:

    finiteTwoReplicaNonzeroPauliResolvedSubspace_canonical_le_shadow

No hypothesis, on any finite linearly ordered register, for every `q`. Umbrella
build passes; the axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Log

- 2026-08-05 — general internal graded-selector equality mechanism proved.
- 2026-08-05 — canonical nonzero paired-Pauli sector reproduced by the
  literal weight-one family.
- 2026-08-09 — greatest-maximizer premise discharged; `(1)` is now a
  hypothesis-free theorem about a named subspace.
