# Sonin Euler inverse and polar corners are noncompact

- **ID:** sonin-euler-inverse-polar-corner-noncompact
- **Stage:** 2-fully-proven
- **Type:** THEOREM / ROUTE GATEKEEPER (paper)
- **Scientific status:** BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Source inputs:** Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*,
  arXiv:2310.18423v2, Propositions 4.6--4.8; `sonin-euler-metric-corner-noncompact.md`

## Statement

Let `Q_lambda` be the orthogonal projection onto the actual even archimedean Sonin space at
`lambda>0`. For a prime `p`, put

`w_p(s)=|1-p^(-1/2-is)|^2`

on the archimedean Hardy--Titchmarsh line and let `W_p=M_{w_p}`. Then all four corners

`(1-Q_lambda) W_p Q_lambda`,

`(1-Q_lambda) W_p^(-1) Q_lambda`,

`(1-Q_lambda) W_p^(1/2) Q_lambda`,

`(1-Q_lambda) W_p^(-1/2) Q_lambda`

are noncompact. In particular none is Hilbert--Schmidt or trace class.

The inverse weight is the Euler cyclic-density multiplier

`W_p^(-1)=M_|L_p(1/2-is)|^2`.

If `theta_p` is the source's bounded Sonin isomorphism, then

`theta_p^* theta_p=W_p`

in the pinned archimedean realization, and its polar unitary is

`U_polar=theta_p W_p^(-1/2)`.

Although `theta_p` maps the archimedean Sonin space exactly onto the `{infinity,p}` Sonin space,
`U_polar` does not do so even modulo compact operators: its crossing corner is noncompact. Thus the
canonical Sonin identification cannot be converted into a unitary/Fredholm determinant comparison by
the source metric, its inverse, or its polar square root.

## Abstract operator lemma

Let `Q` be an orthogonal projection on a Hilbert space and let `A` be a bounded positive invertible
operator. Then:

1. `(1-Q)AQ` is compact if and only if the commutator `[Q,A]` is compact.
2. `[Q,A^(-1)]=-A^(-1)[Q,A]A^(-1)`. Hence the `A` and `A^(-1)` corners are compact
   simultaneously.
3. If the `A^(1/2)` corner is compact, then the `A` corner is compact.
4. If the `A^(-1/2)` corner is compact, then the `A^(-1)` corner is compact.

Consequently noncompactness of the `A` corner forces noncompactness of the inverse and both square-root
corners.

## Proof

Since `A=A^*`, the two off-diagonal blocks are adjoints:

`QA(1-Q)=((1-Q)AQ)^*`.

Moreover

`[Q,A]=QA(1-Q)-(1-Q)AQ`.

The compact operators form a norm-closed adjoint ideal. This proves item 1. Multiplying
`AA^(-1)=1` on the appropriate sides gives

`[Q,A^(-1)]=-A^(-1)[Q,A]A^(-1)`

and, conversely,

`[Q,A]=-A[Q,A^(-1)]A`.

Thus one commutator is compact exactly when the other is, proving item 2. If `C=A^(1/2)`, then

`[Q,A]=[Q,C^2]=[Q,C]C+C[Q,C]`.

Compactness of `[Q,C]` would imply compactness of `[Q,A]`, proving item 3 by contraposition. Applying
the same square identity to `A^(-1)=(A^(-1/2))^2` proves item 4.

The source weight obeys

`(1-p^(-1/2))^2 <= w_p(s) <= (1+p^(-1/2))^2`,

so `W_p` is bounded, positive, and invertible. The theorem
`sonin-euler-metric-corner-noncompact.md` proves that its `Q_lambda` corner is noncompact, hence the
abstract lemma gives all four claims.

For the polar statement, let `K_lambda` and `K_lambda^p` be the two Sonin spaces. Since `theta_p` is
boundedly invertible and maps `K_lambda` onto `K_lambda^p`, it induces a bounded isomorphism of the
quotient Hilbert spaces. Therefore

`(1-Q_lambda^p) theta_p W_p^(-1/2) Q_lambda`

is compact if and only if `(1-Q_lambda)W_p^(-1/2)Q_lambda` is compact. The latter is noncompact, so
the polar-unitary corner is noncompact.

## Route consequence

- `[CLOSED]` The forward Euler metric is not a trace-ideal Sonin seam.
- `[CLOSED]` Passing to the cyclic density `|L_p|^2`, to the inverse norm, or to either polar
  square-root correction cannot repair compactness.
- `[CLOSED]` The exact Sonin isomorphism `theta_p` cannot be made unitary modulo compacts by its
  canonical polar decomposition.
- `[OPEN CORE]` This does not rule out additional smoothing by two closed prolate resolvents. Such a
  construction must first specify self-adjoint/closed realizations and prove a relative-resolvent
  Schatten estimate.

## Novelty audit

The abstract commutator identities are standard operator theory, and this card is a direct consequence
of the already-proved forward metric noncompactness theorem. It closes a source-specific gap but does
not pass the novelty gate. It is retained as a gatekeeper because it removes the inverse-weight and
polar-unitarization variants from Route B without computation.

## Lean formalization

Status: **complete and unconditional**.

Module `formal/GaloisForLFunctions/HTGeometry/ProjectionCornerCommutator.lean` — the abstract
operator lemma:

- `crossCorner Q A = (1-Q) A Q`, `upperCorner Q A = Q A (1-Q)`, `projCommutator Q A = QA - AQ`.
- `isCompactOperator_crossCorner_iff` — item 1 (corner and commutator compact together; the
  converse direction is Schauder via `isCompactOperator_adjoint_rectangular`).
- `projCommutator_inv`, `isCompactOperator_projCommutator_inv_iff` — item 2.
- `projCommutator_mul`, `isCompactOperator_projCommutator_sq`, `isCompactOperator_crossCorner_sq`
  — items 3 and 4.
- `not_isCompactOperator_crossCorner_inv`, `not_isCompactOperator_crossCorner_sqrt` — the
  propagation of noncompactness.
- `mixedCorner P Q A = (1-P) A Q`, `mixedCorner_eq_comp`, `crossCorner_eq_comp`,
  `isCompactOperator_mixedCorner_iff` — transport of corner compactness along a bounded
  isomorphism carrying `ran Q` onto `ran P`.  This is the polar-statement step.

Module `formal/GaloisForLFunctions/RHTower/SoninEulerInversePolarCorner.lean` — the concrete
Sonin instance, built on `RHTower.centralPositiveEulerCorner_not_isCompactOperator`:

- `positiveEulerDilationOperator_isSelfAdjoint`, `positiveEulerDilationOperator_sub`,
  `norm_eulerPerturbation_le`, `two_lt_sqrt_add_inv_sqrt`,
  `isUnit_positiveEulerDilationOperator` — `W_p` is self-adjoint and boundedly invertible by a
  Neumann series, since `‖p^{-1/2}(D_p + D_p^*)‖ ≤ 2/√p < 1 + p^{-1}`.
- `spectrum_positiveEulerDilationOperator_pos` — every real spectral value of `W_p` is positive.
- `eulerInverseWeight`, `eulerSqrtWeight`, `eulerInverseSqrtWeight` — the continuous functional
  calculus weights `W_p^{-1}`, `W_p^{1/2}`, `W_p^{-1/2}`, with
  `eulerInverseWeight_mul`, `positiveEulerDilationOperator_mul_inverse`,
  `eulerSqrtWeight_mul_self`, `eulerInverseSqrtWeight_mul_self` and their self-adjointness.
- `not_isCompactOperator_eulerCorner`, `not_isCompactOperator_eulerInverseCorner`,
  `not_isCompactOperator_eulerSqrtCorner`, `not_isCompactOperator_eulerInverseSqrtCorner` — the
  four corners of the statement.
- `not_isCompactOperator_corner_of_inverse`, `not_isCompactOperator_corner_of_sqrt`,
  `not_isCompactOperator_corner_of_inverseSqrt` — the stronger forms: *every* self-adjoint
  inverse, and *every* self-adjoint square root of `W_p` or of `W_p^{-1}`, has a noncompact
  corner.  The polar operators are particular cases.
- `not_isCompactOperator_polarCorner`, `not_isCompactOperator_polarSqrtCorner` — the polar
  statement: for every bounded isomorphism `θ` carrying the Sonin space at `a` onto a second
  Sonin space with projection `P`, the corner of `θ W_p^{-1/2}` (resp. `θ W_p^{1/2}`) across the
  pair is noncompact.

Every declaration depends only on `propext`, `Classical.choice`, `Quot.sound`.

The `[OPEN CORE]` item (additional smoothing by two closed prolate resolvents) is unaffected: it
requires unbounded self-adjoint realization theory that is outside this card's statement.
