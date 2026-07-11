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
