# First-order Clifford interpolation law

- **ID:** first-order-clifford-interpolation-law
- **Stage:** 2 — fully proven
- **Type:** THEOREM (bridge)
- **Parent:** `product-clifford-visible-recovery-reduction-law.md`
- **Status:** `[PROVED HERE] [FORMAL-SOURCE-CHECKED] [NOVELTY NOT CLAIMED]`

## Exact theorem

Let `A` and `B` be commuting involutions, put `R=AB`, and let `J` commute
with `A`, `B`, and `X`. Define

\[
 T_+=1+J(A+B)-AB,\qquad T_-=1-J(A+B)-AB.
\]

On the exact `R`-odd sector, `RXR=-X`,

\[
 \boxed{T_+XT_- - T_-XT_+
        =4J[A+B,X].}                               \tag{1}
\]

For the physical two-replica register, take `A=P tensor I`,
`B=I tensor P`, `J=iI`, and use the strict Clifford quarter turns
`C_+` and `C_-`. Then for every finite register and every one-site Pauli
axis,

\[
 \boxed{\operatorname{ad}^{(2)}_P(X)
   =-i\,(C_+X-C_-X)}                                \tag{2}
\]

whenever paired-Pauli conjugation by `P tensor P` sends `X` to `-X`.

## Proof

Oddness and `R^2=1` give `RX=-XR`. Also
`R(A+B)=(A+B)R=A+B`. Expanding the left side of (1), commuting `J`, and
using these identities leaves exactly `4J((A+B)X-X(A+B))`.

The strict doubled quarter-turn matrix is `T_+/2`; its inverse is `T_-/2`.
Thus the difference of its two conjugation directions is one quarter of the
left side of (1). Substituting `J=iI` and multiplying by `-i` proves (2).

## Frontier consequence

If a subspace is invariant under every product Clifford, both terms on the
right side of (2) remain in that subspace. Therefore every selected
first-defect commutator image from an odd paired-Pauli character remains in
the canonical obstruction itself. This is stronger than the previous square
identity, which only proved preservation after applying the commutator twice.

The theorem is the missing local ingredient for upgrading collision-free
nonzero-character Hall expansion to internal reproduction. That upgrade is
now proved in `nonzero-pauli-internal-reproduction-law.md`; the remaining
channel is zero-character anisotropy and completeness of the full character
split.

## Hostile audit

- Formula (2) applies only on the exact paired-Pauli odd sector; it does not
  assert first-order invariance on the zero-character sector.
- No continuous Lie-invariance or differentiation of a finite group action is
  used.
- This theorem alone does not prove target reproduction, full Hall,
  anti-concentration, complexity growth, plateau, or recurrence scales.

## Formal status

`HTGeometry/TwoReplicaFirstOrderCliffordInterpolation.lean` proves (1) over
an arbitrary ring and (2) for every finite qubit register. Targeted source
elaboration passes. Axiom audits report `[propext, Quot.sound]` for the pure
ring identity and only `propext`, `Classical.choice`, and `Quot.sound` for the
physical capstone. The same module proves odd first images and all
first-defect-selected images remain inside every canonical greatest
obstruction, with the same standard-axiom audit. Final umbrella build remains
deferred to final audit.

## Log

- 2026-08-05 — abstract odd-sector quarter-turn difference identity proved.
- 2026-08-05 — physical strict product-Clifford interpolation formalized and
  axiom-audited.
