# Aggregate Pauli visible-quotient detector law

- **Stage:** 3-formalized
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL] [BRIDGE] [NEW MECHANISM; PRIORITY UNCHECKED]`
- **Parent:** `visible-kernel-recovery-hall-law.md`
- **Lean certificate:** `aggregate-pauli-visible-quotient-detector-law-formalized.md`
- **Lean:** `HTGeometry/TwoReplicaPauliVisibleQuotientDetector.lean` (abstract layer),
  `HTGeometry/CanonicalTwoReplicaObstruction.lean` and
  `HTGeometry/PauliVisibleQuotientDetectorCanonical.lean` (concrete canonical layer)

## Exact statement

Let `V` be a finite qubit register. Let `X_0` be the exact zero
paired-Pauli-character subspace of the two-replica operator algebra, and let
`W` be any subspace invariant under all paired-Pauli conjugations. For a
locality cutoff `q`, define

\[
 A_P=\begin{cases}
 \operatorname{ad}^{(2)}_P,&\operatorname{wt}(P)\le q,\\
 0,&\operatorname{wt}(P)>q,
 \end{cases}
\]

and the single aggregate quotient detector

\[
 \mathcal D_{q,W}(s)=
 \left[\sum_{P\in\{I,X,Y,Z\}^V}A_Ps\right]\in X/W,
 \qquad s\in U_S\le X_0.                         \tag{1}
\]

Then

\[
 \boxed{\mathcal D_{q,W}(s)=0
 \iff A_Ps\in W\text{ for every }P.}             \tag{2}
\]

Moreover, the range of `D_(q,W)` embeds into `X/W` by its subtype map, and
that embedded range lies in the quotient of the literal one-step
weight-at-most-`q` output from `U_S`. Thus it supplies both the injective
visible assembly and exact hidden-kernel hypothesis required by
visible-kernel recovery.

## Dependency-closed proof

Zero-character input satisfies `C_Qs=s` for every paired-Pauli conjugation.
Exact covariance gives

\[
 C_Q(A_Ps)=\chi_P(Q)A_Ps,                         \tag{3}
\]

so every summand in `(1)` belongs to its labelled exact character grade.

If every `A_Ps` belongs to `W`, their sum belongs to `W`, proving the reverse
implication in `(2)`. Conversely, if `D_(q,W)(s)=0`, then
`sum_P A_Ps` belongs to `W`. Since `W` is paired-Pauli invariant, every exact
character projector `Pi_P` preserves `W`. Applying `Pi_P` to the aggregate
and using character orthogonality leaves exactly `A_Ps`; hence `A_Ps` belongs
to `W`. This proves `(2)`.

The detector already takes values in the actual quotient `X/W`. Therefore
its range subtype is injective. Its value is the quotient of a sum of literal
family images of `s`, so its range lies in the quotient of the one-step
family shadow. No separate direct-sum codomain, dimension comparison, or
choice of grade representatives is needed.

## Concrete canonical layer

For the canonical greatest two-replica Hall obstruction `U_*`, put

\[
 U_W=U_*\cap\ker T_V.
\]

Product-Clifford covariance makes `U_*` paired-Pauli invariant, while the
strict half-turn theorem proves `ker T_V` paired-Pauli invariant. Hence
`U_W` satisfies the invariant-subspace premise of `(2)` unconditionally.

## Formal status

Closed, unconditionally.

**Abstract layer.**  `(1)` is `finiteTwoReplicaPauliVisibleQuotientDetector` — the quotient map
composed with the aggregate of every cutoff collective commutator, restricted to the source.  `(2)`
is `finiteTwoReplicaPauliVisibleQuotientDetector_mem_ker_iff`, for an arbitrary zero-character
source and an arbitrary paired-Pauli invariant target.  The range claims are
`finiteTwoReplicaPauliVisibleRangeInclusion_injective` (the subtype map, so injectivity is
`Subtype.val_injective` and nothing else is needed) and
`finiteTwoReplicaPauliVisibleRangeInclusion_range_le`.  All three hold for every `Uₛ` and `W`, so
they are strictly stronger than the canonical instance and need no restatement.

**Concrete canonical layer.**  This is what was missing.  The layer's two premises were previously
carried as hypotheses because nothing named the card's `U_*`.  Supermodularity already proved the
greatest defect maximizer exists *and* is unique, so it is a function of the family:
`HTGeometry/CanonicalTwoReplicaObstruction.lean` names it
`canonicalTwoReplicaQLocalObstruction` and records that it is greatest, which discharges the
premise.

`HTGeometry/PauliVisibleQuotientDetectorCanonical.lean` then names both sides of the card's
concrete layer —

- `canonicalTwoReplicaHiddenLayer` = `U_* ⊓ ker T_V`, proved paired-Pauli invariant with no
  hypothesis (`canonicalTwoReplicaHiddenLayer_pairedPauli_invariant`);
- `canonicalTwoReplicaVisibleSource` = `U_* ⊓ range (swap-invariant embedding)`, proved to have
  exact zero paired-Pauli character (`canonicalTwoReplicaVisibleSource_le_zeroCharacter`) —

and states `(2)` there:

    finiteTwoReplicaPauliVisibleQuotientDetector_canonical_mem_ker_iff

No hypothesis, on any finite register, for every `q`.  Umbrella build passes; the axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Hostile audit

- Source must have exact zero paired-Pauli character. The theorem does not
  apply to an arbitrary product-Clifford fixed vector until that concrete
  zero-character inclusion is proved.
- `W` must be invariant under every paired-Pauli conjugation. Independence
  of the grades alone is insufficient.
- The theorem closes detector assembly and hidden first-image recovery only.
  It does not prove nonsinglet Hall reproduction or injectivity of connected
  edge recovery modulo identity/global swap.
- It proves no complexity growth, cavity decay, anti-concentration, plateau,
  or recurrence statement.
