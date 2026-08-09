# Aggregate Pauli visible-quotient detector law

- **Stage:** 2 — fully proven on paper
- **Status:** `[PAPER-PROVED] [BRIDGE] [NEW MECHANISM; PRIORITY UNCHECKED]`
- **Parent:** `visible-kernel-recovery-hall-law.md`
- **Lean target:** `HTGeometry/TwoReplicaPauliVisibleQuotientDetector.lean`

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
