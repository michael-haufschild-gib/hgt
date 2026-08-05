# Product-Clifford visible-recovery reduction law

- **ID:** product-clifford-visible-recovery-reduction-law
- **Stage:** 2 — fully proven
- **Type:** THEOREM (bridge)
- **Parent:** `static-local-complexity-law.md`
- **Status:** `[PROVED HERE] [FORMAL-SOURCE-CHECKED] [NOVELTY NOT CLAIMED]`

## Exact theorem

Let `T_V` be product-Clifford twirling on the two-replica matrix algebra of
any finite qubit register. For every Pauli word `P`, every
`X in range(T_V)`, and the collective commutator `A_P`,

\[
                     \boxed{T_V(A_PX)=0.}             \tag{1}
\]

Consequently, for every locality cutoff `q` and every
`U_S <= range(T_V)`, the complete one-step q-local shadow obeys

\[
        \boxed{\sum_{\operatorname{wt}P\le q}A_PU_S
                   \subseteq\ker T_V.}               \tag{2}
\]

Now let `q >= 2`, let `G` be any connected interaction graph, and let
`U_W <= ker(T_V)` be invariant under paired-Pauli conjugations. If

\[
                 U_W\subseteq\sum_{\operatorname{wt}P\le q}A_PU_W,
                                                               \tag{3}
\]

then the aggregate Pauli quotient detector and positive graph Casimir give

\[
 \boxed{\dim(U_S+U_W)\le
   \dim\sum_{\operatorname{wt}P\le q}A_P(U_S+U_W)
   +\dim(U_S\cap N),}                                \tag{4}
\]

where `N` is exactly the span of global identity and global replica swap.

For the canonical greatest maximum-defect subspace `U_*`, its established
product-Clifford split automatically supplies `U_S`, `U_W`, disjointness,
paired-Pauli invariance, detector hidden-kernel classification, visible
quotient rank, and connected graph recovery. Therefore (3) is the only
remaining premise needed for (4).

## Proof

Product-Clifford range lies in the trivial paired-Pauli character. Hence
`A_PX` has exact character `P`. If `P` is the identity word, `A_P=0`. If
`P` is nonidentity, choose a paired Pauli `Q` whose conjugation sign on `P`
is `-1`. Product-Clifford twirling is unchanged by paired-Pauli conjugation,
so

\[
 T_V(A_PX)=T_V(C_QA_PX)=T_V(-A_PX)=-T_V(A_PX),
\]

which forces (1). Taking spans proves (2).

For (4), quotient all first images `A_Ps` of `s in U_S` by occupied
`U_W`. Exact Pauli-character projectors show the single aggregate detector
vanishes exactly when every first image is in `U_W`. Its range embeds in the
literal output quotient, giving the visible-rank estimate. On detector
kernel, every first image belongs to `U_W`; the positive connected graph
Casimir returns these directions to the singlet layer through literal
weight-two output. Its kernel there is exactly `N`. Common-kernel-corrected
visible recovery yields (4).

## Hostile audit

- Equation (1) is exact finite-group character separation, not a Haar or
  continuous-symmetry inference.
- The aggregate detector does not discard cancellations: exact character
  projectors recover every labelled summand modulo paired-Pauli-invariant
  `U_W`.
- No injectivity is asserted before accounting for identity/global swap.
- Condition (3) remains unproved for the complete canonical zero-twirl
  layer. Nonzero Pauli-character Hall alone does not imply (3), because
  zero-character anisotropic directions remain.
- Thus this theorem closes every mixed visible-recovery interface but does
  not yet prove full two-replica Hall, circuit anti-concentration, complexity
  growth, plateau, or recurrence scales.

## Formal status

`HTGeometry/TwoReplicaProductCliffordVisibleRecovery.lean` proves (1), (2),
the physical detector wrapper (4), and the canonical greatest-maximizer
reduction. Targeted source elaboration passes. Axiom audits of all four
capstones report only `propext`, `Classical.choice`, and `Quot.sound`. Final
umbrella build remains deferred to final audit.

## Log

- 2026-08-05 — exact singlet-output zero-twirl separation proved.
- 2026-08-05 — aggregate detector, quotient rank, positive graph recovery,
  and canonical split assembled; unique remaining premise isolated as (3).
