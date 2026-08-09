# Finite Pauli-character projector extraction law

- **Stage:** 3-formalized
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL] [BRIDGE] [NOVELTY NOT CLAIMED]`
- **Parent:** `../1-in-progress/static-local-complexity-law.md`, O4.12z25
- **Lean certificate:** `finite-pauli-character-projector-extraction-law-formalized.md`
- **Lean:** `HTGeometry/FinitePauliCharacterProjector.lean` (orthogonality, projector, extraction),
  `HTGeometry/PauliCharacterProjectorExtraction.lean` (empty register, submodule form)

## Exact statement

Let `V` be any finite qubit register and let

\[
 \chi_P(Q)=\prod_{v\in V}\epsilon(Q_v,P_v),
 \qquad P,Q\in\{I,X,Y,Z\}^V,
\]

where `epsilon(q,p)` is the sign obtained by conjugating Pauli `p` by
Pauli `q`. Then

\[
 \boxed{\sum_Q\chi_P(Q)\chi_R(Q)=4^{|V|}\,\mathbf 1_{P=R}.}
 \tag{1}
\]

Let `C_Q` be conjugation of the two-replica operator algebra by the paired
Pauli `Q tensor Q`. Define

\[
 \Pi_P=4^{-|V|}\sum_Q\chi_P(Q)C_Q.                 \tag{2}
\]

If `X_R` has exact paired-Pauli character `R`, then

\[
 \boxed{\Pi_PX_R=\mathbf 1_{P=R}X_R.}             \tag{3}
\]

Consequently, if a subspace `U` is invariant under every `C_Q`, and
`X_R` belongs to character `R` for every `R`, then

\[
 \boxed{\sum_R X_R\in U\quad\Longrightarrow\quad X_P\in U
        \text{ for every }P.}                     \tag{4}
\]

The statement includes the empty register: there is one character and its
projector is the identity.

## Dependency-closed proof

On one site the four sign vectors are the rows of the order-four Walsh
matrix. Directly,

\[
 \sum_{q\in\{I,X,Y,Z\}}\epsilon(q,p)\epsilon(q,r)
 =4\mathbf 1_{p=r}.                                \tag{5}
\]

Finite distributivity factors the global sum:

\[
\begin{aligned}
 \sum_Q\chi_P(Q)\chi_R(Q)
 &=\sum_Q\prod_v
     \epsilon(Q_v,P_v)\epsilon(Q_v,R_v)\\
 &=\prod_v\sum_q\epsilon(q,P_v)\epsilon(q,R_v).
\end{aligned}
\]

If `P=R`, every factor is `4`. If `P` and `R` differ at one site, the
corresponding factor is zero. This proves `(1)`.

For `X_R` in exact character `R`, `C_QX_R=chi_R(Q)X_R`. Substitution in
`(2)` and `(1)` proves `(3)`. If `U` is invariant, every summand in `(2)`
maps `U` into `U`, so `Pi_P(U)<=U`. Apply `Pi_P` to `sum_R X_R`; equation
`(3)` leaves only `X_P`, proving `(4)`.

## Frontier consequence

This supplies the exact extraction step missing from the visible quotient
detector. Aggregate all weight-at-most-two commutator images of a
zero-character singlet input before quotienting by occupied nonsinglet
input. If the aggregate vanishes in that quotient, `(4)` recovers membership
of every individual Pauli-character image. No unproved direct-sum assertion
and no fourth-moment Clifford inference is needed.

The remaining concrete obligations are:

1. prove the product-Clifford zero-twirl canonical layer is invariant under
   every paired-Pauli conjugation;
2. instantiate the aggregate quotient detector and its hidden-kernel law;
3. reproduce the nonsinglet layer by the one-site central-Casimir family;
4. remove the global identity and global-swap kernel in the connected-edge
   recovery.

## Formal status

Closed, unconditionally.

`(5)` is `boolPauliConjugationSign_orthogonality` and `(1)` is
`finitePauliConjugationSign_orthogonality`; the factorisation of the global sum into a product of
one-site sums is exactly the finite distributivity the card describes.  `(2)` is
`finiteTwoReplicaPauliCharacterProjector`, `(3)` is
`finiteTwoReplicaPauliCharacterProjector_apply_grade`, and `(4)` is
`finiteTwoReplicaPauliCharacter_component_mem_of_sum_mem`.

Two statements the card makes were added in `HTGeometry/PauliCharacterProjectorExtraction.lean`:

- The empty register.  `finitePauliMatrix_const_none` — the all-identity string is the identity
  matrix — gives `finiteTwoReplicaPairedPauliConjugationLinear_const_none`, so on an empty register
  the single label acts trivially and `finiteTwoReplicaPauliCharacterProjector_of_isEmpty` says the
  projector is `LinearMap.id`.  `card_pauliLabel_of_isEmpty` counts the one character.  No
  orthogonality argument survives there: the sum has one term and its sign is an empty product.
- `Π_P(U) ≤ U` as a submodule inequality
  (`finiteTwoReplicaPauliCharacterProjector_map_le_of_invariant`); the corpus stated it
  memberwise, and the card writes it as an inclusion.

The four frontier obligations listed below are now closed elsewhere: `(1)` and `(2)` by
`paired-pauli-zero-twirl-invariance-law` and `aggregate-pauli-visible-quotient-detector-law`, and
`(4)`'s mode count by `positive-graph-edge-casimir-kernel-law`.  Obligation `(3)` — reproducing the
nonsinglet layer by the one-site central-Casimir family — remains open, on
`visible-kernel-recovery-hall-law`.

Umbrella build passes; the axiom audit reports only `propext`, `Classical.choice`, and
`Quot.sound`.

## Hostile audit

- `(4)` assumes actual invariance of `U`; independence of character spaces
  alone would not permit extraction modulo an arbitrary subspace.
- Projectors resolve paired-Pauli characters, not Clifford isotypic
  multiplicities or higher-replica permutation sectors.
- This theorem does not prove Hall expansion, circuit anti-concentration,
  complexity growth, a plateau, or recurrence timing.
- No novelty is claimed for finite character orthogonality. Its value is
  closing a precise logical gap in the concrete mixed-Hall construction.
