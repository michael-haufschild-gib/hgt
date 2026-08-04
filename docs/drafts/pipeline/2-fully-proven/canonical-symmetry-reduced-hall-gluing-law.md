# Canonical symmetry-reduced Hall gluing law

- **ID:** canonical-symmetry-reduced-hall-gluing-law
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `static-local-complexity-law.md`, gate O4.12z25
- **Statement:** Every finite linear family has a unique largest maximum-defect subspace; it is fixed by every invertible symmetry preserving the family span, and disjoint forward/reverse Hall channels glue across two layers whenever the reverse channel pays exactly for forward-output overlap.

## Goal

Replace arbitrary mixed singlet/nonsinglet Hall counterexamples by one canonical symmetry-invariant
counterexample and give an exact dimension theorem that closes the mixed-layer overlap once the
physical forward and reverse Pauli channels are verified.

## Gates

- [x] 0 → 1 in-progress: finite-dimensional defect and symmetry action are well posed
- [x] 1 → 2 fully-proven: dependency-closed proofs below
- [ ] 2 → 3 formalized: targeted modules compile and axiom audit is clean; final umbrella build intentionally deferred to final audit
- [ ] 3 → 4 publication-ready: use only after concrete local-Pauli span covariance and reverse-overlap Hall hypotheses are discharged

## Theorems and proofs

Let (A=(A_j)_{j\in J}\) be a finite family (X\to Y),

\[
 F(U)=\sum_jA_jU,\qquad \delta(U)=\dim U-\dim F(U).
\]

Since (F(U+V)=F(U)+F(V)) and (F(U\cap V)\subseteq F(U)\cap F(V)), rank
modularity gives

\[
 \delta(U)+\delta(V)\le \delta(U+V)+\delta(U\cap V).
\]

Deficiency is integer-valued and bounded above by (dim X), so it attains a maximum. Choose a
maximizer (U_*\) of largest dimension. If (V\) is another maximizer, supermodularity and maximality
force both (U_*+V\) and (U_*\cap V\) to be maximizers. Maximal dimension gives
(U_*+V=U_*\), hence (V\subseteq U_*\). Thus (U_*\) contains every maximizer and is unique.
Because (delta(0)=0\), the all-subspaces Hall condition is equivalent to the single equation
(delta(U_*)=0\).

Suppose invertible maps (g_X,g_Y\) carry the linear span of the family to itself under
(T\mapsto g_YTg_X^{-1}\), in both directions. Then

\[
 F(g_XU)=g_YF(U),\qquad \delta(g_XU)=\delta(U).
\]

Thus (g_XU_*\) is another maximum-defect subspace of the same dimension. The greatest-maximizer
property and dimension equality give (g_XU_*=U_*\). This covers continuous mixing of Pauli
generators, not only permutations.

For the gluing law, let (S\cap W=0\), (S_0\subseteq S\), (W_0,C\subseteq W\), and
(C^*\subseteq S\). Suppose

\[
 \dim C\ge\dim S_0,
 \qquad
 \dim C^*\ge\dim(C\cap W_0),
\]

and the delivered output contains ((W_0+C)+C^*\). The two summands are disjoint, so

\[
\begin{aligned}
 \dim((W_0+C)+C^*)
 &=\dim W_0+\dim C-\dim(C\cap W_0)+\dim C^*\\
 &\ge\dim W_0+\dim S_0
 =\dim(S_0+W_0).
\end{aligned}
\]

This is exact overlap compensation: the forward image expands the first layer, and the reverse
image repays precisely the part already hidden in the second layer.

## Formal status

- `LinearFamilyDefectSupermodularity.lean`: supermodularity, existence and uniqueness of the
  greatest maximizer, one-equation Hall criterion, permutation covariance, and continuous
  span-covariance invariance.
- `BipartiteHallGluing.lean`: overlap-compensated mixed-layer rank theorem.
- `TwoInvolutionCollectiveCommutator.lean`: for commuting involutions (p,q\), the collective
  commutator squares to four on the sector odd under conjugation by (pq\), hence is injective there.
- `TwoReplicaPauliRelativeParityInverse.lean`: literal one-qubit two-replica Pauli instantiation,
  including the full all-subspaces finrank inequality on each relative-odd sector.
- `TwoReplicaPauliHallSymmetryReduction.lean`: exact paired-Pauli covariance of the literal local
  commutator family, preservation of its operator span, invariance of the canonical greatest
  maximum-defect subspace, and its resulting four-sector Pauli bigrading.
- `FinitePauliConjugationLaw.lean` and `TwoReplicaGlobalPauliHallSymmetryReduction.lean`: exact
  arbitrary-register Pauli conjugation law and global weight-at-most-`q` covariance; the canonical
  global maximum-defect subspace is now proved invariant under every paired Pauli string and resolves
  exactly under every finite list of those commuting involutions.
- Targeted `lake env lean <file>` checks pass. Axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound` where finite-dimensional subspace selection is used; the
  two-involution theorem uses only `propext`.

## Exact surviving frontier

For the two-replica local-Pauli family, concrete paired-Pauli span covariance, its arbitrary-site
weight-at-most-`q` lift, canonical-maximizer invariance, and finite simultaneous parity resolution are
proved. The surviving task is to prove a globally injective selection/assembly of the
literal local relative-odd inverses, and prove reverse Hall expansion on the overlap between
grade-zero edge images and already occupied nonzero grades. The local relative-odd sectors already
have the exact inverse (A_p^2=4I\). No claim of full Pauli Hall expansion is made until the global
assembly and reverse-overlap theorems are proved.

## Log

- 2026-08-04 — Dependency-closed paper proofs completed; all three abstract mechanisms formalized
  and axiom-audited. Final umbrella build deferred by project rule.
- 2026-08-04 — Added basis-free invariant-subspace parity resolution. Over every field with
  `2 != 0`, a subspace preserved by an involution is the internal direct sum of its even and odd
  parts. For two commuting involutions it is the sum of four simultaneous parity sectors, with an
  exact four-term finrank identity. Literal paired two-replica Pauli conjugations are involutive and
  mutually commuting, so every subspace stable under two of them has this four-sector resolution.
  `InvolutiveSubspaceParityDecomposition.lean` and the extended
  `TwoReplicaPauliRelativeParityInverse.lean` compile; capstone axiom audits contain only
  `propext`, `Classical.choice`, and `Quot.sound`. This proves the decomposition mechanism but does
  not yet prove that the canonical global maximizer is stable under the concrete local-Pauli family;
  concrete span covariance remains the next gate.
- 2026-08-04 — Closed concrete covariance for the literal local family. Conjugating by paired Pauli
  `b` fixes axis `a=b` and negates either transverse-axis collective commutator. Therefore every
  conjugated generator lies in the original operator span, the canonical greatest maximum-defect
  subspace is fixed by every paired-Pauli conjugation, and it has the exact four-sector bigrading for
  every pair of axes. `TwoReplicaPauliHallSymmetryReduction.lean` compiles; axiom audits of covariance,
  span preservation, canonical invariance, and bigrading contain only `propext`, `Classical.choice`,
  and `Quot.sound`. Global arbitrary-site tensor lifting and grade assembly remain open.
- 2026-08-04 — Closed arbitrary-site tensor lifting. Every finite Pauli string conjugates another by
  the product of local signs; paired strings commute exactly because the one-replica sign occurs
  twice. Every global collective commutator is therefore an eigenoperator under every paired-Pauli
  conjugation, for any locality cutoff `q`. The canonical greatest maximum-defect subspace of the
  complete weight-at-most-`q` family is fixed by all paired strings. The targeted modules compile and
  their capstone axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`. Finite
  simultaneous character resolution and mixed zero-character overlap are the surviving gates.
- 2026-08-04 — Closed finite simultaneous parity resolution. A subspace invariant under any finite
  commuting list of involutions equals the sum of all recursively resolved parity pieces, and their
  finranks add exactly. Instantiation for any finite list of paired global Pauli strings now applies
  to the canonical weight-at-most-`q` maximum-defect subspace. Targeted compilation and capstone
  axiom audits pass with only `propext`, `Classical.choice`, and `Quot.sound`. Graded selector-output
  assembly and zero-character overlap remain.
- 2026-08-04 — Closed graded selector-output assembly for every nonzero global Pauli character.
  `PauliCharacterFirstDefectCovariance.lean` proves distinct Pauli words define distinct simultaneous
  conjugation characters and that their exact character subspaces form an `iSupIndep` family.
  `PauliCharacterFirstDefectHallExpansion.lean` then applies the collision-free first-defect
  selector to the literal weight-one Pauli family and proves
  `finiteTwoReplicaNonzeroPauliResolvedSubspace_finrank_le_shadow` for the sum of all nonzero
  character components of every ambient subspace. Targeted elaboration passes and the capstone uses
  only `propext`, `Classical.choice`, and `Quot.sound`. The sole remaining two-replica Hall channel is
  zero character: anisotropic diagonal correlations and reverse compensation for overlap of their
  edge outputs with the already occupied nonzero grades.
