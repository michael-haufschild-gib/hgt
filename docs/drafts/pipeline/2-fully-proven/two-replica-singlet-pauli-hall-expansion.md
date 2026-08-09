# Two-replica singlet Pauli Hall expansion

- **Stage:** 2 — fully proven on paper
- **Status:** `[PAPER-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/static-local-complexity-law.md`, O4 planar replica cavity
- **Lean:** resolved-fibre Hall mechanism formalized as
  `resolvedFiberAssembly_subspace_finrank`; exact one-site Clifford
  identity/swap reduction is also formalized. The arbitrary-register physical
  identity/swap embedding is now injective, and the nine-term weight-two edge
  Casimir is exactly intertwined with its coefficient action. The
  fixed-orientation single-commutator mismatch projections and orthogonal
  edge-defect assembly required for the stronger Hall statement remain.

## Exact statement

Let `G=(V,E)` be a finite connected simple graph.  At each physical qubit,
let `F_i` exchange two replicas and put

\[
 L_i=\operatorname{span}_{\mathbb C}\{I_i,F_i\},
 \qquad
 \mathcal S_2=\bigotimes_{i\in V}L_i.               \tag{1}
\]

This is the sitewise two-replica singlet algebra.  Its global permutation
subspace is

\[
 \mathcal G_2=\operatorname{span}_{\mathbb C}
 \left\{\bigotimes_i I_i,\ \bigotimes_iF_i\right\}. \tag{2}
\]

Fix any Pauli labels `a,b in {1,2,3}`.  For every edge `e={i,j}`, define

\[
 G_{e,ab}=\sigma_a^{(i,1)}\sigma_b^{(j,1)}
          +\sigma_a^{(i,2)}\sigma_b^{(j,2)},
 \qquad
 A_{e,ab}=\operatorname{ad}_{G_{e,ab}}.             \tag{3}
\]

Then for every complex linear subspace
`U <= S_2/G_2`,

\[
 \boxed{\qquad
 \dim_{\mathbb C}\operatorname{span}
    \{\overline A_{e,ab}U:e\in E\}
 \ge \dim_{\mathbb C}U.
 \qquad}                                            \tag{4}
\]

Here `overline A_(e,ab)` is the map induced from `S_2/G_2` into the full
two-replica Hilbert--Schmidt space: every vector in `G_2` is annihilated by
all edge commutators.  Thus the full weight-at-most-two collective Pauli
family satisfies Hall expansion on the complete sitewise singlet quotient.
Only one fixed Pauli orientation per graph edge is needed.

## Local edge law

On one local two-replica factor write

\[
 L_a=\sigma_a\otimes I,\qquad
 R_a=I\otimes\sigma_a,\qquad
 D_a=L_a-R_a.                                       \tag{5}
\]

The swap relations are

\[
 L_aF=FR_a,\qquad R_aF=FL_a,
 \qquad FD_a=-D_aF.                                 \tag{6}
\]

On the four-dimensional endpoint singlet space
`span{I tensor I, I tensor F, F tensor I, F tensor F}`, direct commutator
expansion gives

\[
\begin{array}{rcl}
 A_{e,ab}(I\otimes I)&=&0,\\
 A_{e,ab}(F\otimes F)&=&0,\\
 A_{e,ab}(I\otimes F)&=&-D_a\otimes FD_b,\\
 A_{e,ab}(F\otimes I)&=&-FD_a\otimes D_b.
\end{array}                                         \tag{7}
\]

The last two outputs are nonzero and orthogonal.  Indeed

\[
 \|D_a\|_{\rm HS}^2=8,\qquad
 \langle D_a,FD_a\rangle_{\rm HS}=0,               \tag{8}
\]

and the same holds for `b`.  The first identity follows from
`D_a^2=2I-2 sigma_a tensor sigma_a`.  For the second, use
`Tr(F(X tensor Y))=Tr(XY)` and expand:

\[
\begin{aligned}
 \operatorname{Tr}(D_aFD_c)
 &=\operatorname{Tr}(FD_cD_a)\\
 &=\operatorname{Tr}(\sigma_c\sigma_a)
   -\operatorname{Tr}(\sigma_c\sigma_a)
   -\operatorname{Tr}(\sigma_a\sigma_c)
   +\operatorname{Tr}(\sigma_c\sigma_a)=0.         \tag{9}
\end{aligned}
\]

Consequently `A_(e,ab)` is injective on

\[
 M_e=\operatorname{span}\{I_iF_j,F_iI_j\}
       \otimes\bigotimes_{k\notin e}L_k,            \tag{10}
\]

and annihilates the complementary endpoint-matched coordinate sector of
`S_2`.

Moreover, `D_a` and `FD_a` are orthogonal to `L_i`.  Hence

\[
 A_{e,ab}(\mathcal S_2)\subseteq
 \mathcal W_e:=L_i^\perp\otimes L_j^\perp
       \otimes\bigotimes_{k\notin e}L_k.            \tag{11}
\]

If `e != e'`, then `W_e` and `W_(e')` are orthogonal: at a vertex in their
symmetric difference, one tensor factor lies in `L` and the other in
`L^perp`.

## Global proof

Use the tensor basis indexed by bit strings `x:V -> {0,1}`, with `0`
representing `I` and `1` representing `F`.  Let `P_e:S_2 -> M_e` be the
coordinate projection retaining exactly the strings with unequal endpoint
bits on `e`.  Equation (7) says

\[
 A_{e,ab}|_{\mathcal S_2}=A_{e,ab}P_e,
 \qquad
 \ker(A_{e,ab}|_{\mathcal S_2})=\ker P_e.           \tag{12}
\]

Connectedness gives the exact common kernel

\[
 \bigcap_{e\in E}\ker P_e=\mathcal G_2,             \tag{13}
\]

because a bit string agrees across every edge exactly when it is constant.

Let `U <= S_2/G_2` and choose any linear lift
`U_tilde <= S_2` complementary to `G_2`.  Then
`dim U_tilde=dim U` and (13) makes the stacked projection

\[
 P:U_{\rm tilde}\longrightarrow
       \bigoplus_{e\in E}P_eU_{\rm tilde},
 \qquad u\longmapsto(P_eu)_e                         \tag{14}
\]

injective.  Therefore

\[
 \dim U
 \le\sum_{e\in E}\dim P_eU_{\rm tilde}.            \tag{15}
\]

By the local injectivity in (10),

\[
 \dim A_{e,ab}U_{\rm tilde}=\dim P_eU_{\rm tilde}. \tag{16}
\]

The edge output spaces are mutually orthogonal by (11), so their dimensions
add:

\[
\begin{aligned}
 \dim\operatorname{span}_{e\in E}A_{e,ab}U_{\rm tilde}
 &=\sum_{e\in E}\dim A_{e,ab}U_{\rm tilde}\\
 &=\sum_{e\in E}\dim P_eU_{\rm tilde}\\
 &\ge\dim U.
\end{aligned}                                       \tag{17}
\]

Since every element of `G_2` is killed, the images depend only on quotient
classes.  Equation (17) proves (4).

## What this advances

The physical synchronization theorem now proves that the sum of the nine
literal weight-two edge Casimirs has common kernel `G_2` in the global matrix
algebra, not merely in a coefficient surrogate. Equation (4) remains
strictly stronger: it
controls every subspace of the singlet quotient and therefore supplies the
actual Hall quantifier required by operator scaling.  Its mechanism is not a
spectral gap.  It is resolved edge incidence: mismatch coordinates are
jointly faithful, each fixed Pauli edge map is injective on its mismatch
fibre, and different edges have disjoint defect support.

Together with `all-replica-local-casimir-hall-expansion.md`, the two-replica
Pauli Hall problem is now proved separately on both canonical layers:

1. weight-one generators expand every subspace of `S_2^perp`;
2. weight-two generators expand every subspace of `S_2/G_2`.

The remaining two-replica issue is the mixed-subspace gluing theorem.

## Hostile audit

- Separate Hall laws on `S_2/G_2` and `S_2^perp` do not automatically imply
  Hall for an arbitrary subspace crossing both layers; their output spans
  can overlap inside `S_2^perp`.
- The proof uses the special two-replica local commutant
  `span{I,F}`.  At higher replica order the local singlet algebra is a
  quotient of the permutation algebra, and a new permutation-incidence
  theorem is required.
- Connectedness is necessary.  For a disconnected graph, one independent
  constant swap label survives on each connected component.
- The theorem proves rank nondecrease only.  It supplies no quantitative
  operator-scaling condition number, matrix-semicircle regularity, long-time
  cavity decay, or circuit anti-concentration by itself.

## Formal progress log

- 2026-08-04 — `TwoReplicaGlobalSingletEdgeCasimirBridge.lean` closed the
  physical global Casimir gap. It proves explicit coefficient recovery,
  exact weight-two support, edge-extension multiplication, literal
  physical/coefficient intertwinement and the connected-graph two-mode common
  kernel. Capstone axiom audits use only `propext`, `Classical.choice` and
  `Quot.sound`. This does not formalize the fixed-orientation
  single-commutator Hall assembly in equations (7)--(17).
- No standalone novelty claim is made before external priority review.

## Next exact theorem

Use `visible-kernel-recovery-hall-law.md`. Independent edge-character outputs
define visible quotient detector `F`. Its range pays singlet directions not
already hidden in nonsinglet input. On `ker F`, every first edge image belongs
to nonsinglet input, so a second generator application produces edge-Casimir
recovery in singlet layer. Exact synchronization makes this recovery injective
after quotienting global identity and global swap. This avoids unsupported
claim that weight-one strictness surplus must dominate full overlap.

## Formal bridge status

The dimension argument in (14)--(17) is now formalized independently of the
Pauli coordinates in `HTGeometry/ResolvedFiberHallExpansion.lean`.  It states
that an injective stacked resolver followed by an injective assembly of its
resolved fibres cannot shrink any subspace.  This packages both quantifiers
that the common-kernel theorem lacked: arbitrary input subspace and the whole
edge family at once.

This card remains Stage 2.  Exact physical completion still requires three
concrete maps: the mismatch coordinate projections on the synchronized
quotient, the fixed-orientation Pauli commutator on each mismatch fibre, and
the injection assembling distinct edge-defect sectors into the full
Hilbert--Schmidt space.

Progress against that list:

- **`(7)` closed.**  `HTGeometry/TwoReplicaEdgeCommutatorSwapBasis.lean` gives all four values of
  one fixed-orientation edge commutator on the local identity/swap basis:
  `twoReplicaEdgeCommutator_one_one` and `..._swap_swap` are zero, while `..._one_swap` and
  `..._swap_one` are the negated products of replica differences `D_a = σ_a ⊗ I - I ⊗ σ_a`.  The
  proof is the swap relations applied once at each endpoint — the card's `(6)` — with no spectral
  input.  `twoReplicaLocalDiff_mul_swap` records that the swap anticommutes with `D_a`, which is
  what makes the two mismatched outputs independent.
- **`(13)` available.**  The connected-graph common-kernel classification is
  `finiteTwoReplicaPhysical_connectedGraph_kernel_iff`: vanishing on every edge forces the Boolean
  word to be constant, which is exactly `⋂_e ker P_e = G_2` in swap coordinates.
- **`(8)` closed.**  `twoReplicaLocalDiff_sq` is `D_a^2 = 2I - 2 sigma_a ⊗ sigma_a`, giving
  `trace_twoReplicaLocalDiff_sq : Tr(D_a^2) = 8`; and
  `trace_twoReplicaLocalDiff_mul_swap_mul_diff : Tr(D_a F D_a) = 0`.  The orthogonality proof is
  not the card's trace expansion: `D_a F = -F D_a` (`twoReplicaLocalDiff_mul_swap`) turns it into
  `-Tr(F D_a^2)`, and `Tr(F) = 2` cancels against `Tr((sigma_a ⊗ sigma_a) F) = 2`.  The latter is
  itself structural — `sigma_a ⊗ sigma_a = L_a R_a` and `R_a F = F L_a` reduce it to `Tr(F)`.
- **Remaining:** the orthogonality of distinct edge output sectors `(11)`, and the assembly
  `(14)`--`(17)` into `ResolvedFiberHallExpansion`.

`HTGeometry/TwoReplicaCliffordTwirlHallSymmetryReduction.lean` additionally
proves, in both exact matrix conventions, that the canonical greatest local
Hall obstruction is invariant under the strict doubled Clifford group and
splits under its idempotent average into `span{I,F}` plus the zero-twirl
kernel. This supplies the local identity/swap layer used here without the
invalid inference that second-design commutant completeness controls every
invariant operator subspace. The arbitrary-register product lift remains a
separate formal obligation.
