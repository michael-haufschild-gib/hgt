# All-replica fixed-edge singlet Hall expansion law

- **ID:** `all-replica-fixed-edge-singlet-hall-expansion-law`
- **Stage:** 3 -- formalized in Lean 4
- **Type:** THEOREM (paper)
- **Source:** `../1-in-progress/static-local-complexity-law.md`, growing-replica planar-cavity core
- **Status:** `[LEAN-CERTIFIED] [UNCONDITIONAL] [NOVELTY UNVERIFIED]`
- **Statement:** On every finite connected qubit interaction graph and at every finite replica
  order, one fixed Pauli orientation on each edge expands every subspace of the sitewise collective
  singlet sector modulo the exact global collective commutant.

## Goal

Close the precise higher-replica obstruction left by
`all-replica-local-casimir-hall-expansion.md`.  Weight-one collective Pauli commutators already
expand every subspace orthogonal to the sitewise singlet sector.  The missing theorem was one-step
weight-two Hall expansion inside that singlet sector, with only global replica-permutation modes
allowed to survive.

The proof below does not extrapolate the two-replica bit-string argument.  At higher replica order,
local singlets have large multiplicities and individual edge maps need not be injective.  The new
mechanism is instead:

1. every edge commutator creates a nonsinglet defect at both endpoints;
2. distinct graph edges therefore land in orthogonal defect sectors; and
3. connected local controllability identifies the joint edge kernel with the global collective
   commutant.

Joint faithfulness, not edgewise injectivity, is enough for the Hall inequality.

## Setup

Let `G=(I,E)` be a finite connected simple graph with at least two vertices.  Let

\[
  h=\mathbb C^2,
  \qquad H=h^{\otimes I},
  \qquad \mathcal H_r=H^{\otimes r}
\]

for an arbitrary finite replica order `r>=1`.  Regrouping tensor factors by physical site gives

\[
  \mathcal H_r\cong \bigotimes_{i\in I} h_i^{\otimes r},
  \qquad
  \mathcal V_r=\operatorname{End}(\mathcal H_r)
    \cong\bigotimes_{i\in I}\operatorname{End}(h_i^{\otimes r}),             \tag{1}
\]

with Hilbert--Schmidt inner product.

At site `i`, let

\[
  \mathcal S_{i,r}
   =\{X\in\operatorname{End}(h_i^{\otimes r}):
       [X,U^{\otimes r}]=0\text{ for every }U\in SU(2)\}.                    \tag{2}
\]

The sitewise singlet sector is

\[
  \mathcal S_r=\bigotimes_{i\in I}\mathcal S_{i,r}\subseteq\mathcal V_r.   \tag{3}
\]

Equivalently, it is the simultaneous kernel of all weight-one replicated Pauli commutators at all
physical sites.

Fix one Pauli axis `a_i(e)` at each endpoint `i` of every edge `e={i,j}`.  No genericity or
variation of these axes is assumed; they may all be `X`.  Define

\[
  Q_e=\sum_{\ell=1}^{r}
    \sigma_{a_i(e)}^{(i,\ell)}\sigma_{a_j(e)}^{(j,\ell)},
  \qquad
  A_e=\operatorname{ad}_{Q_e}.                                             \tag{4}
\]

Let the exact global collective commutant be

\[
  \mathcal N_r
   =\{X\in\mathcal V_r:[X,M^{\otimes r}_{\rm coll}]=0
       \text{ for every }M\in\operatorname{End}(H)\},                       \tag{5}
\]

where infinitesimally `M_coll` means `sum_l M^(l)`.  Equivalently, `N_r` is the commutant of the
diagonal `GL(H)` action.  Replica-position permutations lie in `N_r`; Schur--Weyl duality identifies
`N_r` with their linear span.  They are linearly independent in the stable range `r<=dim H=2^|I|`.

## Theorem 1: local singlet multiplication has zero singlet component

For every site `i`, replica `ell`, Pauli axis `a`, and local singlets
`X,Y in S_(i,r)`,

\[
 \langle Y,\sigma_a^{(i,\ell)}X\rangle_{\rm HS}=0,
 \qquad
 \langle Y,X\sigma_a^{(i,\ell)}\rangle_{\rm HS}=0.                           \tag{6}
\]

Consequently both left and right multiplication of a local singlet by one single-replica Pauli
land in `S_(i,r)^perp`.

### Proof

For the first inner product, cyclicity gives

\[
 \operatorname{Tr}(Y^*\sigma_a^{(\ell)}X)
 =\operatorname{Tr}(XY^*\sigma_a^{(\ell)}).                                 \tag{7}
\]

The product `Z=XY*` is a local singlet.  Choose a Pauli axis `b` orthogonal to `a` and let
`U=exp(-i pi sigma_b/2)` be the corresponding half-turn, up to an irrelevant phase.  Diagonal
conjugation by `U^(tensor r)` fixes `Z` and sends `sigma_a^(ell)` to `-sigma_a^(ell)`.  Trace
invariance therefore makes the right side of (7) equal to its negative, so it is zero.  Applying
the same argument after cyclically moving the final Pauli proves the second identity.  No
representation classification is used.  `square`

## Theorem 2: different edges have orthogonal endpoint-defect images

For `e={i,j}`, define

\[
 \mathcal D_e
 =\mathcal S_{i,r}^{\perp}\otimes\mathcal S_{j,r}^{\perp}
    \otimes\bigotimes_{k\notin\{i,j\}}\mathcal S_{k,r}.                     \tag{8}
\]

Then

\[
  A_e(\mathcal S_r)\subseteq\mathcal D_e,                                  \tag{9}
\]

and for distinct simple-graph edges

\[
  \mathcal D_e\perp\mathcal D_f.                                           \tag{10}
\]

### Proof

It suffices to apply `A_e` to a pure tensor `X=otimes_k X_k` with each `X_k` locally singlet.  Each
replica summand of the commutator is

\[
 (\sigma_a^{(i,\ell)}X_i)\otimes
 (\sigma_b^{(j,\ell)}X_j)
 - (X_i\sigma_a^{(i,\ell)})\otimes
   (X_j\sigma_b^{(j,\ell)})                                                  \tag{11}
\]

tensored with the unchanged local singlets away from the edge.  Theorem 1 puts both endpoint
factors in the corresponding orthogonal complements, proving (9) by linearity.

If `e!=f`, their endpoint sets have nonempty symmetric difference.  At a vertex in that symmetric
difference, one defect sector has local factor `S_(i,r)^perp` and the other has local factor
`S_(i,r)`.  Tensor-product Hilbert--Schmidt orthogonality proves (10).  `square`

## Theorem 3: exact synchronized edge kernel

For a connected graph,

\[
 \boxed{\qquad
  \mathcal S_r\cap\bigcap_{e\in E}\ker A_e=\mathcal N_r.
 \qquad}                                                                    \tag{12}
\]

This holds for every finite replica order and for every fixed choice of one nonidentity Pauli axis
at each edge endpoint.

### Proof

Take `X` in the left side.  Membership in `S_r` says that `X` is invariant under independent
collective `SU(2)` rotations at every physical site.  Fix an edge `e={i,j}`.  Conjugating
`[Q_e,X]=0` by arbitrary independent collective rotations at `i` and `j` preserves `X` and rotates
the two fixed Pauli axes independently.  The orbit of a Pauli matrix spans the traceless Hermitian
one-qubit matrices.  By bilinearity,

\[
 \left[X,\sum_{\ell=1}^r
      \sigma_a^{(i,\ell)}\sigma_b^{(j,\ell)}\right]=0                       \tag{13}
\]

for every pair of Pauli axes `a,b` and every graph edge.

The sitewise-singlet condition already gives commutation with every replicated weight-one Pauli
direction.  On a connected qubit graph, all one-site Pauli directions together with all two-site
Pauli directions on graph edges Lie-generate `su(2^|I|)`.  For completeness, this standard
controllability statement follows by adjoining vertices along a spanning tree: `su(2^m)` on the
grown connected block, `su(2)` on the new qubit, and any nonzero product coupling across the next
edge generate

\[
 (su(2^m)\otimes I)\oplus(I\otimes su(2))
 \oplus(su(2^m)\otimes su(2))=su(2^{m+1}),                                  \tag{14}
\]

because local adjoint commutators span each tensor factor.  Induction closes the graph.

Diagonal replication is a Lie homomorphism:

\[
 \left[\sum_\ell P^{(\ell)},\sum_\ell R^{(\ell)}\right]
 =\sum_\ell[P,R]^{(\ell)}.                                                  \tag{15}
\]

Equations (13)--(15) therefore show that `X` commutes with every collective physical matrix
direction, so `X in N_r`.

Conversely, a global collective-commutant element commutes with every weight-one and edge
direction, hence belongs to the left side.  This proves (12).  `square`

## Theorem 4: all-replica fixed-edge Hall expansion

For every complex linear subspace `U<=S_r`,

\[
 \boxed{\qquad
  \dim U
  \leq
  \dim\operatorname{span}\{A_eU:e\in E\}
  +\dim(U\cap\mathcal N_r).
 \qquad}                                                                    \tag{16}
\]

Equivalently, the induced fixed-edge family is rank nondecreasing on every subspace of the quotient
`S_r/N_r`:

\[
 \boxed{\qquad
  \dim\operatorname{span}\{\overline A_e\overline U:e\in E\}
  \geq\dim\overline U
  \quad\text{for every }\overline U\leq\mathcal S_r/\mathcal N_r.
 \qquad}                                                                    \tag{17}
\]

### Proof

Stack all edge maps on `U`:

\[
 T_U:U\longrightarrow\bigoplus_{e\in E}\mathcal D_e,
 \qquad u\longmapsto(A_eu)_{e\in E}.                                      \tag{18}
\]

Theorem 3 and rank--nullity give

\[
 \operatorname{rank}T_U
   =\dim U-\dim(U\cap\mathcal N_r).                                         \tag{19}
\]

Theorem 2 makes the actual edge images pairwise orthogonal, hence

\[
\begin{aligned}
 \dim\operatorname{span}\{A_eU:e\in E\}
   &=\sum_{e\in E}\dim A_eU\\
   &\geq \operatorname{rank}T_U.                                            \tag{20}
\end{aligned}
\]

Combining (19) and (20) proves (16).  For a quotient subspace `Ubar`, choose a linear lift
`U<=S_r` disjoint from `N_r`.  All `A_e` annihilate `N_r`, so the output is independent of the
lift; (16) becomes (17).  `square`

## Stable-range corollary

Schur--Weyl duality identifies `N_r` with the span of global replica-position permutations.  If

\[
 r\leq\dim H=2^{|I|},                                                        \tag{21}
\]

these `r!` permutation operators are linearly independent.  Hence every `U<=S_r` obeys

\[
 \dim U\leq\dim\operatorname{span}_{e\in E}A_eU+r!,                         \tag{22}
\]

and the defect in (16) is the exact intersection with this `r!`-dimensional global sector, not the
much larger sitewise singlet algebra.

Outside the stable range, (16)--(17) remain exact with `N_r` itself.  Only the numerical formula
`dim N_r=r!` is lost because permutation operators become linearly dependent.

## Why this is stronger than the two-replica proof

The formalized two-replica theorem resolved local singlets into `I/F` bit strings and proved each
edge map injective on its endpoint-mismatch coordinates.  That mechanism does not scale directly:
higher-replica local commutants have multiplicities and nontrivial edgewise kernels.

The proof above shows edgewise injectivity was never necessary.  For any family of maps with
pairwise orthogonal ranges,

\[
 \operatorname{rank}(A_1,\ldots,A_m)
 \leq\sum_j\operatorname{rank}A_j
 =\dim\sum_j A_jU.                                                           \tag{23}
\]

Thus only the common kernel must be classified.  Connected Pauli controllability performs that
classification uniformly at every replica order.

At `r=2`, (17) recovers the previous theorem without the local swap-coordinate calculation.  At
arbitrary `r`, it closes the exact theorem named open in
`all-replica-local-casimir-hall-expansion.md`.

## Conjecture attack log

1. **Conjecture:** every individual fixed edge is injective on a canonical higher-replica mismatch
   sector.  **Rejected as unnecessary and likely false.** Local singlet multiplicities create
   edgewise kernels.
2. **Conjecture:** one must prove a higher-replica permutation-incidence theorem generalizing the
   two-replica cut map.  **Rejected as overfitted.** Stacking arbitrary edge maps already exposes
   the common kernel.
3. **Conjecture:** distinct edge images of sitewise singlets are orthogonal because each edge creates
   exactly two local nonsinglet defects.  **Proved** by the half-turn trace-flip lemma.
4. **Conjecture:** the synchronized fixed-axis edge kernel equals the full collective commutant.
   **Proved** by independent local rotation, connected graph controllability, and diagonal Lie
   replication.
5. **Conjecture:** orthogonal edge defects plus synchronized-kernel classification imply Hall
   expansion on every singlet quotient subspace.  **Proved** by one stacked-map rank argument.

## Relation to nearby external results

Known local-random-circuit moment operators have permutation ground spaces, and swap-algebra methods
describe invariant sectors.  Operator-scaling literature supplies general rank-nondecreasing/Hall
criteria.  Those are adjacent ingredients, not the argument above.  The present theorem concerns
one deterministic fixed interaction orientation per physical edge and obtains an all-subspaces
Hall law from endpoint-defect orthogonality plus controllability.

Searches against the local-design/moment-Hamiltonian literature and operator-Hall terminology found
no exact theorem with this statement.  This is negative search evidence, not a priority claim.
External novelty remains unverified until specialist review.

## Consequence for the Brown--Susskind frontier

This theorem closes the all-replica **singlet-layer** Hall obstruction.  Combined with the existing
all-replica local-Casimir theorem, both canonical layers now expand at every finite replica order:

1. weight-one collective commutators expand every subspace of `S_r^perp`;
2. one fixed weight-two commutator per connected graph edge expands every subspace of `S_r/N_r`.

This is a genuine frontier reduction: higher-replica permutation incidence is no longer the missing
mathematics.  The next exact issue is mixed-layer gluing for arbitrary subspaces crossing `S_r` and
`S_r^perp`.  Separate Hall laws do not automatically glue because weight-two images from `S_r` can
overlap weight-one or weight-two images from `S_r^perp`.

Even a mixed-layer Hall theorem would establish rank fullness, not a quantitative smallest
singular-value bound, quenched growing-replica lower tail, finite-volume cavity decay rate, or Brown
complexity ramp.  None of those claims follows here.

## Hostile audit

- **No hidden genericity.** Axes are arbitrary fixed nonidentity Pauli axes; all edges may use the
  same orientation.
- **Connectedness is load-bearing.** On a disconnected graph the common kernel contains one
  independent collective commutant per connected component.  The theorem then holds componentwise
  with that larger exact defect, not with `N_r`.
- **Simple graph is used for orthogonality.** Parallel interactions on the same endpoint pair share
  the same defect sector.  Keeping one representative edge restores the theorem.
- **Qubit local rotations are load-bearing.** The proof extends to local dimensions only when the
  chosen fixed endpoint observables have adjoint orbits spanning the needed local Lie algebra.
- **The quotient is exact.** Outside stable range, replacing `N_r` by an abstract `r!`-dimensional
  space would be false because global permutation operators are linearly dependent.
- **One-step scope is precise.** The result is one-step on the singlet quotient only.  It does not
  establish one-step Hall expansion for arbitrary mixed subspaces of the full replicated operator
  space.
- **Rank is not conditioning.** Hall expansion gives no uniform lower bound on pseudodeterminants or
  singular values.  Approximate tubes and a complete circuit union need quantitative control.
- **No physics overclaim.** No complexity growth, plateau, recurrence, black-hole, thermodynamic,
  or locality conclusion is authorized by this theorem alone.
- **Novelty is open.** Corpus comparison is complete for the named route; external priority remains
  subject to specialist literature review.

## Formalization status

Lean work is intentionally deferred while the corpus is being refactored.  Existing formal modules
already provide the weight-one singlet definition, replicated Pauli commutators, full two-local Lie
generation, and stable-range collective-commutant classification.  Missing formal content is the
half-turn trace-flip lemma, endpoint-defect tensor orthogonality, connected-edge controllability in
the exact graph convention, and the stacked-map quotient Hall assembly.  No formal theorem is
claimed by this card.

## Mixed-layer target — closed on the next card

`all-replica-one-step-local-pauli-hall-saturation-law.md` proves the required mixed-layer gluing law
for the complete weight-one and graph-edge weight-two Pauli family.  Its proof uses the canonical
greatest maximum-defect subspace, continuous product-local rotation covariance, the all-replica
Pauli-character visible detector, and the full nine-orientation positive edge Casimir.  Fixed
orientations remain sufficient for this card's singlet Hall theorem; all orientations are
load-bearing only for mixed hidden-kernel recovery.

## Log

- 2026-08-10 — conjectured endpoint-defect mechanism after higher-replica incidence route stalled.
- 2026-08-10 — proved local trace-flip orthogonality, pairwise edge-sector orthogonality, exact
  synchronized kernel, and all-subspaces quotient Hall inequality at every finite replica order.
- 2026-08-10 — hostile audit isolates mixed-layer gluing and quantitative conditioning as remaining
  frontier; Lean deferred during corpus refactor.

## Lean certificate

Every statement of this card is proved unconditionally in Lean 4 inside
`formal/GaloisForLFunctions/HTGeometry/`.  All declarations audit to
`[propext, Classical.choice, Quot.sound]`.

Sites are a finite type `I`, replicas a finite type `R`; the qubit register is indexed by `I × R`
and operators are vectorised over `FiniteAllReplicaOperatorIndex I R`.

| Equation | Declaration | Module |
|---|---|---|
| `(1)` | `FiniteAllReplicaOperatorIndex`, `matrixCommutatorRepresentation` | `AllReplicaCollectivePauliCasimir` |
| `(2)`, `(3)` | `finiteAllReplicaCollectiveSingletSubspace`, `mem_singlet_iff` | `CentralCasimirCommonKernelCorrection`, `FixedEdgeSingletDefect` |
| `(4)` | `fixedEdgeCollectivePauli`, `fixedEdgeCommutatorMatrix` | `FixedEdgeCollectivePauli`, `FixedEdgeSingletDefect` |
| `(5)` | `collectivePauliString`, `collectiveCommutantSubspace` | `CollectivePauliString`, `FixedEdgeSingletHallCommutant` |
| `(6)`, `(7)` | `siteCollectiveCasimir_fixedEdge_left/right` | `FixedEdgeSingletDefect` |
| `(8)`, `(9)` | `siteCollectiveCasimir_fixedEdge_notMem` | `FixedEdgeSingletDefect` |
| `(10)`, `(11)` | `inner_fixedEdge_eq_zero_of_separating`, `inner_edgeMap_eq_zero` | `FixedEdgeSingletDefect`, `FixedEdgeSingletHall` |
| `(12)` | `collectivePauliString_commutator_apply_eq_zero_of_fixed`, `singlet_and_edge_of_collectivePauliString_commutator` | `CollectivePauliString` |
| `(13)` | `fixedEdge_apply_eq_zero_of_axes` | `FixedEdgeSingletDefect` |
| `(14)` | `label_mem_of_connected` | `PauliLabelGraphGeneration` |
| `(15)` | `collectivePauliString_bracket` | `CollectivePauliString` |
| `(16)` | `finrank_le_edgeImages_add_collectiveCommutant` | `FixedEdgeSingletHallCommutant` |
| `(17)` | `finrank_le_edgeImages_add_kernel` | `FixedEdgeSingletHall` |
| `(18)`–`(20)`, `(23)` | `edgeSumMap_apply_eq_zero_iff` | `FixedEdgeSingletHall` |
| `(21)`, `(22)` | `finrank_collectiveCommutantSubspace_le_factorial`, `finrank_le_edgeImages_add_factorial` | `FixedEdgeSingletStableRange` |

Three parts of the formal proof depart from the paper argument.

Theorems 1 and 2 are obtained without the tensor-factor defect sectors `D_e` and without the
half-turn trace-flip lemma.  The edge image of a singlet is exhibited as an eigenvector of each
endpoint's collective quadratic Casimir with the nonzero adjoint eigenvalue `8`
(`pauliStructureCoeff_double_contraction`), while at a site off the edge it stays in that Casimir's
kernel.  Self-adjointness of the Casimir then gives orthogonality directly, so no
commutant-of-a-tensor-factor theorem is needed.

Theorem 4 uses the single map `∑_e A_e` instead of the stacked map into `⊕_e D_e`.  Orthogonality
of the edge images of one vector makes that sum have the same kernel as the whole family
(`edgeSumMap_apply_eq_zero_iff`), so rank–nullity for one linear map suffices and no direct-sum
dimension formula for an orthogonal family is required.

Theorem 3's controllability input `(14)` is proved at the level of Pauli labels on the site type
rather than by the spanning-tree induction on `su(2^m)`.  The collective bracket law
`[C_P, C_Q] = (Γ(P,Q) − Γ(Q,P)) · C_{P·Q}` makes the commuting labels closed under products of
anticommuting labels; two adjacent edges then produce the far pair by a two-bracket identity, a
walk induction propagates it, and a heavier label is the product of a two-site label with a
strictly lighter one.  A separate `Fin 4`-encoded version of the same controllability statement for
matrix generators is available as
`dynamicalLieAlgebra_graphTwoLocalPauliMatrices_eq_tracelessLie` in `GraphEdgeLieGeneration`.

The stable-range corollary `(22)` reuses the corpus's Schur–Weyl bound
`finiteReplicaCollectiveCommutant_finrank_le_factorial` through the replica regrouping
`configCurry`, the relabelling `piRelabelEquiv`, and the vectorisation `vecLinearEquiv`
(`ReplicaConfigurationBridge`); `bridgeMap` is the resulting injection of the collective commutant
into the corpus's indexing.
