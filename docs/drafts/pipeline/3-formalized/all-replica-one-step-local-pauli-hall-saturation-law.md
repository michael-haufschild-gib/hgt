# All-replica one-step local-Pauli Hall saturation law

- **ID:** `all-replica-one-step-local-pauli-hall-saturation-law`
- **Stage:** 3 -- formalized in Lean 4
- **Type:** THEOREM (paper)
- **Source:** `../1-in-progress/static-local-complexity-law.md`, growing-replica planar-cavity core
- **Status:** `[LEAN-CERTIFIED] [UNCONDITIONAL] [NEW MECHANISM; PRIORITY UNVERIFIED]`
- **Statement:** On every finite connected qubit graph and at every finite replica order, the
  complete one-site and graph-edge two-site replicated Pauli commutator family is one-step rank
  nondecreasing modulo exactly the global collective commutant.

## Goal

Close the arbitrary mixed-subspace gap left after the two canonical layers were solved separately.
The prior corpus proves:

1. weight-one collective Pauli commutators expand every subspace orthogonal to the sitewise
   collective-singlet sector; and
2. `all-replica-fixed-edge-singlet-hall-expansion-law.md` proves fixed-edge expansion inside the
   singlet sector modulo the global collective commutant.

Separate layerwise Hall laws do not generally glue.  This card proves that the concrete local-Pauli
family has enough symmetry and quadratic return structure to force gluing at the unique canonical
worst subspace.  This removes the all-replica one-step Hall obstruction; quantitative conditioning
and quenched growing-replica probability remain separate.

## Setup

Let `G=(I,E)` be a finite connected simple graph with at least two vertices, let

\[
 H=(\mathbb C^2)^{\otimes I},
 \qquad \mathcal H_r=H^{\otimes r},
 \qquad \mathcal V_r=\operatorname{End}(\mathcal H_r)                       \tag{1}
\]

for arbitrary finite `r>=1`, and equip `V_r` with the Hilbert--Schmidt inner product.

For every nonidentity one-site Pauli word `p` and every nonidentity two-site Pauli word supported on
an edge of `G`, define

\[
 Q_p^{(r)}=\sum_{\ell=1}^{r}p^{(\ell)},
 \qquad A_p^{(r)}=\operatorname{ad}_{Q_p^{(r)}}.                            \tag{2}
\]

Let `P_G` denote this complete weight-one/graph-edge weight-two label set and put

\[
 \mathfrak A_{G,r}=\{A_p^{(r)}:p\in\mathcal P_G\}.                          \tag{3}
\]

Let `S_r` be the sitewise collective-singlet sector, as in the fixed-edge card, and put

\[
 W_r=\mathcal S_r^\perp.                                                     \tag{4}
\]

Let `N_r` be the exact commutant of every collectively replicated physical matrix.  Connected Pauli
controllability gives

\[
 \mathcal N_r=\bigcap_{p\in\mathcal P_G}\ker A_p^{(r)}.                    \tag{5}
\]

Schur--Weyl duality identifies `N_r` with the span of global replica-position permutations.  No
stable-range assumption is used below.

Because every `A_p` is self-adjoint and annihilates `N_r`, the orthogonal complement

\[
 \mathcal V_r^0=\mathcal N_r^\perp                                          \tag{6}
\]

is invariant.  Work first on `V_r^0`, where the family has trivial common kernel.  Its canonical
orthogonal splitting is

\[
 \mathcal V_r^0=\mathcal S_r^0\oplus\mathcal W_r,
 \qquad \mathcal S_r^0=\mathcal S_r\cap\mathcal N_r^\perp.                 \tag{7}
\]

## Theorem 1: exact Hall law

For every complex linear subspace `U<=V_r`,

\[
 \boxed{\qquad
  \dim U
  \leq
  \dim\operatorname{span}\{A_p^{(r)}U:p\in\mathcal P_G\}
   +\dim(U\cap\mathcal N_r).
 \qquad}                                                                    \tag{8}
\]

Equivalently, on the quotient by the exact collective commutant,

\[
 \boxed{\qquad
  \dim\operatorname{span}\{\overline A_p^{(r)}\overline U:
          p\in\mathcal P_G\}
   \geq\dim\overline U
  \quad\text{for every }\overline U\leq\mathcal V_r/\mathcal N_r.
 \qquad}                                                                    \tag{9}
\]

The result holds at every finite replica order, in one application of the literal local generator
family, with no genericity, spectral-gap, asymptotic, or probabilistic assumption.

## Proof architecture

The proof needs only the canonical greatest maximum-defect subspace, not an arbitrary decomposition
of every candidate subspace.

For a finite linear family `A` on a finite-dimensional space define

\[
 \operatorname{Sh}_A(U)=\operatorname{span}_p A_pU,
 \qquad
 \delta_A(U)=\dim U-\dim\operatorname{Sh}_A(U).                             \tag{10}
\]

Deficiency is supermodular.  Therefore it has a unique greatest maximizer `U_*`: it contains every
other maximum-defect subspace.  Since `delta_A(0)=0`, the all-subspaces Hall law is equivalent to

\[
 \delta_A(U_*)=0.                                                           \tag{11}
\]

Apply this on `V_r^0`.  We prove `dim Sh_A(U_*)>=dim U_*`.

## Lemma 2: product-local rotation invariance of the canonical obstruction

Let `g=(g_i)_(i in I) in SU(2)^I` and let `T_g` be conjugation by the collectively replicated
product unitary on `V_r^0`.  Then

\[
 T_g\,\operatorname{span}(\mathfrak A_{G,r})\,T_g^{-1}
   =\operatorname{span}(\mathfrak A_{G,r}),                                \tag{12}
\]

and consequently

\[
 T_gU_*=U_*.                                                                \tag{13}
\]

### Proof

The adjoint action of one-qubit `SU(2)` rotates the three Pauli matrices by a real orthogonal
`3 times 3` matrix.  A product-local rotation therefore maps a weight-one physical Pauli into the
linear span of weight-one Paulis on the same site and maps an edge Pauli into the nine-dimensional
edge-Pauli span on the same edge.  Replication and commutator formation are linear, proving (12).
The inverse rotation gives equality in both directions.

Thus `T_g Sh_A(U)=Sh_A(T_gU)` and deficiency is invariant.  The unique greatest maximizer must be
fixed by every such symmetry, proving (13).  `square`

## Lemma 3: reducing singlet split and internal reproduction of the nonsinglet layer

The product-local Haar projector onto `S_r` preserves `U_*`.  Hence

\[
 U_*=U_S\oplus U_W,
 \qquad
 U_S=U_*\cap\mathcal S_r^0,
 \qquad
 U_W=U_*\cap\mathcal W_r.                                                   \tag{14}
\]

Moreover the literal weight-one family reproduces `U_W` internally:

\[
 \boxed{\qquad
 U_W=\operatorname{span}_{\operatorname{wt}(p)=1}A_p^{(r)}U_W.
 \qquad}                                                                    \tag{15}
\]

### Proof

Equation (13) says every product-local rotation preserves `U_*`.  Averaging these rotations
therefore preserves `U_*`; the average is the orthogonal projector onto the product-group fixed
space `S_r`.  This proves (14).

Differentiate the invariant curve `T_(exp(t sigma))U_*=U_*` at `t=0`.  Its infinitesimal action is,
up to a nonzero scalar, the corresponding weight-one collective commutator.  Therefore every
weight-one `A_p` preserves `U_*`.  It annihilates `S_r` and, by self-adjointness, preserves `W_r`, so

\[
 A_pU_W\subseteq U_W.                                                       \tag{16}
\]

The all-replica local-Casimir Hall theorem gives

\[
 \dim\operatorname{span}_{\operatorname{wt}(p)=1}A_pU_W\geq\dim U_W.       \tag{17}
\]

The left side is the dimension of a subspace of `U_W` by (16); equality and (15) follow. `square`

## Lemma 4: all edge orientations form independent character outputs on singlets

For a physical phase-free Pauli word `q`, let `C_q` be conjugation on `V_r` by `q` applied in every
replica.  The `C_q` are commuting unitary involutions.  For every edge Pauli `p`,

\[
 C_q A_p C_q^{-1}=(-1)^{[q,p]}A_p,                                         \tag{18}
\]

where `[q,p]` is the nondegenerate Pauli symplectic pairing.  Every `s in S_r` is fixed by all
`C_q`, so `A_ps` lies in the exact simultaneous character grade labelled by `p`.  Distinct edge
Pauli words have distinct characters.  Consequently

\[
 A_p(\mathcal S_r)\perp A_{p'}(\mathcal S_r)
 \quad(p\ne p'),                                                            \tag{19}
\]

and the aggregate map

\[
 L:\mathcal S_r^0\longrightarrow\mathcal W_r,
 \qquad Ls=\sum_{\operatorname{wt}(p)=2,\ \operatorname{supp}(p)\in E}A_ps \tag{20}
\]

is injective.

### Proof

Conjugating a physical Pauli by another physical Pauli supplies exactly the sign in (18), on every
replica summand.  Commutation of the conjugation involutions is unaffected by Pauli phases.  The
symplectic form separates distinct phase-free Pauli labels, so their simultaneous characters are
distinct and their unitary eigenspaces are orthogonal.  This proves (19).

If `Ls=0`, orthogonality makes every edge image `A_ps` zero.  The synchronized-kernel theorem from
the fixed-edge card already shows that even one orientation per edge has common kernel `N_r` on
`S_r`.  Thus `s in N_r`; since `s in S_r^0`, it is zero.  Hence `L` is injective.  The local
trace-flip lemma in that card also gives `A_p(S_r) subset W_r`, so (20) has the stated codomain.
`square`

## Lemma 5: visible quotient detector

Let

\[
 C=\operatorname{span}_{\operatorname{wt}(p)=2}A_pU_S\subseteq W_r          \tag{21}
\]

and define

\[
 F:U_S\longrightarrow W_r/U_W,
 \qquad F(s)=L(s)+U_W.                                                       \tag{22}
\]

Then

\[
 \operatorname{rank}F+\dim U_W\leq\dim(U_W+C),                             \tag{23}
\]

and

\[
 s\in\ker F
 \quad\Longleftrightarrow\quad
 A_ps\in U_W\text{ for every edge Pauli }p.                                \tag{24}
\]

### Proof

The range of `F` is contained in `(U_W+C)/U_W`, giving (23).

By Lemma 2, `U_W` is invariant under every paired-Pauli conjugation `C_q`.  Finite character
projectors therefore preserve `U_W`.  If `F(s)=0`, then the sum `L(s)` belongs to `U_W`.  Projecting
onto the exact character grade `p` and using (19) gives `A_ps in U_W` separately for every `p`.
The converse follows by summation.  This proves (24). `square`

## Lemma 6: hidden-kernel edge-Casimir recovery

Define the full graph-edge Casimir

\[
 K_2=\sum_{\operatorname{wt}(p)=2,\ \operatorname{supp}(p)\in E}A_p^2.     \tag{25}
\]

Then

\[
 K_2(\mathcal S_r^0)\subseteq\mathcal S_r^0,
 \qquad
 K_2|_{\mathcal S_r^0}\text{ is injective}.                                \tag{26}
\]

For `D=ker F`,

\[
 K_2D\subseteq\operatorname{Sh}_{\mathfrak A_{G,r}}(U_W)\cap\mathcal S_r^0.
                                                                                \tag{27}
\]

### Proof

For each graph edge, summing `A_p^2` over all nine Pauli orientations is invariant under independent
rotations at its endpoints: orientation coefficients transform by orthogonal matrices and their
contracted squares are unchanged.  Thus `K_2` commutes with the product-local rotation action and
preserves its fixed space `S_r`.  It is self-adjoint and annihilates `N_r`, hence preserves
`S_r^0`.

Each `A_p` is Hilbert--Schmidt self-adjoint, so

\[
 \langle s,K_2s\rangle_{\rm HS}=\sum_{\operatorname{wt}(p)=2}\|A_ps\|^2.
                                                                                \tag{28}
\]

Therefore the kernel of `K_2` on `S_r` is the common edge kernel, exactly `N_r` by the synchronized
kernel theorem.  Its restriction to `S_r^0` is injective, proving (26).

If `s in D`, (24) gives `A_ps in U_W` for every edge label.  Hence

\[
 A_p^2s=A_p(A_ps)\in\operatorname{Sh}_{\mathfrak A_{G,r}}(U_W).
\]

Summation and (26) prove (27). `square`

## Mixed-layer assembly

The total one-step output from `U_*` contains `U_W+C`: it contains `U_W` by internal reproduction
(15), and it contains `C` by applying edge generators to `U_S`.  This space lies in `W_r`.

It also contains `K_2D` by (27), and this space lies in `S_r^0`.  The two pieces are orthogonal.
Injectivity of `K_2` on `D` gives `dim K_2D=dim D`.  Therefore

\[
\begin{aligned}
 \dim\operatorname{Sh}_{\mathfrak A_{G,r}}(U_*)
 &\geq \dim(U_W+C)+\dim K_2D\\
 &\geq \dim U_W+\operatorname{rank}F+\dim\ker F\\
 &=\dim U_W+\dim U_S\\
 &=\dim U_* .                                                               \tag{29}
\end{aligned}
\]

Thus `delta(U_*)<=0`.  Since zero subspace has deficiency zero and `U_*` maximizes deficiency,
`delta(U_*)=0`.  By the greatest-maximizer Hall criterion, every subspace of `V_r^0` expands.  This
proves (9).

For arbitrary `U<=V_r`, quotienting by `U cap N_r` loses exactly that dimension while every
generator kills `N_r`.  Lifting (9) gives (8). `square`

## Stable-range corollary

If `r<=dim H=2^|I|`, global replica-position permutations are linearly independent and
`dim N_r=r!`.  Thus

\[
 \dim U\leq\dim\operatorname{Sh}_{\mathfrak A_{G,r}}(U)+r!.                \tag{30}
\]

Equation (8) is sharper: it pays only `dim(U cap N_r)`.  Outside stable range, (8)--(9) remain exact
while the numerical factorial identity is replaced by the actual Schur--Weyl commutant dimension.

## What is new relative to the prior corpus

The prior all-replica theorem needed products of local generators of physical word depth at most
`|I|` to reach Hall expansion modulo the global collective commutant.  Equation (9) reduces that
depth from linear to exactly one for the complete graph-local Pauli family.

The prior one-step theorem paid the entire sitewise singlet dimension on a mixed subspace.  Equation
(8) reduces the defect to the exact global collective commutant at every replica order.

The proof combines four mechanisms which previously existed only separately or at two replicas:

1. greatest-defect symmetry reduction under continuous span covariance;
2. all-replica local-Casimir internal reproduction off the singlets;
3. all-replica Pauli-character separation of every edge orientation on singlet input; and
4. all-replica positive edge-Casimir recovery of hidden visible-detector kernel.

The key new observation is that Pauli-character separation and local-singlet input are
replica-order independent.  The two-replica visible-kernel proof therefore did not depend on the
two-dimensional local `span{I,swap}` commutant once singlet Hall and synchronized kernel were
replaced by their representation-free forms.

## Conjecture attack log

1. **Conjecture:** separate all-replica Hall laws on `S_r/N_r` and `W_r` glue abstractly.
   **Falsified.** A two-layer family can rotate nonsinglet input into the singlet forward image while
   its reverse coupling misses that input.
2. **Conjecture:** physical local-Casimir tightness alone forbids this crossing contraction.
   **Rejected.** Tightness proves rank nondecrease of the nonsinglet shadow, not internal
   reproduction for arbitrary input.
3. **Conjecture:** it suffices to test the unique greatest maximum-defect subspace, which is invariant
   under every continuous product-local symmetry normalizing the generator span. **Proved.** This
   makes the singlet projector reducing and the nonsinglet shadow internally reproducing.
4. **Conjecture:** edge orientations remain distinguishable at arbitrary replica order by paired
   Pauli-conjugation characters. **Proved.** The character sign acts on the physical Pauli label and
   is independent of replica multiplicity.
5. **Conjecture:** aggregate visible quotient rank plus the full edge Casimir recovers exactly the
   hidden kernel. **Proved.** Character projectors resolve hidden first images, and positive Casimir
   injectivity follows from the exact synchronized kernel.
6. **Conjecture:** the canonical obstruction has nonpositive deficiency, forcing the complete
   all-subspaces one-step Hall law. **Proved** by (29).

## Hostile audit

- **All edge orientations are required for recovery.** One fixed orientation per edge proves
  singlet Hall, but its square sum need not preserve the sitewise singlet sector.  The full nine-axis
  edge Casimir is load-bearing in (25)--(27).
- **Continuous family-span covariance is load-bearing.** Invariance under a finite Clifford group
  alone would not justify infinitesimal preservation by weight-one commutators.  Equation (12) uses
  the complete linear span of all Pauli axes and the full product-local `SU(2)` action.
- **Canonical reduction is essential.** The internal reproduction identity (15) is asserted only for
  the unique greatest maximum-defect subspace.  It is not true for arbitrary nonsinglet input.
- **Connectedness is essential.** A disconnected graph has a larger componentwise collective
  commutant.  The same proof applies after replacing `N_r` by that exact common kernel.
- **Rank, not conditioning.** Equation (9) gives no lower bound on the smallest nonzero singular
  value, capacity, pseudodeterminant, or operator-scaling convergence rate.
- **No probability theorem.** No quenched lower tail, approximate-tube bound, circuit-union
  estimate, or local-Hamiltonian ensemble transfer follows from rank saturation alone.
- **No cavity decay theorem.** Full rank rules out exact atoms forced by a deterministic kernel.  It
  does not establish a replica-uniform spectral density or a decay rate for a planar/free cavity
  propagator.
- **Finite volume only.** No thermodynamic-limit or continuous-spectrum claim occurs.
- **No complexity claim yet.** Brown growth, plateau, lifetime, and recurrence are not consequences
  of this card alone.
- **External novelty remains unverified.** Corpus comparison proves this is stronger than existing
  internal theorems.  Specialist priority review is still required before any novelty claim.

## Hostile external-priority audit — 2026-08-10

Targeted searches found no external statement matching (8)--(9).  Three neighboring results define
the boundary precisely.

1. Baer--Haah, [*Random unitary circuits with constant spectral gap*](https://arxiv.org/abs/2607.20919),
   prove a representation-uniform constant gap for a depth-two brickwork walk of independently
   Haar-random `SU(4)` gates.  Their path-average local-subgroup projector estimate also implies,
   by the positive minimum nontrivial `SU(4)` Casimir, a representation-uniform lower frame bound

   \[
    \sum_{p\in\mathcal P_G}\|A_px\|^2\ge c\|x\|^2
    \qquad(x\perp\mathcal N_r)                                             \tag{31}
   \]

   after fixed Pauli normalization, with `c>0` independent of physical size and replica order.
   This is a bound for the **generator-labelled stacked map** `x mapsto (A_px)_p`.  It neither proves
   common-output Hall expansion nor controls the completely positive operator
   `X mapsto sum_p A_p X A_p` after operator scaling.  Their gates are independently refreshed;
   they do not describe `exp(-itH)` for one time-independent random local Hamiltonian.
2. Chen--Haah--Haferkamp--Liu--Metger--Tan,
   [*Incompressibility and spectral gaps of random circuits*](https://arxiv.org/abs/2406.07478),
   prove robust Brown--Susskind growth for random circuits.  This confirms that the refreshed-circuit
   problem is solved in a strong regime and sharpens why transfer to one static Hamiltonian is the
   actual target; it does not imply such a transfer.
3. Kwok--Lau--Ramachandran,
   [*Spectral analysis of matrix scaling and operator scaling*](https://arxiv.org/abs/1904.03213),
   obtain quantitative capacity and scaling-condition bounds from a spectral gap of the
   **matrix representation of the completely positive map**, together with near double balance.
   The group-walk gap and frame coercivity (31) do not supply either premise for the commutator CP
   map.  Conflating these two spectral gaps would repeat the retired minimum-gap error.

Thus current theorem is not a disguised random-circuit spectral-gap result.  It supplies the exact
rank-nondecreasing premise which those external quantitative operator-scaling theorems need, but a
new proof of near balance and CP-map spectral expansion is still required before their capacity
bounds can be imported.

## Lean certificate

Every statement of this card is proved unconditionally in Lean 4 inside
`formal/GaloisForLFunctions/HTGeometry/`.  All declarations audit to
`[propext, Classical.choice, Quot.sound]`.

Sites are a finite type `I`, replicas a finite type `R`, the graph is any `SimpleGraph I`; the
qubit register is indexed by `I x R` and operators are vectorised over
`FiniteAllReplicaOperatorIndex I R`.  The generator index is
`GraphLocalIndex I G = (I x Fin 3) + {p // IsEdgeWord G p}`: the weight-one layer is indexed by a
site and a letter, the weight-two layer by the edge word itself, so the index map is injective --
which is what the character separation argument needs.

| Equation | Declaration | Module |
|---|---|---|
| `(1)`, `(2)` | `collectivePauliString`, `matrixCommutatorRepresentation`, `collectiveCommutatorOperator` | `CollectivePauliString`, `AllReplicaCollectivePauliCasimir`, `MatrixSandwichEquiv` |
| `(3)` | `GraphLocalIndex`, `graphLocalLabel`, `graphLocalGenerator` | `GraphLocalPauliFamily` |
| `(4)` | `finiteAllReplicaCollectiveSingletSubspace`, `singletSubspace_eq_familyCommonKernel` | `CentralCasimirCommonKernelCorrection`, `GraphLocalHallAssembly` |
| `(5)` | `graphLocalCommonKernel`, `graphLocalCommonKernel_eq_collectiveCommutant` | `GraphLocalCompletedFamily`, `GraphLocalHallSaturation` |
| `(6)` | `familyCommonKernel_orthogonal_eq`, `graphLocalReducedObstruction` | `SelfAdjointFamilyCommonKernel`, `GraphLocalHallAssembly` |
| `(7)`, `(14)` | `graphLocalReducedObstruction_le_split`, `invariantSubspace_le_commonKernel_sup_orthogonal` | `GraphLocalHallAssembly`, `HermitianFamilyCasimirSplit` |
| `(8)` | **`graphLocal_finrank_le_shadow_add_commonKernel`** | `GraphLocalHallSaturation` |
| `(9)` | **`graphLocal_finrank_le_shadow_of_le_orthogonal`**, `graphLocalCompleted_hall` | `GraphLocalHallSaturation` |
| `(10)`, `(11)` | `linearFamilyShadow`, `linearFamilyDefect`, `linearFamilyHall_iff_greatestMaximizer_defect_eq_zero` | `LinearFamilyDefectSupermodularity`, `LinearFamilyGreatestMaximizer` |
| `(12)` | `replicaGate_conj_collectivePauliString`, `replicaGate_conj_mem_graphLocalStringSpan` | `ReplicaRationalGate`, `GraphLocalPauliCovariance` |
| `(13)` | `replicaGate_sandwich_mem_obstruction`, `siteConjEquiv_mem_obstruction` | `GraphLocalPauliCovariance`, `GraphLocalPauliConjugation` |
| `(15)`, `(16)` | **`graphLocalNonsinglet_le_shadow`** | `GraphLocalHallAssembly` |
| `(18)` | `siteConjString_conj_collectivePauliString`, `siteConjEquiv_commutator_singlet` | `AllReplicaSiteString`, `GraphLocalPauliDetector` |
| `(19)` | `inner_collectiveCommutator_eq_zero_of_sign_ne`, `exists_boolPauliConjugationSign_mul_eq_neg_one` | `PauliConjugationGrading`, `GraphLocalPauliDetector` |
| `(20)` | `graphLocalEdgeSum`, `graphLocalEdgeGenerator_mem_singlet_orthogonal` | `GraphLocalHallAssembly` |
| `(21)`, `(22)` | `graphLocalVisible`, `graphLocalDetector` | `GraphLocalHallAssembly` |
| `(23)` | `graphLocalDetector_visible_finrank`, `visibleQuotientDetector_finrank` | `GraphLocalHallAssembly`, `VisibleKernelRecoveryHallExpansion` |
| `(24)` | **`edgeImage_mem_of_sum_mem`**, `graphLocalDetector_ker_edge_mem` | `GraphLocalPauliDetector`, `GraphLocalHallAssembly` |
| `(25)`, `(27)` | `graphLocalRecovery`, `graphLocalRecovery_range_le` | `GraphLocalHallAssembly` |
| `(26)` | `graphLocalRecovery_injective`, `hermitianFamilyCasimir_eq_zero_iff` | `GraphLocalHallAssembly`, `HermitianFamilyCasimirSplit` |
| `(28)` | `inner_hermitianFamilyCasimir_self` | `HermitianFamilyCasimirSplit` |
| `(29)` | **`graphLocalReducedObstruction_finrank_le`**, `visibleKernelRecovery_finrank_of_disjoint` | `GraphLocalHallAssembly` |
| `(30)` | **`graphLocal_finrank_le_shadow_add_factorial`** | `GraphLocalHallSaturation` |

Supporting infrastructure added for this card:

- `VandermondeCoefficientMembership` -- `mem_of_forall_polynomial_value_mem` and its graded form:
  a module-valued polynomial whose values at enough distinct scalars lie in a submodule has all its
  coefficients there.  The Vandermonde matrix of the sample points is inverted explicitly.
- `ReplicaRationalGate` -- the replicated rational rotation
  `G_s = prod_l (1 + s i sigma_c^{(v,l)})`, its opposite-scale inverse `G_s G_{-s} = (1+s^2)^r`,
  the one-replica-at-a-time conjugation formula, the closed form of
  `G_s Q_p G_{-s}` inside the family span, and the expansion of `G_s X G_{-s}` as a polynomial in
  the scale whose linear coefficient is exactly `i [Q_{v,c}, X]`.
- `MatrixSandwichEquiv` -- two-sided multiplication by a scalar-inverse pair as a linear
  automorphism of the vectorised operator space, and its exact covariance with commutator actions.
- `SelfAdjointFamilyCommonKernel` -- for a self-adjoint family, the orthogonal complement of the
  simultaneous kernel is the span of the ranges; both are preserved by every span-covariant
  automorphism, so the kernel projector commutes with it.
- `CommutingInvolutionCharacterExtraction` -- sign-graded extraction: if distinct components carry
  distinct sign characters under operators preserving a subspace, membership of their sum forces
  membership of each.  One separating operator is averaged at a time; only invertibility of `2` is
  used.
- `HermitianFamilyCasimirSplit` -- the quadratic Casimir of a Hermitian family is self-adjoint with
  kernel the simultaneous kernel and range inside its complement, so any Casimir-invariant subspace
  splits along it.

## What the formal proof does differently

Five steps of the paper argument are replaced by strictly finite substitutes.

**Product-local `SU(2)` is replaced by rational rotations at finitely many scales.**  Equation
`(12)` is not obtained from a continuous group action.  The formal symmetry is the replicated
rational gate `G_s = prod_l (1 + s i sigma_c)`, invertible for every real `s` with
`G_s G_{-s} = (1+s^2)^r`.  Conjugation acts one replica at a time, so a collective string is sent
to an explicit combination of itself and the string with the letter multiplied in, which stays in
the family span because multiplying a letter into a local word leaves its support unchanged.  The
infinitesimal statement `A_p U_* subset U_*` is then recovered without any limit: the sandwich
`G_s X G_{-s}` is a polynomial in `s` of degree at most `2r` whose linear coefficient is
`i [Q_{v,c}, X]`, and Vandermonde inversion at `2r+2` integer scales extracts that coefficient.

**Haar averaging is replaced by kernel-range splitting.**  Equation `(14)` follows from invariance
of the obstruction under the weight-one Casimir alone: the Casimir is self-adjoint, its kernel is
the singlet sector, its range lies in the orthogonal complement, and an endomorphism whose kernel
meets its range trivially has kernel and range spanning.  No spectral projector is constructed.

**The all-replica local-Casimir Hall law is not used.**  Internal reproduction `(15)` is obtained
directly: the weight-one Casimir is injective on the nonsinglet layer, hence surjective onto it,
and every Casimir image is a two-step weight-one image, so the layer reproduces itself.

**The edge-Casimir singlet invariance of Lemma 6 is not needed.**  The assembly uses a form of the
visible-kernel recovery inequality in which the output independence is a hypothesis, and that
independence is proved directly from the Casimir quadratic form: an element of the visible output
that is also an edge-Casimir image of a singlet pairs to zero with its own preimage, so every edge
image of the preimage vanishes and the element is zero.

**The commutant correction is realised by completing the family.**  The exact commutant `N_r` is
taken to be the literal simultaneous kernel of the generators, as in `(5)`.  Adjoining its
orthogonal projector produces a family with trivial simultaneous kernel whose ordinary Hall
condition is equivalent to `(9)`, and the greatest obstruction of that completed family is the one
the assembly bounds.  For a connected graph the simultaneous kernel is identified with the
commutant of every collective string, which is what turns `(8)` into the stable-range form `(30)`.

## Exact surviving frontier

One-step rank saturation is closed.  Next theorem must be quantitative: prove a growing-replica
lower bound for the capacity or pseudodeterminant of the normalized local-Pauli family on the
collective-commutant quotient, strong enough to survive approximate tubes and the complete circuit
union.  Equivalently, identify a replica-uniform coercive invariant stronger than Hall rank but
weaker than a minimum spectral gap.  Rank saturation alone cannot supply that scale.

The sharpened candidate is a **scaled commutator quantum-expander law**.  Let
`eta_r(X)=sum_p A_p X A_p` on `N_r^perp`, and let `C_r` be a canonical positive symmetric operator
scaling satisfying `eta_r(C_r)=C_r^(-1)` when attained.  For
`B_p=C_r^(1/2) A_p C_r^(1/2)`, prove a lower bound on the second-singular-value gap of
`sum_p B_p tensor conjugate(B_p)` whose logarithmic loss is sublinear in the total replica order.
Failure must exhibit an explicit near-invariant traceless matrix after scaling.  A gap only for the
stacked vector map, the unscaled edge Casimir, or the refreshed local-unitary walk does not count.

## Log

- 2026-08-10 — abstract mixed-layer gluing conjecture falsified by a two-layer rotation example.
- 2026-08-10 — product-local symmetry reduction identified internal nonsinglet reproduction at the
  canonical greatest obstruction.
- 2026-08-10 — proved arbitrary-replica character-resolved visible detector and full edge-Casimir
  hidden-kernel recovery.
- 2026-08-10 — assembled exact one-step Hall saturation modulo the global collective commutant for
  every finite replica order; quantitative conditioning isolated as surviving frontier.

## 2026-08-10 quantitative-frontier correction

The scaled-commutator candidate above is not implied by this card's Hall and Casimir inputs.
`all-replica-incidence-normalized-local-word-leakage-law.md` gives an explicit Hermitian `3 x 3`
two-matrix family whose quadratic frame operator stays between `(1/2)I` and `4I`, and whose span
contains an invertible matrix, while its operator capacity is between `epsilon^2/2` and
`2 epsilon^2`.  Capacity therefore tends to zero at fixed Hall rank and fixed vector-frame
coercivity.  This is the required near-shrunk counterexample to the proposed inference.

The positive survivor moves from one step to controlled local-word depth.  Every full Pauli
commutator has a depth-at-most-`n` synthesis from physical weight-one and weight-two commutators
with total coefficient `ell^1` mass exactly one.  Full-Pauli Casimir normalization is bi-tight on
the collective-commutant quotient.  Consequently every dimension-losing incidence cut has
normalized local-word leakage at least

\[
 {2D^2\over D^2-1}(\dim U-\dim V)>2(\dim U-\dim V)
\]

at every finite replica order, with synthesis-sheet multiplicity retained.  This closes
conditioning for the all-to-all two-local **word family**, not the one-step tuple.  It still does
not control a full-span nonlinear circuit union.  The surviving Brown frontier is now explicitly
Bellman-compatible transfer before occupied-span projection, not another capacity estimate for the
one-step CP map.

## 2026-08-10 planar composition and static nontransfer

The Hall theorem does close one qualitative analytic consequence: with strictly positive
variances on the complete local family, Kargin's full-matrix-semicircle theorem makes the free
planar vacuum-compressed propagator decay to zero on the collective-commutant quotient at every
finite replica order.  That result does **not** transfer to a classical static Gaussian pencil.

Every realized collective Liouvillian `ad_(H_[r])` has a Hamiltonian-dependent centralizer larger
than the common permutation algebra.  For maximal projective `D`-level spectrum its dimension is
`sum_(|k|=r)(r!/prod_j k_j!)^2`; the static fixed-shell ensemble converges instead to the average
projection onto these moving kernels.  The exact proof, collision-floor trace, and nonzero
planar/static separation bound are in
`all-replica-static-centralizer-planar-separation-law.md`.  Thus the phrase “no cavity decay theorem”
in the hostile audit should be read as “no static-Hamiltonian cavity transfer or Brown decay.”
The free all-replica cavity theorem is now closed on paper; the static selector-aware problem is
not.
