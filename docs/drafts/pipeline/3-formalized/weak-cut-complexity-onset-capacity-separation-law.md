# Weak cuts separate static-local complexity onset from plateau capacity

- **ID:** `weak-cut-complexity-onset-capacity-separation-law`
- **Stage:** 3 -- formalized in Lean 4
- **Type:** theorem / Brown-onset obstruction / nearest-neighbour static-local dynamics
- **Parents:** `cubic-phase-seeded-static-local-full-scale-plateau-law.md`,
  `../3-formalized/weak-interaction-recurrence-singularity-law.md`,
  `../3-formalized/fast-forwardable-stratum-codimension-obstruction.md`
- **Status:** `[FORMALIZED] [FRONTIER ADVANCE] [NOVELTY UNVERIFIED]`
- **Date:** 2026-08-09

## Public sentence

An arbitrarily weak bond can leave a finite quantum system's eventual complexity capacity maximal
while postponing the first full-complexity epoch for an arbitrarily long time.  Plateau height and
onset time are therefore different physical data: the first is spectral capacity, while the second
also sees interaction conductance.

## Setup

Let

\[
 \mathcal H=\mathcal H_A\otimes\mathcal H_B,
 \qquad
 H=H_A\otimes I+I\otimes H_B+V,                                \tag{1}
\]

where `V` is the interaction crossing the cut.  Start from a product state
`chi=chi_A tensor chi_B`.  Circuit complexity is measured from a product reference using an
inverse-closed finite universal one- and two-qubit alphabet and pure-state trace distance.

For `k` qubits and `eta>0`, let `S_k(eta)` be a uniform state-synthesis cap: every `k`-qubit pure
state has an `eta`-approximation using at most `S_k(eta)` gates.  Standard recursive state
preparation followed by finite-alphabet compilation gives, at every fixed `eta`,

\[
 S_k(eta)\le 2^k\,\operatorname{poly}(k,\log(1/eta)).            \tag{2}
\]

Only finiteness of `S_k(eta)` is needed for the exact finite-size theorem; `(2)` gives its
large-system scale.

## Theorem A -- cut-conductance delay law

This theorem is the balanced-cut specialization of the already
`[LOCAL-RESEARCH] [LEAN-PROVED]` fast-forwardable-stratum Duhamel law. It is retained here as the
physical bridge to spatial conductance, not claimed as a new continuity mechanism.

For `eta_A,eta_B>=0` and `epsilon>eta_A+eta_B`, every time satisfying

\[
 |t|\,\|V\|_{\rm op}\le\epsilon-eta_A-eta_B                   \tag{3}
\]

obeys

\[
 \boxed{
 C_\epsilon(e^{-itH}\chi)
 \le S_{n_A}(eta_A)+S_{n_B}(eta_B).}                           \tag{4}
\]

For a balanced cut and fixed positive errors, the right side is

\[
 2^{n/2}\operatorname{poly}(n)=o(2^n/\log n).                 \tag{5}
\]

Consequently the first time at which complexity can exceed the split-system synthesis cap obeys

\[
 \boxed{
 T_{\rm full}(H,\epsilon)
 \ge {\epsilon-eta_A-eta_B\over\|V\|_{\rm op}}.}              \tag{6}
\]

### Proof

Put `H_0=H_A tensor I+I tensor H_B`.  Duhamel's formula and unitarity give

\[
 \|e^{-itH}-e^{-itH_0}\|_{\rm op}\le |t|\,\|V\|_{\rm op}.    \tag{7}
\]

The decoupled state factors exactly:

\[
 e^{-itH_0}\chi
 =(e^{-itH_A}\chi_A)\otimes(e^{-itH_B}\chi_B).                \tag{8}
\]

Prepare the two factors with errors `eta_A,eta_B` and concatenate their disjoint circuits.  Tensor
stability and the triangle inequality give total trace-distance error at most

`eta_A+eta_B+|t| ||V||_op`.  Equations `(3)--(4)` follow.  Equation `(2)` on a balanced cut proves
`(5)`, and `(6)` is the contrapositive of `(4)`.

No spectral gap, perturbation expansion, or long-time approximation is used.  The estimate is
uniform on the complete interval `(3)`.

## Lean progress -- Theorem A

`formal/GaloisForLFunctions/HTGeometry/WeakCutSynthesisCap.lean` (new, umbrella-wired,
axiom-clean).

| Card item | Declaration |
|---|---|
| `(7)` Duhamel: `‖e^{-itH} - e^{-itH_0}‖ <= |t| ‖V‖` | `dist_orbitState_le` (`FastForwardableStratumCodimension`) |
| **`(4)`**: while `|t| ‖V‖` stays inside the error budget, the coupled orbit inherits the split synthesis cap | `approxComplexity_le_of_decoupled` |
| the same with a larger error budget | `approxComplexity_le_of_decoupled_mono` |
| **`(6)`**: exceeding the cap forces `t > (eps - eta_A - eta_B)/‖V‖` | `lt_time_of_exceeds_cap` |

`(4)` is the transport lemma applied to the pair `(H, H_0)` over the window `[0,t]`, and `(6)` is
its contrapositive; both are unconditional in the abstract gate model, with no spectral gap and no
perturbation expansion.

### `(8)` is closed too

`formal/GaloisForLFunctions/HTGeometry/TensorConcatenation.lean` (new, umbrella-wired,
axiom-clean) supplies the product-alphabet layer the concatenation needs.

| Card item | Declaration |
|---|---|
| gates of the two halves acting on the pair, each on its own factor | `prodAct` |
| a word of left gates moves only the left factor, and dually | `wordAct_prodAct_inl`, `wordAct_prodAct_inr` |
| **the concatenated word moves both factors** | `wordAct_prodAct_append` |
| **`(8)`**: a product state is prepared by the two factor circuits, lengths adding | `approxComplexity_prodAct_le` |
| the product state vector and its norm `‖psi (x) phi‖ = ‖psi‖‖phi‖` | `tensorVec`, `norm_tensorVec` |
| one-sided differences of product states | `tensorVec_sub_left`, `tensorVec_sub_right` |
| **factor errors add**: `‖psi(x)phi - psi'(x)phi'‖ <= ‖psi-psi'‖ + ‖phi-phi'‖` for unit vectors | `norm_tensorVec_sub_le` |

So Theorem A is complete: `(4)` and `(6)` from `WeakCutSynthesisCap`, `(8)` from
`TensorConcatenation`, and `(7)` from the corpus Duhamel bound.  `(5)` is the arithmetic
`2^{n/2} poly(n) = o(2^n/log n)`.

### Theorem B is closed

| Card item | Declaration |
|---|---|
| unnormalized product phase vector, one independent uniform phase per factor index | `phaseVec` (`BipartitePhaseSeedCollision`) |
| the squared pairing is a character combination with pair frequencies | `sq_inner_phaseVec` |
| at most four terms share a frequency | `card_filter_prodPairFreq_le` |
| Parseval with bounded frequency multiplicity | `integral_box_normSq_trigLift_le_mul` |
| **`(9)` for one unit vector**: fourth moment `<= 4/D^2` | `integral_box_inner_prodPhaseSeed_fourth_le` |
| **`(9)`**: summed over an orthonormal family, `<= 4|iota|/D^2` | `integral_box_sum_inner_prodPhaseSeed_fourth_le` |
| integrability of the collision on the phase box | `integrableOn_box_sum_inner_prodPhaseSeed_fourth` (`BipartiteSeedSelection`) |
| **one seed at or below the mean** | `exists_prodPhaseSeed_collision_le` |
| **"at least one product seed has collision at most `4/D`"** | `exists_prodPhaseSeed_collision_le_four_div` |

The Lean route to `(9)` is the frequency-multiplicity Parseval bound rather than the card's
`(11)`--`(12)` pairing chain; it gives the same constant four, and the same conclusion.  The
"four-wise independence transfers every moment used" step is the cubic-phase parent's clause, not a
new obligation here.

## Theorem B -- product cubic-phase seeds retain full spectral capacity

Split the qubits into nonempty sets `A,B`, with dimensions `d_A,d_B` and `D=d_A d_B`.  Independently
sample the degree-at-most-three `Z/8Z` cubic-phase seeds `chi_(h_A)` and `chi_(h_B)` on the two
factors.  For every orthonormal basis `(e_j)_(j=1)^D` of the full, possibly entangled, bipartite
space,

\[
 \boxed{
 \mathbb E_{h_A,h_B}
 \sum_{j=1}^D
 |\langle e_j,\chi_{h_A}\otimes\chi_{h_B}\rangle|^4
 \le {4\over D}.}                                             \tag{9}
\]

Hence at least one exactly `O(n^3)`-preparable product cubic seed has spectral collision at most
`4/D` in that basis.

### Proof

It is enough to compute with independent Steinhaus coordinate phases; four-wise independence of
each cubic-phase family transfers every moment used below exactly.  Fix a unit vector
`e in H_A tensor H_B`.  For a phase state `a` on `A`, let

\[
 v_a=(\langle a|\otimes I)e,
 \qquad q(a)=\|v_a\|^2.                                       \tag{10}
\]

Phase pairing on `B` gives

\[
 \mathbb E_b|\langle e,a\otimes b\rangle|^4
 \le {2q(a)^2\over d_B^2}.                                    \tag{11}
\]

Writing `rho_A=Tr_B |e><e|`, a second phase pairing gives

\[
 \mathbb E_a q(a)^2
 ={(Tr\,rho_A)^2+Tr(rho_A^2)-\sum_x(rho_A)_{xx}^2\over d_A^2}
 \le {2\over d_A^2}.                                         \tag{12}
\]

Thus the fourth moment for one `e` is at most `4/D^2`.  Sum over the `D` basis vectors to obtain
`(9)`.  Averaging then supplies one seed pair below the mean.  Each factor has the exact cubic
controlled-phase preparation from the parent theorem, so their product costs `O(n^3)` gates.

## Theorem C -- arbitrary onset delay with a full later plateau

Fix constant resolution budgets

\[
 0<eta_A+eta_B<epsilon_-<epsilon_+<1                           \tag{13}
\]

and any prescribed finite delay `L>0`.  For every sufficiently large `n`, there exist

1. one unit-coefficient-shell, time-independent nearest-neighbour Pauli Hamiltonian `H_n`;
2. one product cubic-phase seed `chi_n` of exact complexity `O(n^3)`;

such that all of the following hold for the same fixed pair:

\[
\begin{array}{ll}
\text{delayed full onset:}&
 C_{\epsilon_-}(e^{-itH_n}\chi_n)
 \le 2^{n/2}\operatorname{poly}(n)\quad(0\le t\le L),\\[2mm]
\text{full later plateau:}&
 C_{\epsilon_-}(e^{-itH_n}\chi_n)
 \ge c\,2^n/\log M_n
 \quad\text{through one interval of length }\exp(c2^n),\\[2mm]
\text{later recurrence:}&
 e^{-itH_n}\chi_n\text{ later returns within any prescribed positive error of }\chi_n,\\[1mm]
\text{permanent non-Haar locality:}&
 e^{-itH_n}\text{ remains separated from Haar randomness by the fixed local two-query protocol}
 \text{ for every real }t.
\end{array}                                                    \tag{14}
\]

Here `c>0` depends only on the fixed errors and gate alphabet, not on `L`.

### Proof

Choose a balanced spatial cut, a decoupled path-local coefficient-shell point `H_0`, and a
positive-volume shell neighbourhood `U` on which

\[
 \|H-H_0\|_{\rm op}
 \le {\epsilon_- -eta_A-eta_B\over L}.                         \tag{15}
\]

The path-local simple-spectrum, cyclicity, and maximal-projective-rank loci are conull; cyclicity
may be imposed simultaneously for the finite set of all product cubic seeds.  For every
`H in U`, Theorem B says that at least one seed in this finite set has collision at most `4/D` in
the eigenbasis of `H`.  The corresponding finitely many collision-good subsets cover `U`.
Therefore one fixed seed has a positive-measure collision-good subset of `U`; choose `H_n` from
its intersection with the preceding conull locus, and call that seed `chi_n`.  Thus the seed is
fixed for the resulting evolution rather than resampled in time.  Theorem A and `(15)` prove the
first line of `(14)`.

The collision-to-capacity theorem on the completed phase torus gives a depth
`cD/log M_n` easy-circuit complement whose bad Haar-phase measure is `exp(-cD)`.  Maximal
projective rank makes the one fixed orbit equidistributed on that torus.  A speed mesh and the same
complete-union estimate select a continuous hard block of length `exp(cD)`; reducing `c` once
absorbs the mesh.  Projective recurrence gives the later return.  The already proved bounded-weight
Pauli two-query separator applies at every time.  These are exactly the remaining three lines of
`(14)`.

Since `L` was arbitrary while the plateau constants are independent of it, eventual plateau
capacity does not bound first onset.

## Theorem D -- the ordinary shell has an unavoidable polynomial delay tail

For the full one-site plus nearest-neighbour two-site Pauli coefficient shell, the coefficient
dimension is

\[
 m=3n+9(n-1)=12n-9.                                           \tag{16}
\]

Across any fixed edge, the genuinely coupling Pauli block has dimension `p=9`.  For a uniform shell
point, let `rho` be the Euclidean norm of those nine coefficients.  Then

\[
 \rho^2\sim\operatorname{Beta}\left({9\over2},{m-9\over2}\right),              \tag{17}
\]

and therefore, for `0<x<1`,

\[
 \boxed{
 \Pr\{\rho\le x\}
 ={B_{x^2}(9/2,(m-9)/2)\over B(9/2,(m-9)/2)}
 =\Theta_n(x^9)\quad(x\downarrow0).}                           \tag{18}
\]

Deleting this edge decouples the chain, while

\[
 \|V\|_{\rm op}\le\sum_{a,b=1}^3|J_{ab}|\le3\rho.           \tag{19}
\]

For every fixed product seed, Theorem A and `(18)--(19)` imply the lower failure floor

\[
 \boxed{
 \Pr\{T_{\rm full}>L\}
 \ge c_n L^{-9}}                                               \tag{20}
\]

for all sufficiently large `L`, with an explicit positive finite-size constant `c_n` determined
by `(18)` and the fixed error margin.  A quenched Brown theorem for this unconditioned shell can
therefore never have a uniformly smaller delay tail.  At Brown time `L=2^n/poly(n)`, the floor is
`exp(-Theta(n))`, not doubly exponentially small: the beta normalization in `(18)` contributes
only a polynomial factor in `n` when `p=9` is fixed.

### Proof

Orthogonal projection of a uniform sphere point onto a fixed `p`-dimensional coordinate subspace
has the beta law `(17)`.  Its distribution function is `(18)`.  Equation `(19)` is Cauchy--Schwarz
for the nine unitary Pauli words.  Substitute

\[
 x={\epsilon-eta_A-eta_B\over3L}
\]

in `(18)` and apply `(6)`.

## Theorem E -- the complete path bottleneck can be paid once

For edge `e`, write `rho_e` for its nine-coefficient Euclidean norm and `V_e` for its two-site
interaction.  Pauli orthogonality on the four-dimensional edge Hilbert space gives

\[
 \|V_e\|_{\rm HS}=2\rho_e,
 \qquad
 \boxed{\rho_e\le\|V_e\|_{\rm op}\le3\rho_e}.                 \tag{21}
\]

Define the contiguous-cut conductance

\[
 \mathfrak g_{\rm path}(H)=\min_{1\le e<n}\|V_e\|_{\rm op}.  \tag{22}
\]

If `F_(m,9)(x)` denotes the beta distribution function in `(18)`, then no independence between
different edges is required for

\[
 \boxed{
 F_{m,9}(x/3)
 \le \Pr\{\mathfrak g_{\rm path}(H)\le x\}
 \le(n-1)F_{m,9}(x).}                                         \tag{23}
\]

Thus the whole weak-cut sector has the same ninth-power small-`x` exponent, up to the explicit
linear edge union.  At inverse Brown scale `x=poly(n)/2^n`, its probability is
`exp(-Theta(n))`.  Conditioning on

\[
 \mathfrak g_{\rm path}(H)>x                                  \tag{24}
\]

excludes the norm-small single-edge mechanism of Theorem A from certifying a delay longer than a
constant multiple of `1/x`, while costing only the tail `(23)` once.  It does not exclude other
fast-forwarding or onset-delay mechanisms.

### Proof

The nine two-site Pauli words are Hilbert--Schmidt orthogonal with squared norm four, so
`||V_e||_HS=2rho_e`.  Since `V_e` has matrix rank at most four,
`||V_e||_op>=||V_e||_HS/2=rho_e`; the upper estimate is `(19)`.  If one fixed edge has
`rho_e<=x/3`, then `mathfrak g_path<=x`, proving the lower bound in `(23)`.  Conversely,
`mathfrak g_path<=x` forces `rho_e<=x` for at least one edge; the union bound proves the upper
bound.  Equation `(18)` supplies both endpoint probabilities.

## What this changes in the Brown frontier

The conjecture

> collision `O(1/D)` plus maximal projective rank forces Brown-time onset

is false.  Theorem C keeps both properties and every already proved late-time clause while making
the onset delay arbitrarily large.  Spectral capacity and physical clock speed are independent.

The missing invariant is not a minimum spectral gap.  Every valid onset theorem must include the
interaction cut profile

\[
 \mathfrak g(H)=\min_{A|B\ {\rm nontrivial}}\|V_{A|B}\|_{\rm op}             \tag{25}
\]

as one necessary clock, but this profile is not sufficient.  For seeds product across the
minimizing cut, Theorem A proves the universal necessary clock `1/mathfrak g(H)`.  Theorems D--E
fix the sharp small-cut exponent for one edge and for the complete contiguous-cut profile of the
ordinary path-local shell.

This does not prove that a lower bound on `mathfrak g(H)` is sufficient for Brown growth.  Typical
fixed-shell Hamiltonians may still possess circuit shortcuts unrelated to a weak spatial cut.
The later capacity-compatible fast-forwardable incubation law gives fully coupled diagonal
carriers with arbitrarily long delay, so the sharpened target is:

> name concrete shortcut-carrier tubes, pay both their codimension tails and the explicit
> `L^{-9}` cut-bad sector, then attack geometric-skeleton Bellman escape on the complement.

This is a research programme, not a sufficiency theorem or an inverse classification.

## Conjecturing and falsification ledger

### C0 -- full collision capacity fixes the first plateau time

`[FALSIFIED]`.  Theorem C preserves collision `O(1/D)`, maximal projective rank, full plateau
height, exponential-in-`D` duration, recurrence, and the locality separator while delaying onset
past arbitrary `L`.

### C1 -- fixed coefficient-shell norm removes weak-interaction delay

`[FALSIFIED]`.  The global shell norm remains one while a single nine-dimensional edge block tends
to zero.

### C2 -- weak cuts are negligible enough to demand superexponential quenched tails

`[FALSIFIED]`.  The exact beta law gives the `L^{-9}` floor.

### C3 -- condition on cut conductance and run Bellman escape

`[FALSIFIED]`.  The fully coupled diagonal carrier in
`capacity-compatible-fast-forwardable-incubation-law.md` has
`mathfrak g_path(H)=Omega(n^(-1/2))`, optimal collision, and generic maximal projective rank after
transverse perturbation, yet remains easy through any prescribed `L`.

## Hostile audit

1. This theorem is a no-go and frontier correction, not Brown growth.
2. The delayed family is fine-tuned through one weak edge; Theorem D states exactly how much shell
   probability that tuning costs.
3. The product seed in Theorem C may depend on `n` and the prescribed delay `L`.  It is fixed for
   the resulting evolution, but the argument does not provide one explicit seed with a
   high-probability theorem over the whole shell.
4. State-synthesis bound `(2)` is standard infrastructure and carries no novelty claim.
5. Duhamel delay and its codimension mechanism are internally prior. Candidate novelty is limited
   to the product-cubic capacity composition, its delayed-yet-late-full plateau/recurrence/locality
   conclusion, and exact nine-dimensional path-edge refinement. External priority remains
   unaudited.
6. The Lean formalization and axiom audit are complete; audit items 1--5 stand unchanged.

## Lean realization

The dependency order actually used:

1. bipartite decoupled exponential factorization and Duhamel trace-distance bound;
2. tensor preparation and approximate-complexity upper transfer `(4)`;
3. product phase-state fourth-moment bound `(9)`, then its finite eighth-root form;
4. an explicit two-sided sphere-tube estimate in place of the incomplete-beta identity;
5. Pauli Hilbert--Schmidt/operator-norm comparison and the path-edge union `(23)`;
6. the single-orbit plateau window, the path/chain shell identification, and the composition.

## Lean progress -- Theorem A, the budgeting layer

`formal/GaloisForLFunctions/HTGeometry/CircuitWordBudget.lean` (new, umbrella-wired, axiom-clean)
proves the two budget laws that carry `(4)` and `(6)`, on top of the corpus's existing
`HasCircuitWordApproximation` / `CircuitWordSeparated` and its Duhamel bound
`HTGeometry.selfAdjoint_unitaryEvolution_norm_sub_le`.

| Card item | Declaration |
|---|---|
| moving the endpoint by `δ` costs `δ` of tolerance and no gates -- the `\|t\|·‖V‖` term of `(4)` | `HasCircuitWordApproximation.transfer` |
| **concatenating two circuits adds lengths and tolerances** -- "prepare the two factors and concatenate their disjoint circuits", giving `S_{n_A}(η_A) + S_{n_B}(η_B)` | `HasCircuitWordApproximation.mul` |
| the separation form transfers with the radius reduced by exactly the displacement | `CircuitWordSeparated.transfer` |
| **`(6)`**: hence a synthesis cap is a lower bound on the first time the endpoint can exceed it | `not_hasCircuitWordApproximation_of_separated` |

Disjointness of the two registers is *not* needed as a hypothesis: the concatenation law asks only
that composition be non-expanding on each side, which holds for unitary conjugation and for channel
composition alike.  That is why the same lemma serves the Markovian reflection card.

### Theorems D and E are closed

`formal/GaloisForLFunctions/HTGeometry/SphereBlockTail.lean`,
`PauliEdgeBlockNorms.lean`, `PathShellEdgeTail.lean`, `PathShellDelayFloor.lean`,
`PathShellFixedSeed.lean` (all new, umbrella-wired, axiom-clean).

| Card item | Declaration |
|---|---|
| the unit shell of a split Euclidean space, and its block-small event | `blockSmall`, `blockSmallOf` |
| the cone over the block-small event sits inside a product of balls | `cone_blockSmall_subset` |
| and contains a product of an inner ball with an off-centre complement ball | `prod_subset_cone_blockSmall` |
| **the two-sided block tail**: shell mass between constant multiples of `x^{dim U}` | `toSphere_blockSmall_le`, `toSphere_blockSmall_ge` |
| in normalized (probability) form | `shellProb_blockSmall_le`, `shellProb_blockSmall_ge` |
| transport along any orthogonal splitting of any Euclidean space | `toSphere_blockSmallOf`, `exists_blockTail_bounds` |
| **`(16)`**: the coefficient dimension `12n-9` | `finrank_pathShell` |
| the nine-dimensional edge block of the path shell | `finrank_edgeBlock` |
| **`(18)` in `Theta(x^9)` form** (the card's alternative Lean route: an explicit two-sided sphere-tube estimate in place of the incomplete-beta identity) | `exists_edgeSmall_tail_bounds` |
| every Pauli string is a Hermitian involution of operator norm one | `l2_opNorm_finitePauliMatrix` |
| **`(19)`**: `‖V_e‖_op <= 3 rho_e` (and the general `sqrt(N)` Cauchy--Schwarz form) | `l2_opNorm_edgeInteraction_le`, `l2_opNorm_pauliCombination_le`, `norm_edgePart_le` |
| **`(21)` Hilbert--Schmidt half**: `‖V_e‖_HS^2 = 4 rho_e^2` | `hsNormSq_edgeInteraction` |
| the dimension bound `‖A‖_HS^2 <= dim ‖A‖_op^2` | `hsNormSq_le_card_mul_sq` |
| **`(21)` lower half**: `rho_e <= ‖V_e‖_op` | `le_l2_opNorm_edgeInteraction` |
| **`(22)`**: the contiguous-cut conductance profile | `pathConductance` |
| one weak edge forces weak conductance, and conversely | `edgeSmall_subset_conductanceSmall`, `conductanceSmall_subset_iUnion` |
| **`(23)`**: the whole weak-cut sector obeys the same ninth-power law, with the edge union bound and no independence | `exists_pathConductance_tail_bounds` |
| the path-local Hamiltonian `(1)` and its cut, both self-adjoint | `pathHamiltonian`, `pathHamiltonianCut`, `isSelfAdjoint_pathHamiltonian`, `isSelfAdjoint_pathHamiltonianCut` |
| deleting the edge changes the Hamiltonian by exactly its interaction | `pathHamiltonian_sub_cut` |
| **`(20)`**: the delay floor `Pr{T_full > L} >= c_n L^{-9}` | `exists_delay_floor` |
| the delay sector has positive shell measure at every finite delay | `pathShellProb_delayEvent_pos` |
| **Theorem C's selection step**: a finite seed family covering the delay sector has one member with a positive-measure part | `exists_pos_inter_of_cover`, `exists_fixed_seed_on_delay` |

Deviation from the card, recorded: `(17)`--`(18)` are formalized as the two-sided estimate
`c x^9 <= Pr{rho_e <= x} <= C x^9` with explicit positive constants, which is the second option in
the card's own Lean plan ("beta projection law **or** a sufficient explicit sphere-tube lower
bound").  The exact incomplete-beta identity behind `(17)` is not formalized; nothing in `(20)` or
`(23)` uses it, since both consume only the ninth-power two-sided bound.

## Lean progress -- Theorem C (2026-08-21)

Theorem C needs the plateau, the recurrence and the locality **at one fixed pair** `(H_n, chi_n)`,
not on shell average.  Four new modules supply the missing layers.

`formal/GaloisForLFunctions/HTGeometry/SingleOrbitPlateauWindow.lean`:

| Card item | Declaration |
|---|---|
| a closed capture target translated along a time grid, and its Haar volume | `shiftTarget`, `gridTarget`, `volume_shiftTarget`, `volume_gridTarget_le` |
| the metric parametrization of the easy times, and its mesh transfer | `metricEasySet`, `metricEasySet_subset_physicalCaptureSet`, `metricEasySet_mesh`, `dist_orbitVec_le` |
| the density of the times whose forward window meets the target | `badWindowSet`, `badWindowSet_eq_preimage`, `limsup_windowProb_badWindowSet_le` |
| a time density below one leaves times arbitrarily late outside the set | `windowProb_Ioc`, `exists_notMem_of_limsup_windowProb_lt_one` |
| **the single-orbit continuous plateau** | `exists_late_hardWindow` |

The route is the one-sided Kronecker--Weyl law
(`oneSided_closedTarget_limsup_le_volume`) applied to the union of the `N_W` mesh translates of the
closed capture target, whose Haar volume is `N_W` times
`measure_projectiveAmpCaptureTarget_le_two_rpow`.  The hypothesis `N_W · 2^{-r/2} < 1` is exactly the
card's `(21)` condition.

`formal/GaloisForLFunctions/HTGeometry/PathChainLabelIdentification.lean` and
`PathShellProjectiveGenericity.lean`:

| Card item | Declaration |
|---|---|
| a path label is a nearest-neighbour Pauli string, injectively | `pathWord`, `pathWord_isChainLabel`, `pathWord_ne_identity`, `pathWord_injective` |
| and conversely every one of them is a path label | `exists_pathWord_eq`, `pathLabelEquiv` |
| **the two shell parametrizations agree** | `reindex_pathHamiltonian` |
| maximal projectivity is a relabelling invariant | `MaximallyProjectiveEnergy.comp_equiv` |
| one witness makes maximal projectivity full measure | `volume_notMaximallyProjective_eq_zero` |
| **the degenerate path directions are null** | `pathShellProb_pathBadSphere_eq_zero` |
| the eigenbasis of the path-local Hamiltonian, and its genericity | `pathEigenBasis`, `isOrthoEigenBasis_pathEigenBasis`, `maximallyProjectiveEnergy_pathEigenValues` |
| selecting a nondegenerate direction inside a positive-measure sector | `exists_mem_notMem_pathBadSphere` |

`formal/GaloisForLFunctions/HTGeometry/BipartiteEighthRootTransfer.lean`:

| Card item | Declaration |
|---|---|
| a character of a sum index at a pair of eighth-root phases factorizes | `charLift_eighthPhase_sumElim` |
| **two independent low-support-uniform ensembles give one on the sum index** | `eighthPhaseUniform_sumElim`, `eighthPhaseUniform_prodPolyEval` |
| **the bipartite collision is a trigonometric polynomial** on eight coordinates with entries at most four | `prodQuarticSum_eq_trigLift`, `card_freqSupport_prodCollFreq_le`, `abs_prodPairFreq_le`, `exists_prodCollFreq_ne_zero_mod_eight` |
| the moment transfer to the finite product cubic ensemble | `average_prodQuarticSum_polyEval_eq_integral`, `average_prodCollision_polyEval_eq_integral` |
| **`(9)` for a finite family of product cubic seeds** | `exists_prodPolyEval_collision_le_four_div` |

The finite family matters: Theorem C's covering argument needs *finitely many* seeds serving the
whole delay sector, which the continuous product phase seed of Theorem B does not provide.  Only the
**first** collision moment is transferred, because `(9)` is a mean bound.

`formal/GaloisForLFunctions/HTGeometry/WeakCutDelayedPlateau.lean`:

| Card item | Declaration |
|---|---|
| the bipartite reading of the register | `regSplit`, `card_regSplit`, `bipartiteFamily`, `registerSeed`, `finiteComplexInner_bipartiteFamily` |
| the product cubic seed on the register, and its unit norm | `cubicProductSeed`, `finiteComplexInner_cubicProductSeed` |
| **`(23)`**: the orbit speed of the path shell is `sqrt(12(n+2)-9)` | `norm_pathHamiltonian_le_sqrt` |
| the finite product cubic family serves every shell direction | `cubicGood`, `subset_iUnion_cubicGood` |
| one seed and one nondegenerate weak-cut direction | `exists_weakCut_fixed_pair` |
| **Theorem C `(14)`**: delayed onset, full later plateau and later recurrence at the same fixed pair | `exists_weakCut_delayed_plateau` |

The delay sector used is the weak-edge event `edgeSmall e ((eps-eta)/(3L))`, which is
seed-independent and has positive shell measure by `exists_edgeSmall_tail_bounds`; the per-seed
inclusion into `delayEvent` is `edgeSmall_subset_delayEvent`.  The last line of `(14)`, permanent
non-Haar locality, is the seed-independent corpus separator
`haarBenchmark_lt_literalTwoQueryScore_of_trace_eq_zero`; `(19)`--`(22)` are the arithmetic of
`plateauGridCount` at mesh `(eps_+ - eps_-)/sqrt(12(n+2)-9)`.

## Status of the card

| Card statement | Declaration |
|---|---|
| **Theorem A `(4)`, `(6)`** -- the cut-conductance delay law | `approxComplexity_le_of_decoupled`, `lt_time_of_exceeds_cap` |
| **`(8)`** -- decoupled evolution factorizes | `unitaryEvolution_kroneckerSum_mulVec_tensorVec` |
| **Theorem B `(9)`--`(12)`** -- product seeds retain full spectral capacity | `integral_box_sum_inner_prodPhaseSeed_fourth_le`, `exists_prodPhaseSeed_collision_le_four_div`, and on the finite cubic family `exists_prodPolyEval_collision_le_four_div` |
| **Theorem C `(14)`** -- arbitrary onset delay with a full later plateau | `exists_weakCut_delayed_plateau` |
| **`(15)`**, the weak-cut neighbourhood | `edgeSmall`, `edgeSmall_subset_delayEvent` |
| permanent non-Haar locality | `haarBenchmark_lt_literalTwoQueryScore_of_trace_eq_zero` |
| **Theorem D `(16)`--`(20)`** -- the unavoidable polynomial delay tail | `finrank_pathShell`, `exists_edgeSmall_tail_bounds`, `exists_delay_floor` |
| **Theorem E `(21)`--`(23)`** -- the complete path bottleneck | `exists_pathConductance_tail_bounds`, `exists_pos_inter_of_cover`, `exists_fixed_seed_on_delay` |

The gate model (`Γ`, `act`, `chi`, the synthesis cap `S` and its certificate) is the card's own
Setup `(2)`, carried as data exactly as in Theorems A, D and E; every displayed inequality is
unconditional and axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only).  The card is fully
formalized.

## Lean progress -- the state-synthesis cap `(2)` is a theorem

The gate model is no longer a hypothesis anywhere on this card.  Two-level (Givens) synthesis gives,
for every finite register and every tolerance, one explicit finite alphabet and one reference state
whose words of length at most twice the dimension reach *every* pure state of the register:
`K - 1` amplitude rotations in the real coordinate planes `(i, i+1)` bring the first basis vector to
the modulus profile, `K` diagonal phase gates install the arguments, and discretizing every angle on
the `m`-point grid `2\pi j/m` makes the alphabet finite at a cost of `O(\sqrt K/m)` per gate.  This
is exactly `(2)` with `S_k(\eta) = 2\cdot 2^k`.

`formal/GaloisForLFunctions/HTGeometry/TwoLevelStateSynthesis.lean`,
`formal/GaloisForLFunctions/HTGeometry/SynthesisWordApproximation.lean`,
`formal/GaloisForLFunctions/HTGeometry/UniversalSynthesisCertificate.lean`,
`formal/GaloisForLFunctions/HTGeometry/WeakCutUnconditionalPlateau.lean`
(all new, umbrella-wired, axiom-clean):

| Card item | Declaration |
|---|---|
| the two-level rotation and phase gates, and that they preserve the `\ell^2` norm | `rotAct`, `phaseAct`, `sum_normSq_rotAct`, `sum_normSq_phaseAct` |
| the amplitude staircase and its exact rotation angles | `absState`, `rotAngle`, `rotStep`, `absState_zero`, `absState_last` |
| the phase staircase | `phState`, `phaseStep`, `phState_of_ge` |
| each gate is `\ell^2`-Lipschitz in its angle | `norm_rotAct_sub_le`, `norm_phaseAct_sub_le`, `dist_le_of_pointwise` |
| every gate is an isometry, hence so is every word | `dist_synthAct_eq`, `dist_wordAct_eq` |
| the two passes | `exists_absWord`, `exists_phWord` |
| **`(2)`**: a uniform synthesis cap of `2\cdot\dim` at every tolerance | `exists_synthesis_word`, `exists_synthesis_alphabet` |
| the cap read on an arbitrary finite register | `transportAct`, `exists_universal_synthesis_certificate` |
| **the certificate along every self-adjoint orbit**, uniformly in Hamiltonian, seed and time | `exists_orbit_synthesis_certificate` |
| the delayed plateau with the gate model supplied | `exists_weakCut_delayed_plateau_synthesized` |
