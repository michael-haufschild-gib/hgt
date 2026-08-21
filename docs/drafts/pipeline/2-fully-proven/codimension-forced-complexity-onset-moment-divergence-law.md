# Shortcut codimension forces divergent complexity-onset moments

- **ID:** `codimension-forced-complexity-onset-moment-divergence-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** theorem / static-local complexity onset / heavy-tail obstruction
- **Parents:** `weak-cut-complexity-onset-capacity-separation-law.md`,
  `capacity-compatible-fast-forwardable-incubation-law.md`,
  `onset-recurrence-dimension-independence-law.md`
- **Status:** `[PAPER-PROVED] [FRONTIER ADVANCE] [NOVELTY UNVERIFIED] [LEAN DEFERRED]`
- **Date:** 2026-08-09

## Public sentence

Even after retaining only local quantum systems that later attain near-maximal complexity and
maximal recurrence dimension, rare Hamiltonians near a shortcut carrier make sufficiently high
moments of the first-complexity time infinite.  Every moment whose order reaches the carrier's
transverse codimension must diverge.

The last sentence is one-sided: other shortcut carriers may force lower moments to diverge.  No
claim is made that one carrier determines the complete onset distribution.

## 1. Fixed-seed codimension law

Let \(X=S^{m-1}\) be a unit coefficient shell with normalized surface measure \(\sigma\), and let

\[
 H:\mathbb R^m\longrightarrow\operatorname{Herm}(\mathcal H_D)
 \tag{1}
\]

be real-linear with

\[
 \|H(x)-H(y)\|_{\rm op}\le L_H\|x-y\|_2.                    \tag{2}
\]

Let \(F\le\mathbb R^m\) have dimension \(f\), put \(d=m-f\), and let
\(P\subset F\cap X\) be a positive-measure compact patch.  Fix one seed \(\chi\), errors

\[
 0\le\eta<\epsilon_-<\epsilon_+<1,                            \tag{3}
\]

and integers \(B<s_D\).  Suppose the following properties have already been certified.

1. For every \(y\in P\) and every real \(t\),

   \[
    C_\eta(e^{-itH(y)}\chi)\le B.                             \tag{4}
   \]
2. There is \(r_*>0\) such that every \(x\in\mathcal N_{r_*}(P)\) has the collision bound needed
   by the completed-phase capacity theorem for the same seed.
3. A conull set \(G\subset X\) has simple spectrum, maximal projective rational rank, cyclicity of
   \(\chi\), the sharp metric recurrence property, and the permanent local non-Haar separator.
   On \(G\cap\mathcal N_{r_*}(P)\), the completed-phase theorem gives a later interval on which
   \(C_{\epsilon_+}>s_D\), followed by projective recurrence.

These are finite certificates, not probabilistic assumptions added to the conclusion.  In the two
ordinary local-Hamiltonian instantiations below, all three are supplied by the parent theorems.

Define the full-scale first-onset time

\[
 \tau(H,\chi)
 =\inf\{t\ge0:C_{\epsilon_-}(e^{-itH}\chi)>s_D\}.             \tag{5}
\]

It is finite on the completed set in item 3 because
\(C_{\epsilon_-}\ge C_{\epsilon_+}>s_D\) during the later plateau.  With a finite gate alphabet,
the set of states of complexity at most \(s_D\) is a finite union of closed error balls, so the
first-entry variable in `(5)` is measurable.

### Theorem A -- one fixed seed has a codimension tail at every large delay

There are constants \(A_P,L_P>0\) such that the same fixed seed \(\chi\) obeys

\[
 \boxed{
 \sigma\{H\in G:\tau(H,\chi)>L\}\ge A_PL^{-d}
 \qquad(L\ge L_P).}                                          \tag{6}
\]

Consequently, if \(\Gamma=G\cap\mathcal N_{r_*}(P)\), then

\[
 \boxed{
 \mathbb E_\sigma[\tau(H,\chi)^p\mid\Gamma]=\infty
 \qquad\text{for every real }p\ge d.}                        \tag{7}
\]

### Proof

Put \(a=\epsilon_- -\eta>0\) and

\[
 r_L=\min\left\{{r_*\over2},r_P,{a\over4L_HL}\right\},     \tag{8}
\]

where \(r_P\) is a sufficiently small fixed tube radius.  If
\(x\in\mathcal N_{r_L}(P)\), choose \(y\in P\) with
\(\|x-y\|_2\le2r_L\).  For every \(0\le t\le2L\), Duhamel's formula gives

\[
 \|e^{-itH(x)}-e^{-itH(y)}\|_{\rm op}
 \le2LL_H(2r_L)\le a.                                       \tag{9}
\]

The carrier circuit in `(4)` therefore proves
\(C_{\epsilon_-}(e^{-itH(x)}\chi)\le B<s_D\) throughout
\([0,2L]\).  Thus \(\tau(H(x),\chi)>L\).  Removing \(X\setminus G\) costs zero measure.

The shell tube law gives

\[
 \sigma(\mathcal N_r(P))\ge a_Pr^d\qquad(0<r\le r_P).       \tag{10}
\]

For all sufficiently large \(L\), the final term in `(8)` is the minimum.  Equations `(8)--(10)`
give `(6)`.

Define the nonnegative random variable \(Y\) to equal \(\tau(H,\chi)\) on \(\Gamma\) and \(0\)
on its complement.  This avoids the undefined product \(0\cdot\infty\) on permanently easy
systems.  Layer cake gives

\[
 \mathbb E[Y^p]
 =p\int_0^\infty L^{p-1}\sigma\{Y>L\}\,dL.                 \tag{11}
\]

The integrand is bounded below for large \(L\) by
\(pA_PL^{p-d-1}\), whose integral diverges exactly when \(p\ge d\).  Since
\(\sigma(\Gamma)>0\), division by \(\sigma(\Gamma)\) proves `(7)`.

Equation `(7)` is a forced divergence threshold, not a finiteness theorem for \(p<d\).

## 2. Ordinary path-local weak-cut law

Put \(D=2^n\) and use the full one-site plus nearest-neighbour two-site Pauli shell on an open
qubit path.  Its coefficient dimension is

\[
 m=3n+9(n-1)=12n-9.                                         \tag{12}
\]

Fix a balanced edge \(e\).  Setting its nine genuinely coupling Pauli coefficients to zero gives
a decoupled carrier \(F_e\) of codimension

\[
 \boxed{d_{\rm cut}=9.}                                      \tag{13}
\]

Let \(\mathcal Q_A\otimes\mathcal Q_B\) be the finite family of product cubic-phase seeds from
the weak-cut parent.  For every eigenbasis \(u\), that theorem proves

\[
 \mathbb E_{\chi\in\mathcal Q_A\otimes\mathcal Q_B}
 \sum_{j=1}^D|\langle u_j,\chi\rangle|^4\le {4\over D}.      \tag{14}
\]

Choose constants \(K_1>K_0>4\).  On any positive-measure simple-spectrum patch
\(U\subset F_e\cap X\), Markov and Fubini select one fixed product cubic seed \(\chi_n^{\rm cut}\)
such that the carrier subset

\[
 U_0=\left\{y\in U:
 \sum_j|\langle u_j(y),\chi_n^{\rm cut}\rangle|^4
 \le {K_0\over D}\right\}                                  \tag{15}
\]

has relative measure at least \(1-4/K_0>0\).  Inner regularity supplies a positive-measure compact
patch \(P_n^{\rm cut}\subset U_0\).  The spectral collision is continuous on the simple-spectrum
locus.  Compactness and the strict slack \(K_1>K_0\) therefore give \(r_{*,n}>0\) such that the
same fixed seed has collision at most \(K_1/D\) throughout
\(\mathcal N_{r_{*,n}}(P_n^{\rm cut})\).

For every carrier Hamiltonian, evolution factorizes across the cut.  Uniform state synthesis on
the two halves gives

\[
 C_\eta(e^{-itH(y)}\chi_n^{\rm cut})
 \le B_n^{\rm split}
 =S_{\lfloor n/2\rfloor}(\eta_A)+S_{\lceil n/2\rceil}(\eta_B)
 =2^{n/2}\operatorname{poly}(n).                              \tag{16}
\]

Choose \(s_n=c_{K_1}D/\log M_n\) below the completed-phase plateau height.  For all sufficiently
large \(n\), \(B_n^{\rm split}<s_n\).  Let
\(\Gamma_n^{\rm cut}=G_n\cap\mathcal N_{r_{*,n}}(P_n^{\rm cut})\), where \(G_n\) is the
simultaneous conull completion set.  Thus all inputs of Theorem A are now proved for this fixed
seed and patch.

### Theorem B -- ninth and higher onset moments diverge

For every sufficiently large \(n\), there are one fixed exactly \(O(n^3)\)-preparable product
cubic seed \(\chi_n^{\rm cut}\), a completed event \(\Gamma_n^{\rm cut}\) of positive shell
measure, and constants \(A_n,L_n>0\) such that

\[
 \boxed{
 \sigma\{H\in\Gamma_n^{\rm cut}:
 \tau(H,\chi_n^{\rm cut})>L\}\ge A_nL^{-9}
 \qquad(L\ge L_n),}                                         \tag{17}
\]

and

\[
 \boxed{
 \mathbb E[\tau(H,\chi_n^{\rm cut})^p
 \mid\Gamma_n^{\rm cut}]=\infty
 \qquad(p\ge9).}                                             \tag{18}
\]

Every Hamiltonian counted in `(17)` later has an
\(\Omega(D/\log M_n)\) plateau lasting \(\exp(\Omega(D))\), later recurrence to the easy seed,
maximal continuous fidelity-return exponent \((D-2)/2\), and permanent separation from Haar
randomness by the fixed local two-query protocol.

The seed in `(17)` is independent of \(L\).  This is the essential strengthening over the parent
arbitrary-delay theorem, whose Fubini selection was performed separately at each delay and hence
did not define one onset random variable with the asserted tail.

## 3. Fully coupled shortcut law

The ninth-moment obstruction above comes from a vanishing spatial bond.  It is not the complete
story.  Let

\[
 F_{\rm diag}
 =\operatorname{span}\{Z_i:1\le i\le n\}
  +\operatorname{span}\{Z_iZ_{i+1}:1\le i<n\}.                \tag{19}
\]

Its dimension is \(2n-1\), so its codimension in the ordinary shell is

\[
 \boxed{d_{\rm diag}=10n-8.}                                 \tag{20}
\]

Choose a compact positive-measure patch \(P_n^{\rm diag}\subset F_{\rm diag}\cap X\) on which
all \(Z_iZ_{i+1}\) coefficients have magnitude at least \(b_0/\sqrt n\) and all computational-basis
energies are distinct.  Such a patch exists because degeneracies form a finite union of proper
hyperplanes, while the strong-edge condition is open.  Compactness gives a uniform eigenvalue gap
\(\gamma_n>0\).

Use the single explicit seed

\[
 \chi_n^{+}=|+\rangle^{\otimes n}.                             \tag{21}
\]

On the carrier its spectral weights are exactly \(1/D\), its collision is \(1/D\), and commuting
\(Z\) and \(ZZ\) rotations give a uniform polynomial compiler.  If
\(\|H-H_0\|_{\rm op}\le c\gamma_n/\sqrt D\), the rank-one Davis--Kahan theorem labels the
eigenvectors so that their distance from the computational basis is at most \(1/(2\sqrt D)\).
Hence every seed overlap lies between \(1/(2\sqrt D)\) and \(3/(2\sqrt D)\), so the seed is cyclic
and

\[
 \sum_j|\langle e_j(H),\chi_n^+\rangle|^4
 \le {81\over16D}.                                           \tag{22}
\]

Equation `(2)` therefore supplies a fixed robust radius \(r_{*,n}>0\).  Let
\(\Gamma_n^{\rm diag}=G_n\cap\mathcal N_{r_{*,n}}(P_n^{\rm diag})\).  Completed phase,
metric recurrence, and local-separator parents apply on the conull factor \(G_n\) of this event.

### Theorem C -- the moment obstruction survives strong coupling on every edge

For every sufficiently large \(n\), there are a completed positive-measure event
\(\Gamma_n^{\rm diag}\) and constants \(A'_n,L'_n>0\) such that the explicit seed `(21)` obeys

\[
 \boxed{
 \sigma\{H\in\Gamma_n^{\rm diag}:
 \tau(H,\chi_n^+)>L\}
 \ge A'_nL^{-(10n-8)}
 \qquad(L\ge L'_n),}                                        \tag{23}
\]

\[
 \boxed{
 \mathbb E[\tau(H,\chi_n^+)^p
 \mid\Gamma_n^{\rm diag}]=\infty
 \qquad(p\ge10n-8).}                                        \tag{24}
\]

Every Hamiltonian counted in `(23)` has

\[
 \min_{1\le i<n}\|V_i(H)\|_{\rm op}\ge {b_0\over2\sqrt n}, \tag{25}
\]

and nevertheless later has the same full plateau, maximal recurrence exponent, low-complexity
return, and permanent non-Haar locality as in Theorem B.

### Proof

The carrier compiler, `(22)`, and the conull completion verify Theorem A with
\(d=10n-8\).  Shrink \(r_{*,n}\) once so that perturbations preserve `(25)`.  Equations
`(23)--(24)` are then `(6)--(7)`.  No random seed or delay-dependent seed selection remains.

## 4. Conjecture--failure--survivor ledger

### C0 -- carrier codimension is the exact onset-tail exponent

`[FALSIFIED AS STATED]`.  A tube gives a lower tail, not an upper tail.  Other weak cuts,
fast-forwardable strata, eigenstate boxes, or unknown shortcut mechanisms can dominate the full
distribution.

### C1 -- the parent arbitrary-delay theorem already implies moment divergence

`[FALSIFIED]`.  Its selected seed may depend on \(L\).  A family of inequalities for different
random variables cannot be integrated by layer cake as the tail of one random variable.

### C2 -- a fixed seed cannot remain capacity-good arbitrarily close to a shortcut carrier

`[FALSIFIED]`.  On the weak-cut carrier, finite-seed Fubini followed by compactification and
collision continuity produces one robust seed patch.  On the diagonal carrier, the explicit flat
seed plus a uniform spectral gap gives quantitative robustness by Davis--Kahan.

### Positive survivor

Each robust capacity-compatible shortcut patch forces divergence of every onset moment at or
above its codimension for one fixed physical seed.  This is a property of the actual first-onset
random variable, not merely a sequence of delayed examples.

## 5. What this changes in the Brown frontier

1. Ensemble means of sufficiently high powers of onset are not legitimate concentration proxies,
   even after conditioning on eventual full complexity and maximal recurrence.
2. Weak-cut removal is not cosmetic: it removes a dimension-independent ninth-moment divergence.
3. Conductance conditioning still leaves the fully coupled divergence `(24)`.  A Brown upper-tail
   theorem must explicitly pay both sectors before proving finite-scale undistortion on their
   complement.
4. The result does not prove typical linear growth, a median onset bound, or a matching upper tail.
   The exact open core remains quenched finite-scale undistortion on the geometric Brown skeleton.

The appropriate robust statistics for the unresolved upper theorem are therefore quantiles or
truncated moments after named shortcut excision, not unrestricted high moments.

## 6. External novelty boundary

- Brown--Susskind predicts the growth--plateau--recurrence history but does not derive a
  shortcut-codimension law for onset moments.
- Haferkamp et al. prove linear growth for random circuits with freshly sampled gates, not a
  heavy-tail theorem for one static local Hamiltonian ensemble.
- Haque--Jafari--Underwood derive an infinitesimal-time upper growth law in continuous complexity
  geometry.  They do not study finite-alphabet state first passage, quenched onset tails, or
  eventual full-complexity conditioning.
- Kotowski et al. prove saturation and recurrence for random local dynamics with continuing
  randomness and identify purely time-independent local Hamiltonians as an open target.
- Atia--Aharonov and Gu--Somma--Sahinoglu establish fast-forwardable classes, but do not join their
  transverse geometry to divergent first-complexity moments inside an eventually full-complexity
  ensemble.

No located primary source states `(17)--(18)` or `(23)--(25)`.  Search absence is not priority
evidence; status remains `[NOVELTY UNVERIFIED]` pending expert review.

Primary sources:

- A. R. Brown and L. Susskind, *The second law of quantum complexity*,
  [arXiv:1701.01107](https://arxiv.org/abs/1701.01107).
- J. Haferkamp et al., *Linear growth of quantum circuit complexity*,
  [Nature Physics 18 (2022)](https://www.nature.com/articles/s41567-022-01539-6).
- S. S. Haque, G. Jafari and B. Underwood, *Universal Early-Time Growth in Quantum Circuit
  Complexity*, [JHEP 10 (2024)](https://arxiv.org/abs/2406.12990).
- M. Kotowski et al., *Saturation and recurrence of quantum complexity in random local quantum
  dynamics*, [Physical Review X 14 (2024)](https://doi.org/10.1103/PhysRevX.14.041068).
- Y. Atia and D. Aharonov, *Fast-forwarding of Hamiltonians and exponentially precise
  measurements*, [arXiv:1610.09619](https://arxiv.org/abs/1610.09619).
- S. Gu, R. D. Somma and B. Sahinoglu, *Fast-forwarding quantum evolution*,
  [arXiv:2105.07304](https://arxiv.org/abs/2105.07304).

## 7. Hostile audit

1. The tail bounds are lower bounds.  They do not identify the full distribution or prove
   finiteness below the stated moment orders.
2. The conditioning events retain exactly the systems with certified later capacity.  Without
   this restriction, positive-measure permanently easy sectors would make onset infinite for a
   trivial reason.
3. The weak-cut seed is existential but fixed once per \(n\), has an exact polynomial circuit, and
   is independent of \(L\).  The fully coupled seed is explicit.
4. Constants such as \(r_{*,n}\), \(\gamma_n\), and \(A_n\) are finite-size and may be extremely
   small.  Moment divergence depends only on arbitrarily large \(L\), so this does not invalidate
   `(18)` or `(24)`; it does prevent a claimed uniform large-\(n\) crossover scale.
5. Maximal projective rank and the recurrence exponent are exact generic properties, not a claim
   of conventional many-body chaos.
6. Layer cake is elementary.  Candidate novelty lies in producing one robust fixed-seed
   delayed-yet-later-full event to which it applies, and in the ordinary weak-cut and fully coupled
   instantiations—not in the integration identity.
7. This theorem narrows and regularizes the Brown frontier.  It does not close the missing quenched
   upper escape bound or linear ramp.
8. No final-paper claim is authorized before Lean formalization and axiom audit.

## 8. Lean realization after corpus refactor

Reuse the existing fast-forwardable-stratum tube theorem, finite product-cubic collision theorem,
completed collision-to-capacity theorem, generic path-local spectral modules, metric-recurrence
theorem, and local separator.  New formal content is limited to:

1. fixed-seed Fubini selection on one carrier patch;
2. compact collision robustness on a simple-spectrum neighbourhood;
3. the first-onset measurable event and layer-cake divergence lemma;
4. the codimension-nine and codimension-\(10n-8\) conjunctions.

No Lean source or process was touched during the active corpus refactor.

## Lean progress -- Theorem B, `(17)` implies `(18)`

`formal/GaloisForLFunctions/HTGeometry/PowerTailMomentDivergence.lean` (new, umbrella-wired,
axiom-clean).

| Card item | Declaration |
|---|---|
| **the moment floor**: a tail `μ{τ > L} ≥ A L^{-q}` gives `∫ τ^p ≥ A L^{p-q}`, at every `L` | `moment_floor` |
| **an unbounded family of lower bounds forces an infinite integral** | `lintegral_eq_top_of_unbounded_real` |

Composing them is `(17) ⟹ (18)` for every `p > 9`: the tail `A L^{-9}` of `(17)` gives
`∫ τ^p ≥ A L^{p-9}` for every `L ≥ L_n`, that family is unbounded when `p > 9`, and a single
quantity dominating an unbounded family is infinite.  The estimate is pointwise in `L`, so no limit
theorem enters beyond the divergence of `L ↦ L^{p-9}`.

### The boundary exponent is closed too

| Card item | Declaration |
|---|---|
| the reciprocal is not integrable at infinity | `lintegral_Ioi_rpow_neg_one_eq_top` |
| **`(18)` at the boundary `p = 9`** | `lintegral_rpow_eq_top_of_boundary_tail` |

Chebyshev alone gives only `∫ τ^9 ≥ A` uniformly in `L`, which is not divergence.  The boundary is
reached through the layer-cake formula `lintegral_rpow_eq_lintegral_meas_lt_mul`: the integrand
becomes `μ{τ > t}·t^8 ≥ A t^{-9}·t^8 = A t^{-1}`, whose integral over `(L_n, ∞)` is infinite.  So
`(18)` now holds for the card's full range `p ≥ 9` -- strictly above by `moment_floor`, at the
boundary by `lintegral_rpow_eq_top_of_boundary_tail`.

## Lean progress -- Theorem A's machine

Theorem A is the same abstract machine as the sibling card
`capacity-compatible-fast-forwardable-incubation-law`, and every step of it is now Lean-proved:

| Card item | Declaration | Module |
|---|---|---|
| `(9)`, Duhamel transport of the carrier certificate across `[0,2L]` | `approxComplexity_orbitState_le_of_window` | `HTGeometry/IncubationTubeTransport` |
| the same, from membership in the spherical tube around the patch | `approxComplexity_le_of_mem_patchThickening` | `HTGeometry/CapacityIncubationLaw` |
| "removing `X \ G` costs zero measure" | `measureReal_inter_conull` | same |
| **the shell tube law** `sigma(N_r(P)) >= a_P r^d` | `toSphere_patchThickening_ge` | `HTGeometry/SphericalPatchTube` |
| the cone comparison behind it (normalization is two-Lipschitz; the carrier annulus times a transverse ball embeds in the cone) | `norm_normalize_sub_normalize_le`, `patchTube_subset_cone`, `volume_patchTube` | same |
| **`(6)`**, the codimension tail `A_P L^{-d}` at radius `r_L = c/L` | `incubation_tail_lower` | `HTGeometry/CapacityIncubationLaw` |
| finite Fubini seed selection, if the seed is chosen from a family | `exists_seed_measureReal_ge` | same |

So `(6)` and hence `(17)` are formal as an abstract machine: what a concrete instance still needs is
the *data* -- the carrier compiler certificate `(4)`, the patch `P_n^{cut}`, and the conull
completion set `G_n` -- which are inputs from the parent cards rather than steps of this proof.

## Lean progress -- the weak-cut instance of `(17)` and `(18)`

Section 2's instance is now formal end to end, on the concrete path-local Pauli shell, without the
abstract carrier/patch interface: the ninth-power tail is produced directly from the
codimension-nine edge block.

| Card item | Declaration | Module |
|---|---|---|
| **`(12)`**: the coefficient dimension `12n-9` of the path-local shell | `finrank_pathShell` | `HTGeometry/PathShellEdgeTail` |
| **`(13)`**: the nine coupling coordinates of one edge, as a coordinate block | `IsEdgeLabel`, `edgeLabelEquiv`, `finrank_edgeBlock` | same |
| the two-sided shell law of one edge block, `Theta(x^9)` | `exists_edgeSmall_tail_bounds` | same |
| the path-local Hamiltonian and its cut, both self-adjoint | `pathHamiltonian`, `pathHamiltonianCut`, `isSelfAdjoint_pathHamiltonian` | `HTGeometry/PathShellDelayFloor` |
| deleting the edge changes the Hamiltonian by exactly its interaction, of norm `<= 3 rho_e` | `pathHamiltonian_sub_cut`, `norm_edgePart_le` | same |
| the split cap survives through `L` on the whole weak-edge event | `edgeSmall_subset_delayEvent` | same |
| **`(17)`**: the delay sector has probability at least `c L^{-9}` | `exists_delay_floor` | same |
| **`(17)` in shell-measure form** | `exists_delay_floor_toSphere` | `HTGeometry/PathShellOnsetMoments` |
| **`(18)` for every `p > 9`**, from the tail alone | `lintegral_onset_pow_eq_top` | same |
| **`(18)` at the boundary `p = 9`** | `lintegral_onset_rpow_nine_eq_top` | same |
| the delay sector has positive measure, and a finite seed family has one member serving a positive-measure part of it | `pathShellProb_delayEvent_pos`, `exists_fixed_seed_on_delay` | `HTGeometry/PathShellFixedSeed` |

The onset time enters the two divergence theorems only through the interface
`delayEvent ... L ⊆ {u | L < τ u}` -- survival of the split cap through `L` makes the onset time
later than `L` -- together with its measurability.  Both are properties of the onset random variable
itself, not of this proof.

### What remains

Theorem C (the fully coupled `10n-8` shortcut law), and, for the weak-cut instance, the parent
inputs that identify `tau` with the first full-complexity time: the uniform split synthesis
certificate `(16)` for the fixed product cubic seed, and the plateau height `s_n` that separates it
from the cap.  The carrier/patch/conull route of Theorem A remains available as the abstract
alternative; the instance above bypasses it.

## Lean progress -- Theorem C's collision bound `(22)` (2026-08-21)

`(22)` is the analytic crux of the fully coupled law: on the tube around the diagonal carrier the
fixed seed `|+>^{⊗n}` must stay capacity-good.  The card's proof invokes the rank-one Davis--Kahan
theorem; the Lean proof does not need it, and is elementary.

`formal/GaloisForLFunctions/HTGeometry/NearDiagonalOverlapFlatness.lean` (new, umbrella-wired,
axiom-clean):

| Card item | Declaration |
|---|---|
| the basis directions whose carrier energy misses an eigenvalue by half a gap | `farSet` |
| separated energies leave at most one near direction | `card_compl_farSet_le_one` |
| **the eigenvector's weight on the far directions is at most `4δ²/γ²`** | `sum_sq_far_le` |
| **the flat-overlap bound**: every unit eigenvector of a `δ`-nearby operator overlaps a constant-modulus seed by at most `c + 2δ/γ` | `norm_inner_eigenvector_uniform_le` |
| **`(22)`**: hence the spectral collision is at most `(c + 2δ/γ)²`, which is `O(1/D)` at `c = D^{-1/2}` and `δ ≤ γ/(4√D)` | `spectralCollision_le_of_near_diagonal` |

The mechanism is one Parseval split, not a perturbation theorem.  If `He = μe` and
`‖H - diag E‖ ≤ δ` then `‖(diag E - μ)e‖ ≤ δ`, so `∑_k |E_k-μ|²|e_k|² ≤ δ²`; separation of the
carrier energies leaves at most one `k` with `|E_k-μ| < γ/2`, so the weight of `e` off that single
direction is at most `(2δ/γ)²`.  Against a seed of constant modulus `c` the near term contributes
at most `c` and the far term at most `2δ/γ` by Cauchy--Schwarz.  Finally
`∑_j p_j² ≤ (max_j p_j)∑_j p_j = max_j p_j`, so the collision inherits the square of the overlap
bound.  No eigenvector labelling, no contour and no sin-theta theorem appears, and the bound holds
for *every* eigenvector rather than a matched one -- which is what the collision functional needs.

At `c = D^{-1/2}` (the uniform superposition) and tube radius `δ ≤ γ_n/(4√D)` this gives
collision `≤ 9/(4D)`, sharper than the card's `81/(16D)`.

### What remains

Theorem C's remaining data, all on the concrete path shell: that the diagonal carrier
`F_diag = span{Z_i} + span{Z_iZ_{i+1}}` gives a *diagonal* matrix with the computational-basis
energies (the corpus already has the all-`Z` diagonalization at `pauliEnsembleOp_center` /
`zProfile`), the compact patch with distinct energies and its uniform gap `γ_n`, the carrier
compiler certificate for `|+>^{⊗n}`, and then `(23)`--`(24)` are `incubation_tail_lower` and the
moment divergence at `d = 10n-8` in place of `9`.  The transverse splitting itself is owned:
`IsDiagLabel`, `card_diagLabel = 2n+3`, `card_offDiagLabel = 10n+12` and `pathPatchIsometry` in
`HTGeometry/PathShellPatchTransport`, with the patch and its annulus in
`HTGeometry/DiagonalPatchConstruction`.  Section 2's `(16)` and the plateau height `s_n` are
unchanged.

## Lean progress -- Theorem C's carrier and its energy gap (2026-08-21)

Three further umbrella-wired, axiom-clean modules supply the geometric data of `(19)`--`(22)` on the
concrete path shell.

`formal/GaloisForLFunctions/HTGeometry/PathDiagonalCarrier.lean`:

| Card item | Declaration |
|---|---|
| the `Z` onsite word and the `ZZ` coupling word are `Z` strings | `onsiteWord_two`, `couplingWord_zz` |
| **`(19)`**: the classical Ising energy of a configuration under a carrier coefficient vector | `pathDiagEnergy` |
| **the carrier Hamiltonian is diagonal**, with those energies | `pathHamiltonian_eq_diagonal` |
| **`(21)`**: the uniform superposition, a unit state of constant modulus `D^{-1/2}` | `uniformSeed`, `norm_uniformSeed`, `norm_eucVec_uniformSeed` |
| the energies are continuous in the coefficients | `continuous_pathDiagEnergy` |
| a compact separated set of carrier coefficients has a uniform energy gap | `exists_uniform_energy_gap` |

`formal/GaloisForLFunctions/HTGeometry/BaseThreeSignSeparation.lean`:

| Card item | Declaration |
|---|---|
| the `±1` sign of a configuration at a site | `siteSign` and its modulus/difference laws |
| the geometric identity `∑_{k<S} 2·3^k = 3^S − 1` | `sum_lt_three_pow` |
| **base-three separation**: distinct configurations differ by at least two units in the weighted sign sum | `two_le_abs_sum_signDiff` |

`formal/GaloisForLFunctions/HTGeometry/PathCarrierSeparatingDirection.lean`:

| Card item | Declaration |
|---|---|
| the singleton and pair `Z` signs as site signs | `zSetSign_singleton_eq`, `zSetSign_pair_eq` |
| **the separating carrier direction**: onsite weights `A·3^s`, every edge coupling `b` | `sepCarrier`, `sepCarrier_offDiag`, `pathDiagEnergy_sepCarrier` |
| **the energies are separated** by `2A − 2b(n+1)` | `abs_sub_pathDiagEnergy_sepCarrier_ge` |
| the energies are `(2n+3)`-Lipschitz in the coefficients | `abs_pathDiagEnergy_sub_le` |
| **a uniform gap on the whole neighbourhood** of the direction | `gap_near_sepCarrier` |

This settles the card's parenthetical "such a patch exists because degeneracies form a finite union
of proper hyperplanes, while the strong-edge condition is open": the direction is explicit rather
than obtained from a genericity argument, its edge couplings are all equal to `b` -- so `(25)`
holds on it by construction -- and the separation is quantitative, hence survives a ball of radius
`(2A−2b(n+1))/(4(2n+3))` around it.  Choosing `A > b(n+1)` makes the gap positive.

### What remains

Theorem C's assembly: instantiate `spectralCollision_le_of_near_diagonal` at the diagonal patch
around `sepCarrier` (its hypothesis `‖H − diag E‖ ≤ δ` is `norm_pathHamiltonianLM_sub_le` composed
with `pathHamiltonian_eq_diagonal`, and its `gap` is `gap_near_sepCarrier`), then feed the resulting
`(22)` into `incubation_tail_lower` at the diagonal splitting `card_diagLabel = 2n+3`,
`card_offDiagLabel = 10n+12`, and finally run the moment divergence at `d = 10n-8` in place of `9`.
The carrier compiler certificate `(4)` for `|+>^{⊗n}` under commuting `Z` and `ZZ` rotations stays an
input, exactly as it is in the sibling incubation card's `hcert`.  Section 2's `(16)` and the
plateau height `s_n` are unchanged.
