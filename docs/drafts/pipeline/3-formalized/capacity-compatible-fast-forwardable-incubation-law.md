# Capacity-compatible fast-forwardable strata create complexity incubation tails

- **ID:** capacity-compatible-fast-forwardable-incubation-law
- **Stage:** 3 -- formalized in Lean 4
- **Type:** theorem / static-local complexity onset / fast-forwarding singularity
- **Parents:** ../3-formalized/fast-forwardable-stratum-codimension-obstruction.md,
  ../3-formalized/weak-interaction-recurrence-singularity-law.md,
  cubic-phase-seeded-static-local-full-scale-plateau-law.md
- **Status:** `[FORMALIZED] [FRONTIER ADVANCE] [NOVELTY UNVERIFIED]`
- **Date:** 2026-08-09

## Public sentence

A local quantum system can already possess maximal eventual complexity, maximal spectral
independence, and strong coupling across every spatial cut while remaining efficiently reproducible
for as long as desired. Every suitably visible fast-forwardable model contributes a
delayed-but-eventually-complex lower tail whose forced power is its codimension.

## 1. Abstract incubation theorem

Let \(X=S^{m-1}\) be a unit coefficient shell with normalized surface measure \(\sigma\), and let

\[
 H:\mathbb R^m\longrightarrow\operatorname{Herm}(\mathcal H_D)
 \tag{1}
\]

be real-linear with

\[
 \|H(x)-H(y)\|_{\rm op}\le L_H\|x-y\|_2.                       \tag{2}
\]

Let \(F\le\mathbb R^m\) have dimension \(f\), put \(d=m-f\), and let
\(P\subset F\cap X\) be a positive-measure compact patch. Denote by
\(\mathcal N_r(P)\) its Euclidean \(r\)-neighbourhood in \(X\).

Fix a finite seed family \(\mathcal Q\), circuit errors

\[
 0\le\eta<\epsilon_-<\epsilon_+<1,                              \tag{3}
\]

and a finite gate alphabet. Suppose the following independently checkable certificates are given.

1. **Uniform carrier compiler.** There is \(B<\infty\) such that for every
   \(y\in P\), every \(\chi\in\mathcal Q\), and every real \(t\),
   \[
    C_\eta(e^{-itH(y)}\chi)\le B.                               \tag{4}
   \]
2. **Basis-uniform capacity seeds.** For every orthonormal basis \(e\) of
   \(\mathcal H_D\), at least a fraction \(1-\beta\) of the seeds obey
   \[
    \sum_{j=1}^D|\langle e_j,\chi\rangle|^4\le {c_0\over D}.    \tag{5}
   \]
3. **Generic physical completion.** A conull subset \(G\subset X\) has simple spectrum,
   maximal projective rational rank, and cyclicity for every seed in \(\mathcal Q\). The fixed
   local two-query non-Haar separator applies to every \(H(x)\) in the family.
4. **Completed-phase capacity.** The existing collision-to-capacity theorem at errors
   \((\epsilon_-,\epsilon_+)\) turns (5) into depth
   \[
    s_D\ge c_1D/\log M_n                                      \tag{6}
   \]
   on a continuous block of length at least \(\exp(c_2D)\), followed by projective recurrence.

Items 1--4 are certificate data, not conclusions disguised as assumptions. Item 1 is a concrete
compiler on a named carrier, item 2 is a finite moment statement, and items 3--4 are already proved
generic spectral and completed-phase laws.

### Theorem A -- codimension incubation law

For every \(L>0\), put

\[
 r_L=\min\left\{r_0,\ {\epsilon_- -\eta\over2L_HL}\right\},     \tag{7}
\]

where \(r_0>0\) is any radius on which nearest-point directions into \(P\) remain inside the
chosen patch. Then one seed \(\chi_L\in\mathcal Q\) satisfies

\[
\begin{aligned}
\sigma\Bigl\{x\in\mathcal N_{r_L}(P):\;&
 C_{\epsilon_-}(e^{-itH(x)}\chi_L)\le B\quad(0\le t\le L),\\
&H(x)\text{ later has the plateau (6) for }\exp(c_2D)\text{ time},\\
&H(x)\text{ later recurs and is locally non-Haar for every time}
\Bigr\}\\
&\ge (1-\beta)\,\sigma(\mathcal N_{r_L}(P)).                   \tag{8}
\end{aligned}
\]

Moreover there are \(a_P>0\) and \(r_P>0\), depending only on the finite-dimensional patch, such
that

\[
 \boxed{
 \sigma(\mathcal N_r(P))\ge a_Pr^d\qquad(0<r\le r_P).}         \tag{9}
\]

Consequently, for all sufficiently large \(L\),

\[
 \boxed{
 \Pr\{\text{easy through }L\text{ but later full plateau and recurrence}\}
 \ge A_P(1-\beta)L^{-d}.}                                      \tag{10}
\]

The guaranteed contribution has transverse-codimension exponent \(d=m-f\). No claim is made that
this is the complete delay distribution or its sharp exponent after all delayed sectors are united.

### Proof

Fix \(x\in\mathcal N_{r_L}(P)\) and choose \(y\in P\) with
\(\|x-y\|_2\le2r_L\). Duhamel's formula gives, uniformly for \(0\le t\le L\),

\[
\begin{aligned}
\|e^{-itH(x)}-e^{-itH(y)}\|_{\rm op}
&\le t\|H(x)-H(y)\|_{\rm op}\\
&\le 2LL_Hr_L\le\epsilon_- -\eta.                              \tag{11}
\end{aligned}
\]

The carrier circuit (4), applied to the same seed, therefore prepares
\(e^{-itH(x)}\chi\) to error \(\epsilon_-\) with at most \(B\) gates. This proves the first line
inside (8) for every seed.

For each \(x\), apply (5) to an eigenbasis of \(H(x)\). Average its indicator first over
the finite seed family and then over \(x\in\mathcal N_{r_L}(P)\). Fubini gives one fixed seed
\(\chi_L\) for which the collision-good Hamiltonian subset has relative measure at least
\(1-\beta\). Removing \(X\setminus G\) changes no measure. On the remainder, maximal
projective rank and cyclicity give completed phase equidistribution and recurrence; item 4 gives
the continuous full plateau, and the local separator is time-uniform. This proves (8).

For (9), decompose a uniform shell point into \(F\oplus F^\perp\). The squared norm \(U\) of its
transverse projection has law

\[
 U\sim\operatorname{Beta}(d/2,f/2).                            \tag{12}
\]

Conditional on \(U\), the direction of the \(F\)-projection is uniform on \(F\cap X\).
Restrict that direction to a compact positive-measure subset of the interior of \(P\), and
restrict \(U\le r^2/4\). The beta density is bounded below by a positive multiple of
\(u^{d/2-1}\) on a sufficiently short interval. Integration gives \(a_Pr^d\). Combining with
(7)--(8) proves (10).

No inverse theorem is claimed: other delayed sectors may exist. Equation (10) is the universal
forced contribution of every independently certified capacity-compatible fast-forwardable patch.

## 2. Ordinary nearest-neighbour instantiation

Put \(D=2^n\) and use the full one-site plus nearest-neighbour two-site Pauli shell

\[
 m=3n+9(n-1)=12n-9.                                            \tag{13}
\]

Let \(F_{\rm diag}\) be the diagonal path subspace

\[
 H_0(a,b)=\sum_{i=1}^n a_iZ_i+\sum_{i=1}^{n-1}b_iZ_iZ_{i+1}.   \tag{14}
\]

It has dimension

\[
 f=2n-1,\qquad d=m-f=10n-8.                                   \tag{15}
\]

Choose a compact positive-measure patch \(P_n\subset F_{\rm diag}\cap S^{m-1}\) on which

\[
 |b_i|\ge {b_0\over\sqrt n}\qquad(1\le i<n)                   \tag{16}
\]

for a numerical \(b_0>0\). Concretely, take a spherical ball of Euclidean radius
\(\rho/\sqrt n\), for fixed sufficiently small \(\rho>0\), around the normalized all-positive
coefficient vector. Then (16) holds and its normalized \((f-1)\)-sphere measure is at least
\(\exp[-O(n\log n)]\).

Take the complete cubic-phase family

\[
 \chi_h=D^{-1/2}\sum_{z\in\{0,1\}^n}\exp(2\pi ih(z)/8)|z\rangle. \tag{17}
\]

Every seed has exact preparation cost \(O(n^3)\). Since all terms in (14) commute,
\(e^{-itH_0(a,b)}\chi_h\) is prepared by that seed circuit followed by \(n\) one-qubit
\(Z\)-rotations and \(n-1\) two-qubit \(ZZ\)-rotations. Uniform finite-alphabet compilation gives

\[
 B_n(\eta)=O\!\left(n^3+n\log^c(n/\eta)\right)                 \tag{18}
\]

for a gate-set constant \(c\), independently of \(t,a,b\). Thus (4) is a literal compiler, not
membership in an easy set.

The cubic-phase collision theorem gives, for every possibly entangled eigenbasis,

\[
 \Pr_h\left\{
 \sum_j|\langle e_j,\chi_h\rangle|^4>{2+\kappa\over D}
 \right\}
 \le {96\over\kappa^2D}.                                      \tag{19}
\]

Hence \(\beta=96/(\kappa^2D)\). Generic maximal projective rank and simultaneous cyclicity are
conull in the path-local shell. All abstract certificates are therefore present.

### Theorem B -- fully coupled sleeping-chaos family

For fixed errors and every sufficiently large \(n\), every sufficiently large prescribed delay
\(L\) admits one fixed cubic-phase seed \(\chi_{n,L}\) and a shell subset
\(\mathcal I_{n,L}\) satisfying

\[
 \boxed{
 \sigma(\mathcal I_{n,L})
 \ge A_n\left(1-{96\over\kappa^2D}\right)L^{-(10n-8)}.}        \tag{20}
\]

Every \(H\in\mathcal I_{n,L}\) simultaneously obeys:

1. \(C_{\epsilon_-}(e^{-itH}\chi_{n,L})\le B_n(\eta)\) for every \(0\le t\le L\);
2. its projective spectral rank is \(D-1\);
3. its seed collision is at most \((2+\kappa)/D\);
4. its later complexity exceeds \(cD/\log M_n\) continuously for \(\exp(cD)\) time;
5. it later recurs to the easy seed;
6. the fixed local two-query protocol separates its propagator from Haar randomness for every
   real time;
7. every spatial edge remains quantitatively coupled:
   \[
    \boxed{
    \min_{1\le i<n}\|V_i(H)\|_{\rm op}\ge {b_0\over2\sqrt n}.}  \tag{21}
   \]

### Proof

Apply Theorem A to \(F_{\rm diag}\) and \(P_n\). The operator Lipschitz bound

\[
 \|H(x)-H(y)\|_{\rm op}\le\|x-y\|_1\le\sqrt m\,\|x-y\|_2       \tag{22}
\]

allows \(L_H=\sqrt m\). For large \(L\), the radius (7) also obeys
\(3r_L\le b_0/(2\sqrt n)\). On edge \(i\), the diagonal centre has interaction
\(b_iZ_iZ_{i+1}\), while the complete nine-coefficient perturbation has operator norm at most
three times its Euclidean norm. The reverse triangle inequality and (16) prove (21).
Equations (15) and (19) turn (10) into (20). The remaining items are precisely the
generic-completion conclusions already assembled in Theorem A.

The dimension dependence hidden in \(A_n\) is controlled. The radius-\(\rho/\sqrt n\) spherical
patch above has measure at least \(\exp[-O(n\log n)]\). In the beta integral (12), both parameters
are linear in \(n\), so its normalization contributes \(\exp[O(n)]\); replacing \(r\) by
\((2L_HL)^{-1}(\epsilon_- -\eta)\), with \(L_H=\sqrt m\), costs a further
\(m^{-d/2}=\exp[-O(n\log n)]\). Hence, for fixed errors,

\[
 A_n\ge \exp[-O(n\log n)].                                    \tag{23}
\]

At Brown delay \(L=D/\operatorname{poly}(n)\), equation (20) has logarithm

\[
 -(10\log2)n^2+O(n\log n),                                    \tag{24}
\]

so this conductance-good incubation sector has probability \(\exp(-\Theta(n^2))\). It is smaller
than the weak-cut \(L^{-9}\) sector but survives after weak cuts are excluded.

## 3. Exact frontier correction

The following successively stronger onset conjectures are now false.

### C0 -- spatial conductance is sufficient

[FALSIFIED]. The Lean-proved gapped-eigenstate box retains nonzero path interactions while the
chosen eigenstate has zero-gate complexity for every time.

### C1 -- conductance plus optimal collision is sufficient

[FALSIFIED]. The diagonal carrier (14) has strong coupling on every edge and every cubic seed has
computational-basis collision exactly \(1/D\), yet its whole orbit has the compiler (18).

### C2 -- conductance, optimal collision, and maximal projective rank are sufficient

[FALSIFIED]. Every Hamiltonian in \(\mathcal I_{n,L}\) has all three properties and still has
arbitrarily prescribed polynomial-complexity incubation.

### C3 -- any qualitative chaos checklist fixes onset

[FALSIFIED AS A REPRESENTATION]. Dense or conull exact properties hold arbitrarily close to the
certified carrier. Duhamel continuity preserves the carrier's finite-time compiler while those
properties can change discontinuously. No finite list of such qualitative labels can supply a
dimension-uniform onset deadline.

### Positive survivor

For each independently certified fast-forwardable patch \(P\) compatible with the seed's full
spectral capacity, there is a load-bearing quantitative distance. Define the non-circular patch
condition number

\[
 \tau_P(H)
 ={1\over L_H\,\operatorname{dist}(H,P)}.                     \tag{25}
\]

It uses a separately supplied compiler on \(P\), never the unknown minimal circuit of \(H\).
Theorem A proves that \(\tau_P\) lower-bounds onset up to the fixed error margin, and (10) proves
that this patch contributes the carrier-codimension power to the delay tail.

This condition is not claimed sufficient. Nor is a union over “all carriers” defined: doing so
would reproduce the circular inverse-classification problem already retired. The exact consequence
for the Brown programme is narrower and testable. Any proposed shell theorem must name its
exceptional sets and pay, at minimum, both the weak-cut tube and the diagonal-carrier tube at their
proved codimension scales before attacking geometric-skeleton Bellman escape on the complement.
That target is strictly sharper than conductance conditioning and is not killed by the diagonal
family, but it is not yet a sufficiency theorem.

## 4. Relation to prior work and novelty boundary

- [LOCAL-RESEARCH] [LEAN-PROVED]
  fast-forwardable-stratum-codimension-obstruction proves that an \(f\)-dimensional uniformly
  synthesizable coefficient stratum forces an \(L^{-(m-f)}\) shortcut floor. Theorem A does not
  reclaim that Duhamel/codimension mechanism. Its candidate new content is that, when the same
  carrier is capacity-compatible, almost the entire generic transverse tube consists of systems
  that are easy through \(L\) **and later attain the full plateau, recurrence, and non-Haar
  locality simultaneously**.
- [LOCAL-RESEARCH] [LEAN-PROVED]
  weak-interaction-recurrence-singularity-law proves that arbitrarily weak interactions can
  change completed recurrence while bounded-time observables remain close. The present theorem
  upgrades the completed side to near-maximal circuit complexity and gives the codimension tail.
- [LITERATURE] Atia and Aharonov prove that commuting local and quadratic fermionic Hamiltonians
  can be fast-forwarded and connect fast-forwarding to precise energy measurement. The carrier
  compiler itself is therefore known, not novel.
- [LITERATURE] Gu, Somma and Sahinoglu enlarge the positive fast-forwarding classes. Their results
  do not state a delayed-yet-full-complexity transverse-tube law.
- [LITERATURE] Balasubramanian, DeCross, Kar and Parrikar give an eigenstate-complexity condition
  ensuring local minimality of a Nielsen geodesic for exponential time. They do not prove the
  fixed-resolution, nonuniform state-circuit law (8)--(10).

No located primary source states the conjunction (20)--(21). Search absence is not proof of
priority; the result remains [NOVELTY UNVERIFIED] pending specialist review.

Primary sources:

- Y. Atia and D. Aharonov, *Fast-forwarding of Hamiltonians and exponentially precise
  measurements*, [arXiv:1610.09619](https://arxiv.org/abs/1610.09619).
- S. Gu, R. D. Somma and B. Sahinoglu, *Fast-forwarding quantum evolution*,
  [arXiv:2105.07304](https://arxiv.org/abs/2105.07304).
- V. Balasubramanian, M. DeCross, A. Kar and O. Parrikar, *Quantum complexity of time evolution
  with chaotic Hamiltonians*, [arXiv:1905.05765](https://arxiv.org/abs/1905.05765).

## 5. Hostile audit

1. The theorem proves a lower tail of delayed onset, not the Brown upper escape bound.
2. The diagonal carrier is integrable and the transverse tube is fine-tuned. Equation (20)
   quantifies that tuning rather than hiding it.
3. The fixed seed may depend on \(n,L\). It is not resampled in time, but no single explicit seed
   is claimed uniformly over all delays.
4. Exact maximal projective rank is a fragile arithmetic property, not conventional many-body
   chaos. The theorem's point is precisely that qualitative completed-time properties cannot set
   a finite-time clock.
5. The abstract law is one-sided. It does not classify every fast-forwardable or delayed family,
   and it avoids the circular inverse theorem already retired in
   autonomous-shortcut-free-energy-law.md.
6. Scientific novelty lies only in the capacity-compatible composition and its ordinary-local
   instantiation. Duhamel continuity, commuting compilation, beta tubes, and fast-forwarding are
   established mechanisms.
7. The Lean formalization and axiom audit are complete; audit items 1--6 stand unchanged.

## Lean status -- Theorem A is formal; the instantiation needs its parent cards

New modules (umbrella-wired, axiom-clean, no `sorry`):
`formal/GaloisForLFunctions/HTGeometry/IncubationTubeTransport.lean`,
`SphericalPatchTube.lean`, `CapacityIncubationLaw.lean`.

| Card item | Declaration | Module |
|---|---|---|
| `(11)` Duhamel transport across the whole window `[0,L]` | `approxComplexity_orbitState_le_of_window` | `IncubationTubeTransport` |
| the same, from membership in the spherical tube | `approxComplexity_le_of_mem_patchThickening` | `CapacityIncubationLaw` |
| finite Fubini seed selection (averaging step) | `sum_measureReal_ge_of_pointwise`, `exists_measureReal_ge`, `exists_measureReal_ge_of_pointwise` | `IncubationTubeTransport` |
| the same, restricted to the tube | `exists_seed_measureReal_ge` | `CapacityIncubationLaw` |
| "removing `X \ G` changes no measure" | `measureReal_inter_conull` | `CapacityIncubationLaw` |
| normalization is two-Lipschitz off the origin | `norm_normalize_sub_normalize_le` | `SphericalPatchTube` |
| the carrier tube lies in the cone over the thickening | `patchTube_subset_cone` | `SphericalPatchTube` |
| the tube volume is the carrier factor times `rho^d` | `volume_patchTube` | `SphericalPatchTube` |
| **`(9)`**: the thickening has surface measure at least `a_P r^d` | `toSphere_patchThickening_ge` | `SphericalPatchTube` |
| **`(10)`**: the codimension tail `L^{-d}` | `incubation_tail_lower` | `CapacityIncubationLaw` |
| `(22)` the shell is `sqrt(m)`-Lipschitz | `norm_sum_smul_le_sum_abs`, `sq_sum_abs_le_card_mul_sum_sq` | `IncubationTubeTransport` |
| `(21)` half the edge coupling survives the tube | `norm_ge_half_of_perturbation` | `IncubationTubeTransport` |
| Duhamel operator bound `‖e^{-itH}-e^{-itK}‖ <= |t| ‖H-K‖` | `dist_orbitState_le` | `FastForwardableStratumCodimension` |
| the certificate survives a move of size `delta` | `exists_witness_of_dist_le`, `approxComplexity_le_of_witness` | `FastForwardableStratumCodimension` |

Equation `(9)` is proved by the cone comparison rather than by the beta density of `(12)`: the
carrier annulus times a transverse ball of radius `r/8` embeds in the cone over the `r`-thickening,
because normalization is two-Lipschitz, and the product volume of that tube is the carrier factor
times `(r/8)^d` times the unit transverse ball.  This is the same `d = m - f` exponent with an
explicit constant, and it avoids the `Beta(d/2,f/2)` density entirely.

## Lean progress -- Theorem B, the ordinary nearest-neighbour instantiation (2026-08-21)

Theorem A is abstract in the coefficient space; Theorem B needs the nearest-neighbour shell to *be*
one, with the diagonal family `(14)` as carrier.  Five new modules supply the identification and the
certificates.

`formal/GaloisForLFunctions/HTGeometry/CrossSphereIsometryTransport.lean`:

| Card item | Declaration |
|---|---|
| a linear isometry equivalence restricted to the unit spheres | `crossSphereMap`, `continuous_crossSphereMap` |
| it commutes with dilation of sets and preserves the cone | `image_smul_set_isometry`, `image_crossSphereMap_preimage` |
| **the spherical measure transports** | `toSphere_preimage_crossSphereMap` |

`formal/GaloisForLFunctions/HTGeometry/PathShellPatchTransport.lean`:

| Card item | Declaration |
|---|---|
| the diagonal labels `(14)`: one `Z` per site and one `ZZ` per edge | `IsDiagLabel`, `diagLabelEquiv` |
| **`(15)`**: `f = 2n+3` and `d = 10n+12` at `n+2` qubits | `card_diagLabel`, `offDiagLabelEquiv`, `card_offDiagLabel` |
| **the shell is the patch space of the diagonal splitting** | `pathPatchEquiv`, `pathPatchIsometry` |
| the shell map as a real-linear map, and **`(22)`** its `√m` Lipschitz constant | `pathHamiltonianLM`, `norm_pathHamiltonian_le`, `norm_pathHamiltonianLM_sub_le` |
| the degenerate directions stay null after the transport | `toSphere_preimage_pathBadSphere_eq_zero` |

`formal/GaloisForLFunctions/HTGeometry/DiagonalPatchConstruction.lean`:

| Card item | Declaration |
|---|---|
| the normalized all-positive direction | `uniformDir`, `norm_uniformDir` |
| the compact carrier patch: the closed cap of radius `ρ` | `sphericalCap`, `isCompact_embedPatch_sphericalCap`, `nonempty_embedPatch_sphericalCap` |
| **`(16)`**: every coordinate of the cap is at least `f^{-1/2} − ρ` | `sphericalCap_coord_ge` |
| the carrier factor `a_P` is positive | `volume_patchAnnulus_sphericalCap_pos` |

`formal/GaloisForLFunctions/HTGeometry/PatchChainPullback.lean`:

| Card item | Declaration |
|---|---|
| the chain-coefficient reading of the patch space | `pathToChainIsometry`, `patchCoeffIsometry`, `patchToCoeff`, `toSphere_preimage_patchToCoeff` |
| item 3, **the conull generic completion** | `chainBadSphere`, `toSphere_chainBadSphere_eq_zero`, `toSphere_preimage_chainBadSphere_eq_zero` |
| the eigenbasis at a patch direction, and its maximal projectivity | `patchEigenBasis`, `isOrthoEigenBasis_patchEigenBasis`, `maximallyProjectiveEnergy_patchEigenValues`, `mem_simpleLocus_of_notMem_chainBadSphere` |
| item 2, **the density certificate `(19)`**: all but `96/(κ²D)` of the cubic seeds are good at *every* direction | `patchGood`, `measurableSet_patchGood`, `density_patchGood` |
| the Hilbert--Schmidt norm of a Pauli combination, and hence `ρ_e ≤ ‖V_e‖` on the register | `hsNormSq_matrix_eq_trace`, `hsNormSq_pauliCombination`, `edgeRho_le_norm_edgePart` |
| **`(21)`**: inside the tube every edge stays coupled | `edgeCoupling_lower` |

The collision is read through the *gauge-invariant* `crossCollision`, which is continuous on the
simple locus and therefore measurable; the Fubini seed selection needs measurability, and
eigenvector measurability is not available.  On the simple locus `crossCollision_cubicSeed` converts
it back to the eigenbasis collision.

`formal/GaloisForLFunctions/HTGeometry/CapacityIncubationInstantiation.lean`:

| Card item | Declaration |
|---|---|
| the shell map on the patch space, self-adjoint and Lipschitz | `patchHamLM`, `isSelfAdjoint_patchHamLM`, `norm_patchHamLM_sub_le`, `norm_patchHam_le` |
| the cubic seed on the register, and its unit norm | `registerCubicSeed`, `finiteComplexInner_registerCubicSeed` |
| the collision at a good nondegenerate direction | `occupationCollision_eq_phaseCollision`, `phaseCollision_le_of_good` |
| **`(9)` at the constructed patch** | `toSphere_patchThickening_cap_ge`, `volume_patchAnnulus_cap_pos` |
| **Theorem B `(20)` and clauses 1--5, 7** | `exists_incubating_cubicSeed` |

`exists_incubating_cubicSeed` produces one cubic seed together with the measure bound
`(1−β)·σ(tube) ≤ σ(tube ∩ good ∩ generic)` -- which is `(8)`, and with
`toSphere_patchThickening_cap_ge` and `incubation_tail_lower` is `(20)` at `d = 10n−8` -- and, at
every direction of that set, clause 1 (`approxComplexity … ≤ B` through the whole window), clause 2
(maximal projective rank), clause 3 (collision `≤ (2+κ)/D`), clause 4 (hard at every instant of
arbitrarily late windows of length `W`), clause 5 (recurrence to the seed) and clause 7 (`(21)`).
Clause 6 is the seed-independent corpus separator
`haarBenchmark_lt_literalTwoQueryScore_of_trace_eq_zero`.

The gate model -- the alphabet `Γ`, its action, the reference state and the uniform compiler bound
`B` with its certificate -- is the card's own certificate datum 1, carried as data exactly as in
Theorem A; `(18)` is the value of that datum for the commuting diagonal family and is a
compilation count, not a theorem of this card.

## 6. Lean realization

Reused rather than rebuilt:

1. `HTGeometry/FastForwardableStratumCodimension.lean` for Duhamel tube transport;
2. the cubic-phase collision modules of the parent card;
3. the path-local maximal-projective-rank locus;
4. the completed-phase plateau, recurrence and local-separator modules;
5. added: the diagonal splitting isometry, the spherical-cap carrier, the patch pullback, and the
   final conjunction.

## Status of the card

| Card statement | Declaration |
|---|---|
| **Theorem A `(7)`--`(10)`** -- the codimension incubation law | `approxComplexity_le_of_mem_patchThickening`, `toSphere_patchThickening_ge`, `incubation_tail_lower`, `exists_seed_measureReal_ge`, `measureReal_inter_conull` |
| **`(13)`--`(16)`** -- the nearest-neighbour shell, its diagonal subspace, and the carrier patch | `card_diagLabel`, `card_offDiagLabel`, `pathPatchIsometry`, `sphericalCap_coord_ge` |
| **`(19)`** -- the cubic-phase collision density | `density_patchGood` |
| **`(20)`--`(21)`** and clauses 1--5, 7 of Theorem B | `exists_incubating_cubicSeed` |
| clause 6, permanent non-Haar locality | `haarBenchmark_lt_literalTwoQueryScore_of_trace_eq_zero` |
| **`(22)`** -- the shell is `√m`-Lipschitz | `norm_pathHamiltonianLM_sub_le` |

All statements are unconditional and axiom-clean (`propext`, `Classical.choice`, `Quot.sound`
only).  The card is fully formalized.

## Lean progress -- the carrier compiler certificate is discharged (2026-08-21)

`hcert` in `exists_incubating_cubicSeed` asserted that some gate alphabet compiles the carrier
evolution of the cubic seed.  On the diagonal carrier that is not an assumption but a theorem about
an explicit alphabet, and the alphabet is exactly the one the card describes: one gate per
multilinear monomial of degree at most three, plus one rotation per carrier generator.

`formal/GaloisForLFunctions/HTGeometry/PhaseGridApproximation.lean` and
`formal/GaloisForLFunctions/HTGeometry/DiagonalRotationCompiler.lean` (new, umbrella-wired,
axiom-clean) supply the rotation half:

| Card item | Declaration |
|---|---|
| the circle is `1`-Lipschitz in its angle; unit-modulus products telescope | `norm_exp_sub_exp_le`, `norm_prod_sub_prod_le` |
| **grid approximation**: `m` equally spaced angles match every real phase to within `2π/m`, for both signs at once | `gridAngle`, `exists_gridIndex` |
| the carrier Hamiltonian is diagonal, and its evolution is the diagonal of the phases | `pathHamiltonian_embed_eq_diagonal_carrierEnergy`, `unitaryEvolution_diagonal_phase` |
| **the rotation certificate**: depth `2n+3`, error `(2n+3)·2π/m`, for *any* unit seed, every carrier point and every time | `exists_diagAlphabet_word`, `exists_diagAlphabet_compiler` |

`formal/GaloisForLFunctions/HTGeometry/CubicSeedPhaseCompiler.lean` (new, umbrella-wired,
axiom-clean) supplies the seed half:

| Card item | Declaration |
|---|---|
| the eighth-root character is additive-to-multiplicative | `charEight_add`, `charEight_sum`, `norm_charEight` |
| **one diagonal phase gate per monomial** | `monPhaseGate`, `prod_monPhaseGate` |
| **the cubic seed is exactly that word applied to `\|+>^{⊗n}`** | `registerCubicSeed_eq_mulVec` |
| the combined alphabet | `CubicDiagAlphabet`, `cubicDiagGate`, `cubicDiagAct` |
| **the certificate for every cubic seed, from one reference state** | `exists_cubicDiagAlphabet_compiler` |
| **the incubation law with no hypothesis on any gate alphabet** | `exists_incubating_cubicSeed_compiled` |

The word is `(2n+3)` rotations followed by one gate per monomial, so its length is
`card (MonLe) + (2n+3) = O(n³)` -- the card's own `O(n³)` preparability -- and the monomial half is
*exact*: all the error comes from discretizing the rotation angles, and is `(2n+3)·2π/m`.  The
alphabet has `8·card (MonLe) + (2n+3)m` letters with `m = O(n/η)`, so `log M_n = O(log n)`, the
regime the plateau counting condition assumes.

The seed enters the rotation estimate only through `‖ψ‖ = 1`, which is why the same alphabet serves
every cubic seed with a single reference state: the monomial word prepares the seed, the rotation
word evolves it, and the two commute because both are diagonal.
