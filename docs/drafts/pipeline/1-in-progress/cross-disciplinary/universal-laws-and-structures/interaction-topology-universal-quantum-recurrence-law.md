# Interaction topology fixes the completed law of quantum recurrence

- **ID:** `interaction-topology-universal-quantum-recurrence-law`
- **Stage:** 1-in-progress
- **Type:** MASTER CONJECTURE / GENERIC LOCAL QUANTUM DYNAMICS /
  RECURRENCE TORUS / ALL-ORDER RETURN STATISTICS
- **Date:** 2026-07-30
- **Status:** `[CONJECTURE] [PAPER-PROOF COMPONENTS EXIST]`
  `[OPEN CORE] [NOVELTY UNVERIFIED]`
- **Internal parents:**
  `../2-fully-proven/arbitrary-graph-quantum-temporal-curvature-law.md`,
  `../2-fully-proven/local-interaction-replica-collision-extremality.md`,
  `universal-replica-collision-law-of-quantum-return.md`
- **Statement:** For a generic finite local Hamiltonian, interaction
  components are exactly the irreducible factors of its completed recurrence
  torus; this factorization determines every long-time return moment, and a
  connecting interaction removes every replica collision not forced by the
  remaining component factorization.

## Goal

Replace a collage of recurrence bounds, collision identities, spectral-form-
factor limits and locality results by one law:

> **Generic quantum recurrence remembers exactly how the Hamiltonian
> factorizes, and nothing else.**

For a connected interacting system the completed projective orbit is the
full spectral phase torus. For disconnected components it is the tensor
product of their phase tori. Every continuous completed-return statistic and
every replica moment is the Haar statistic of that one torus. The law should
answer the external question whether two-body locality forces hidden energy
resonances, explain why independent-phase plateau laws apply to deterministic
interacting Hamiltonians, and classify the exponential/product/log-normal
late-time regimes as factorization shadows of one object.

The paper is theoretical mathematical physics. Its novelty cannot be the
classical Kronecker--Weyl theorem, the collision identity, the independent-
phase random-walk law, or formal verification. Novelty must be the exact
local-generator theorem and the new order-two tomography law: recurrence
collision classes measure the product geometry of noninteracting components.

## Exact finite law

Let \(V\) be finite, let
\(\mathcal H=\bigotimes_{v\in V}\mathbb C^{q_v}\), \(q_v\ge2\), and let
\(\mathfrak H\) be a finite interaction hypergraph. Let
\(\mathcal L_{\mathfrak H}\) contain arbitrary one-site Hermitian terms and
arbitrary Hermitian terms on every hyperedge. Let
\(\pi_0(\mathfrak H)\) be its connected components and
\[
 D_C=\prod_{v\in C}q_v.
\]

`[PAPER-PROVED — GENERATOR FORM]` A dense full-Lebesgue-measure
\(G_\delta\) subset of \(\mathcal L_{\mathfrak H}\) has simple spectrum and
projective spectral rank
\[
 \tau(H)=\sum_{C\in\pi_0(\mathfrak H)}(D_C-1).       \tag{1}
\]
Equivalently, after writing \(H=\sum_C H_C\), the component gap modules are
mutually rationally transverse and every component spectrum has maximal
projective rank.

For ordinary two-body interaction graphs, `(1)` is
`[LOCAL-RESEARCH] [PAPER-PROVED]` in
`arbitrary-graph-quantum-temporal-curvature-law.md`. The componentwise
genericity gap is closed in
`../../../3-formalized/disconnected-local-spectral-factorization-genericity.md`,
and the all-interaction-order lift is dependency-closed in
`../2-fully-proven/hypergraph-local-projective-spectral-factorization.md`.
The generator law remains unauthorized for the manuscript until exact Lean
formalization.

`[PAPER-PROVED — ORBIT FORM]` For every Hamiltonian in this generic set,
\[
 \overline{\{[e^{-itH}]:t\in\mathbb R\}}
 \cong
 \prod_{C\in\pi_0(\mathfrak H)}\mathbb T^{D_C-1},    \tag{2}
\]
where the embedding sends component phase vectors to their tensor-product
phase tensor. Moreover, for every continuous function \(f\) on the
projective unitary group,
\[
 \lim_{T\to\infty}\frac1{2T}\int_{-T}^{T}
 f([e^{-itH}])\,dt
 =
 \int_{\prod_C\mathbb T^{D_C-1}}f(\Phi(z))\,dm(z).   \tag{3}
\]

Equation `(3)` is a deterministic, ensemble-free completed law. It does not
assert finite mixing, chaos, Wigner--Dyson statistics, or a first-return
time.

## Exact all-order return classifier

Index the total energy eigenstates by
\(x=(x_C)_C\), and let \(p_x>0\), \(\sum_xp_x=1\), be arbitrary spectral
weights. For two independent \(m\)-samples
\(X_1,\ldots,X_m\) and \(Y_1,\ldots,Y_m\) from \(p\), let
\[
 N_C(X_1,\ldots,X_m)(a)
 =
 \#\{r:(X_r)_C=a\}
\]
be the empirical histogram in component \(C\).

`[PAPER-PROVED — COLLISION FORM]` The long-time survival-fidelity moment is
\[
\boxed{
 \lim_{T\to\infty}\frac1{2T}\int_{-T}^{T}
 \left|\sum_xp_xe^{-itE_x}\right|^{2m}dt
 =
 \mathbb P\!\left(
   N_C(X_1,\ldots,X_m)=N_C(Y_1,\ldots,Y_m)
   \ \forall C
 \right).
}                                                       \tag{4}
\]

Thus two replica samples collide exactly when every interaction component
sees the same histogram. If the interaction hypergraph is connected, this
reduces to equality of the full joint histogram and gives the universal
permutation floor. If components are disconnected, different joint
histograms with identical component marginals survive. A connecting
interaction removes exactly those factorization collisions.

### Order-two recurrence tomography

`[PAPER-PROVED] [LEAN-PROVED]` For joint spectral labels
\(x=(x_C)_C\), \(y=(y_C)_C\), let
\[
 d_H(x,y)=\#\{C:x_C\ne y_C\}.
\]
For every additive component spectrum, the complete ordered equal-energy
collision class
\[
 \mathcal R_2(x,y)=
 \{(z,w):E_z+E_w=E_x+E_y\}
\]
contains a canonical Boolean cube:
\[
\boxed{
 |\mathcal R_2(x,y)|\ge2^{d_H(x,y)}
 \quad\text{for every additive factorization},
}                                                       \tag{5}
\]
Under component projective independence, the inclusion is an equivalence
\(\mathcal R_2(x,y)\cong\{0,1\}^{d_H(x,y)}\), so equality holds in `(5)`.
Each Boolean coordinate independently decides whether one disconnected
component is exchanged between the two replicas. Consequently the
order-two collision multiplicity recovers the component Hamming distance
exactly in the independent case and supplies a universal lower bound in
every case. This is the non-formal
tomographic content missing from the earlier synthesis: recurrence does not
merely depend on factorization; its resolved collision classes measure
factor-product geometry exactly.

Operationally, \(\mathcal R_2(x,y)\) is the support of the pair-resolved
completed recurrence kernel
\[
 \lim_{T\to\infty}\frac1{2T}\int_{-T}^{T}
 e^{it[(E_z+E_w)-(E_x+E_y)]}\,dt.
\]
The theorem therefore concerns a dephasing observable, not a post hoc
combinatorial relabelling of a scalar SFF moment.

For uniform spectral weights, define
\[
 X_D(t)=D^{-1}|\operatorname{Tr}e^{-itH}|^2,\qquad
 a_{D,m}=D^{-m}\sum_{\substack{k\in\mathbb N^D\\|k|=m}}
 {m\choose k}^{2}.                                    \tag{6}
\]
Equation `(4)` gives the exact finite-size law
\[
 \lim_{T\to\infty}\frac1{2T}\int_{-T}^{T}X_D(t)^m\,dt
 =
 \prod_{C\in\pi_0(\mathfrak H)}a_{D_C,m}.             \tag{7}
\]
When every \(D_C\to\infty\) with a fixed number \(c\) of components,
\[
 \prod_Ca_{D_C,m}\longrightarrow(m!)^c.               \tag{8}
\]
Hence the connected limit is \(\operatorname{Exp}(1)\); \(c\) macroscopic
components give the product of \(c\) independent unit exponentials; and a
growing factor count enters the Gaussian/log-normal regime after centering
and scaling logarithms. The last growing-factor limit needs its exact
normalization and dependency-closed proof before promotion.

## Finite-time operational layer

For fixed replica order \(m\), let
\[
 \delta_m(H)
 =
 \min\{|E_{i_1}+\cdots+E_{i_m}
       -E_{j_1}-\cdots-E_{j_m}|:
       \text{the difference is nonzero}\}.             \tag{9}
\]
For finite spectrum, \(\delta_m(H)>0\).

`[PAPER-PROVED — FINITE-WINDOW CERTIFICATE]` The exact sinc expansion gives
\[
 \left|
 \frac1{2T}\int_{-T}^{T}F(t)^m\,dt-M_m(H,p)
 \right|
 \le \frac{1}{T\delta_m(H)}                            \tag{10}
\]
for \(T>0\), with the convention that the right side may be replaced by
\(\min(1,(T\delta_m)^{-1})\). On compact coupling sets avoiding the finitely
many order-\(m\) resonance roots of a generic one-parameter family, the
right side is uniform.

This is the required operational meaning: exact arithmetic rank governs the
completed law, while \(\delta_m^{-1}\) governs when a finite-order
experiment resolves it. No parameter-free laboratory timescale is claimed.

## External frontier

- `[LITERATURE]` Riddell--Bertini, *Phys. Rev. E* 110, 064101 (2024),
  state that no-resonance assumptions are standard, strong, and generally
  infeasible to verify analytically or numerically; they identify the
  interplay between rational independence and interacting perturbations as
  immediate future work. More damagingly for the synthesis route, their
  equations (42)--(49) already derive arbitrary-order SFF moments by
  independent history rearrangements of every rationally independent
  free-fermion mode, obtaining
  \(K_q=\binom{2q}{q}^{L}\):
  <https://arxiv.org/abs/2404.12100>.
- `[LITERATURE]` Campos Venuti--Odavić--Hamma, *Phys. Rev. E* 113, 044128
  (2026), derive exact arbitrary SFF moments and exponential/log-normal laws
  under rational-independence/factorization premises, while describing
  independence proofs as mathematically daunting:
  <https://arxiv.org/abs/2505.05199>.
- `[LITERATURE]` Szymański's 2024 quantum-many-body reachability talk asks
  explicitly whether generic two-body Hamiltonians have rationally
  independent eigenenergies and whether every two-body Hamiltonian contains
  hidden resonances:
  <https://quantumstat.es/talks/29aug2024/>.
- `[LITERATURE — CLOSE PARENT]` Huang, *Extensive entropy from unitary
  evolution* (2021), proves that nondegenerate gaps hold almost everywhere
  in broad nearest-neighbour local-Hamiltonian ensembles:
  <https://arxiv.org/abs/2104.02053>. This settles the order-two no-resonance
  layer for those ensembles. The proposed generator theorem must therefore
  be presented strictly as an all-orders/projective-rank advance, never as
  the first generic local nonresonance theorem.
- `[LITERATURE]` Campos Venuti, *The recurrence time in quantum mechanics*
  (2015), obtains double-exponential generic recurrence estimates under
  rational independence and a Gaussian approximation:
  <https://arxiv.org/abs/1509.04352>.
- `[LITERATURE]` Kotowski--Oszmaniec (2026) give deterministic recurrence
  upper bounds in Hilbert-space dimension, complementary to the exact
  generic completed distribution here:
  <https://arxiv.org/abs/2601.10409>.
- `[LITERATURE]` Generic rational independence is known in continuum
  Schrödinger families, for example Poláčik--Valdebenito (2019). This is a
  parent-theory warning: generic nonresonance itself is not new. Exact
  priority for finite tensor-local Hamiltonian spaces remains open.

## Hostile falsity and rediscovery audit

1. **Classical-core attack.** `(2)`--`(4)` follow routinely from spectral
   factorization and Kronecker--Weyl once `(1)` is known.
   **Verdict:** `[BRIDGE]`, not novelty.
2. **Random-matrix attack.** Absolutely continuous full random matrices have
   rationally independent spectra almost surely.
   **Verdict:** does not settle polynomial-parameter local Hamiltonian
   spaces, but forbids claiming generic independence as a new general idea.
3. **Free-model attack.** Rationally independent one-particle free spectra
   still produce factorized many-body collisions and log-normal SFF laws.
   **Verdict:** absorbed rather than contradicted by `(4)`; factorization,
   not local level statistics, is the invariant.
4. **Weak-coupling attack.** An arbitrarily small link cannot change
   finite-horizon observations discontinuously.
   **Verdict:** rank changes only in the completed limit; `(10)` and the
   existing finite-horizon stability theorem must be stated together.
5. **Symmetry attack.** Translation-invariant, conserved-charge and
   integrable subfamilies may lie entirely in the exceptional set.
   **Verdict:** genericity is in the full allowed inhomogeneous coefficient
   space or within a separately proved symmetry sector. No claim about all
   named physical models is authorized.
6. **Topology-overclaim attack.** A single full-system recurrence law sees
   connected components, not every internal edge.
   **Verdict:** full graph reconstruction requires induced-subsystem
   recurrence data; it is a corollary with extra interventions, not the
   master claim.
7. **Infinite-system attack.** Infinite-volume dynamics can have continuous
   spectrum and no global recurrence.
   **Verdict:** the countable extension is only simultaneous finite-volume
   exhaustion. It does not assert infinite-volume recurrence.
8. **Assembly attack.** Factorization of ordinary scalar SFF moments is
   expected from independent subsystems and is not a discovery.
   **Verdict:** scalar factorization is demoted to a corollary. The candidate
   contribution is the resolved collision theorem `(5)`: every two-copy
   collision class is a Boolean cube whose dimension is exactly component
   Hamming distance. Exact priority remains under audit.
9. **Huang-parent attack.** Generic local nondegenerate gaps were already
   proved for substantial nearest-neighbour ensembles in 2021.
   **Verdict:** any order-two genericity claim is prior art. Surviving
   generator novelty must be maximal projective rank—simultaneous absence of
   nontrivial balanced relations at every replica order—and its exact
   recurrence consequences.
10. **All-order rearrangement-parent attack.** Riddell--Bertini already use
    componentwise replica rearrangements at every order; Campos
    Venuti--Odavić--Hamma already give exact multinomial and product moment
    laws. **Verdict:** the new arbitrary-alphabet product theorem and its
    logarithm are not a Nature-level discovery alone. Surviving synthesis
    novelty must be inverse: the pair-resolved recurrence symmetry algebra
    must reconstruct the finest additive interaction blocks.

**Current verdict:** `FORWARD SYNTHESIS FAILS; INVERSE LAW PROVED;
RELATION-LATTICE SYNTHESIS OPEN`. The Boolean inverse theorem is now proved
on paper and in Lean. It is not promoted alone because rectangle
separability and interaction-grouping parent theories may absorb much of its
mathematical novelty. The stronger candidate is now one relation-lattice
law: the completed phase ensemble, all resolved replica layers and the
projective arithmetic constraint lattice are equivalent invariants; the
controlled order-two sector reconstructs the unique additive interaction
partition. See `recurrence-relation-lattice-universal-law.md`. Exact
priority and the generic local-generator capstone remain open.

## Open cores

1. `[CLOSED ON PAPER]` Disconnected genericity now uses componentwise
   symmetric relation polynomials and a rationally transverse witness.
2. `[CLOSED ON PAPER]` Hypergraph locality now contains a two-section
   spanning-forest witness under the explicit support-contained convention.
3. `[CLOSED ON PAPER]` The tensor phase-torus embedding,
   Kronecker--Weyl law and component-histogram equivalence are proved in
   `../2-fully-proven/component-recurrence-torus-and-replica-factorization-law.md`.
4. `[CLOSED ON PAPER FOR FIXED COMPONENT COUNT]` Equations `(7)`--`(8)` and
   the product-exponential limit are proved for fixed component count. A
   growing-component log-normal limit is not required by the master theorem
   and must not be claimed without a separate proof.
5. `[CLOSED ON PAPER]` Equation `(10)` with unit constant and fixed-order
   one-knob uniformity is proved in
   `../2-fully-proven/finite-window-replica-collision-resolution-law.md`.
6. `[CLOSED ON PAPER AND IN LEAN]` The order-two equal-energy class is a
   Boolean cube and has cardinality \(2^{d_H}\), proved in
   `../2-fully-proven/replica-collision-hamming-tomography-law.md`.
7. `[CLOSED ON PAPER AND IN LEAN; PRIOR ART LIMIT]` The all-order
   replica-history collision class is a Cartesian product of component
   arrangement spaces; its logarithmic cardinality is additive and gives a
   universal floor without independence. Formalized in
   `replica-history-factorization-law.md`. Riddell--Bertini and Campos
   Venuti--Odavić--Hamma prevent using the forward product law as headline
   novelty.
8. `[CLOSED ON PAPER AND IN LEAN]` Universal partial-swap recurrence is
   exactly additive cut separability; the valid masks form a Boolean
   algebra whose atoms partition the supplied sites and are recovered by
   pair-resolved completed-time kernels. Do not claim recovery of tensor
   factorization or emergent space.
9. `[OPEN CORE]` Complete exact-object citation ancestry/descendancy search,
   including quantum control generic nonresonance and local spectral Galois
   literature, plus collision-class/Hamming tomography.
10. `[OPEN CORE]` Formalize the arbitrary-graph generator theorem and every
    retained recurrence corollary before manuscript use.
11. `[CLOSED ON PAPER AND IN LEAN; PRIORITY OPEN]` Every finite spectrum has
    a unique completed phase ensemble with Fourier transform equal to the
    indicator of its integer relation lattice. Replica order is exactly
    arithmetic height, and the full resolved hierarchy reconstructs the
    projective relation lattice.

## Lean status

`[CORPUS]` Existing unconditional modules already prove:

- finite-spectrum all-order time-average equals replica collision mass;
- all-order collision-floor equality iff maximal projective energy;
- component-factorized equal-energy collisions are exactly equal component
  histograms, and the completed weighted moment is their collision mass;
- every order-two equal-energy collision class of a mutually independent
  component spectrum is a Boolean cube of cardinality \(2^{d_H}\);
- normalized finite-window error is at most
  \(\min(1,(T\delta_m)^{-1})\) with unit constant;
- every finite rationally independent phase flow converges weakly to
  normalized Haar measure, hence every continuous phase statistic has its
  Haar completed-time average;
- every finite-order equal-energy history class is the Cartesian product of
  component arrangement spaces under projective independence, with a
  universal product-cardinality and logarithmic-entropy floor for every
  additive spectrum;
- every finite spectrum has a unique completed phase ensemble whose Fourier
  transform is the exact indicator of its full integer relation lattice;
- the completed phase ensemble and full relation lattice determine each
  other;
- resolved replica order `n` detects exactly projective relations of
  positive coefficient mass at most `n`, and all orders reconstruct the
  projective relation lattice;
- universally recurrence-preserving partial-swap masks form a Boolean
  algebra whose atoms are the unique additive interaction blocks relative
  to supplied coordinates;
- the local second-order residue, pole separation and endpoint-response
  lemmas needed by the connected graph induction;
- abstract one-knob polynomial avoidance.

No Lean theorem yet proves `(1)` for arbitrary local graphs. The collision
law `(4)`, Hamming law `(5)`, finite-window certificate `(10)`, and
full-phase Haar law are formalized. The generic-local manuscript claim
remains unauthorized until the generator capstone passes the axiom and lint
gates.

## Nature gate

Nature requires original research, outstanding scientific importance,
interdisciplinary interest, an arresting result, and immediate plus
far-reaching implications. This route can plausibly satisfy those criteria
only if the finished paper:

1. leads with the answered hidden-resonance question;
2. presents one recurrence-factorization law rather than several adjacent
   theorems;
3. demonstrates exact consequences for equilibration, SFF plateaus and
   finite-order experiments;
4. distinguishes completed-time singularity from laboratory crossover;
5. avoids unsupported claims about gravity, black holes, thermodynamic
   recurrence or all symmetry-constrained models;
6. survives independent mathematical-physics priority and proof review.

## Gates

- [x] 0 → 1: exact falsifiable law, internal parents, external question,
  hostile preliminary attack
- [ ] 1 → 2: all open cores closed; complete dependency-closed paper proof
- [ ] 2 → 3: exact unconditional Lean capstones; target checks, axiom audit
  and lint pass
- [ ] 3 → 4: coherent Nature-format manuscript and hostile editorial review

## Log

- 2026-07-30 — created as replacement master after rejecting
  spacetime-ontology overreach and the nearest-neighbour-only recurrence
  framing.
