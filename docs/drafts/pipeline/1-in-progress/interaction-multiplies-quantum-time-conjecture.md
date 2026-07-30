# Interaction multiplies quantum time

- **ID:** `interaction-multiplies-quantum-time-conjecture`
- **Stage:** 1-in-progress
- **Type:** FROZEN UNIVERSAL-LAW CONJECTURE / QUANTUM MANY-BODY DYNAMICS /
  RECURRENCE / INTERACTION TOPOLOGY
- **Freeze date:** 2026-07-30
- **Scientific status:** `[CONJECTURE] [PROOF ROUTE NOT PART OF FREEZE]`
  `[PRIORITY UNAUDITED]`
- **Origin:** abductive jump from generic local relation erasure, projective
  recurrence rank, observer temporal dimension, and the failure of passive
  spectral data to reconstruct spatial geometry.

Novelty is measured only against external literature. Corpus results are
evidence and possible proof machinery, never priority evidence.

## Frozen public law

> **When two quantum worlds interact, time does not add—it multiplies.**

Here “dimensions of time” means the independently variable relative phases in
the minimal completed recurrence dynamics. It does not mean extra coordinate
directions in spacetime.

## Frozen exact conjecture

Let \(G=(V,E)\) be any finite undirected interaction graph. Give each vertex
\(v\) a finite Hilbert space \(\mathcal H_v\) of arbitrary dimension
\(q_v\ge2\). Let \(\mathcal L_G\) be the full real vector space of Hermitian
Hamiltonians consisting of arbitrary one-vertex terms and arbitrary two-vertex
terms on the edges of \(G\). For a Hamiltonian \(H\) with eigenvalues
\(\lambda_1,\ldots,\lambda_D\), define its projective temporal dimension by
\[
 \tau(H)
 =
 \dim_{\mathbb Q}
 \operatorname{span}_{\mathbb Q}
 \{\lambda_j-\lambda_1:2\le j\le D\}.
 \tag{1}
\]

For each connected component \(C\) of \(G\), put
\[
 D_C=\prod_{v\in C}q_v.
\]

The conjecture is:
\[
 \boxed{\quad
 \tau(H)=\sum_{C\in\pi_0(G)}(D_C-1)
 \quad}
 \tag{2}
\]
for a dense, full-measure \(G_\delta\) subset of \(\mathcal L_G\). Equivalently,
componentwise additive decomposition supplies every universal rational
spectral relation, and generic local interaction supplies no others.

For connected \(G\), `(2)` becomes
\[
 \tau(H)=\prod_{v\in V}q_v-1,
 \tag{3}
\]
the largest value permitted by the total Hilbert-space dimension.

If one edge joins two previously disconnected components \(A\) and \(B\), then
the generic temporal-dimension jump is exactly
\[
 \Delta\tau
 =
 (D_A-1)(D_B-1).
 \tag{4}
\]
The edge strength may be arbitrarily small but nonzero. Equation `(4)`, not a
metaphor, is the proposed multiplication law.

The recurrence consequence is part of the same conjecture. For every connected
component with maximal projective rank, positive-time exact global return is
absent, while approximate return remains. For a connected total system and
\(0<\varepsilon<2\), the asymptotic density of operator-norm
\(\varepsilon\)-returns is
\[
 \left(
   \frac{2\arcsin(\varepsilon/2)}{\pi}
 \right)^{D-1}.
 \tag{5}
\]

No clause may enter a manuscript until it has a dependency-closed paper proof,
an unconditional formal proof, and an external priority audit.

## Infinite form frozen with the finite law

For every countably infinite, locally finite connected graph with
\(q_v\ge2\), consider any exhaustion by finite connected vertex sets. The
finite-volume temporal dimensions predicted by `(3)` diverge without bound.
The stronger infinite conjecture is that a residual, product-measure-one set
of infinite local coupling assignments makes every member of a fixed
countable exhaustion maximally projective simultaneously. Thus no fixed
finite-dimensional compact phase carrier can realize all exact finite-volume
futures of a generic infinite interacting system.

This is an inverse-limit statement about all finite volumes. It is not a claim
that an infinite-volume Hamiltonian has a trace, a finite list of eigenvalues,
or a global recurrence time.

## Einstein-level reinterpretation

The proposed category change is:
\[
\text{interaction as motion occurring during time}
\quad\longrightarrow\quad
\text{interaction as the operation that creates independent quantum time}.
\]

Disconnected composition adds temporal dimensions. Connecting composition
creates the cross term `(4)`. The basic compositional distinction between
“beside” and “interacting” is therefore visible in the arithmetic geometry of
completed time itself.

This law would explain one fact with one invariant:

- uncoupled many-body spectra are exactly compressible into component phases;
- local interaction erases componentwise compression;
- exact recurrence disappears generically although approximate recurrence
  survives;
- recurrence rarity becomes exponential in Hilbert dimension and therefore
  double-exponential in maximum entropy;
- finite observation can remain continuous as an arbitrarily weak edge causes
  an exact completed-time rank jump;
- infinite connected systems require unbounded temporal phase dimension
  across finite volumes.

## Hard falsifiers

The conjecture dies or must be narrowed if any of the following occurs:

1. a finite connected graph and local dimensions force a nontrace rational
   relation for every allowed local Hamiltonian;
2. a connected graph lacks even one local Hamiltonian with maximal projective
   rank;
3. disconnected components possess a generic cross-component relation beyond
   the componentwise additive structure;
4. the exceptional set is not null and meagre in the declared physical
   parameter space;
5. an external theorem already proves `(2)` or a strictly stronger
   tensor-local result;
6. recurrence density `(5)` fails under the stated operator-norm target;
7. the simultaneous infinite-exhaustion statement fails under every natural
   product measure or Baire topology.

## Hostile significance gate

Even if `(2)`--`(5)` are true and new, a general scientific journal can still
reject the work if:

1. “temporal dimension” is only a relabelled rational spectral rank;
2. the theorem has no finite-system experimental discriminator;
3. exact genericity is physically invisible at every attainable horizon;
4. arbitrary local terms make the ensemble too broad for many-body physics;
5. a graph theorem is advertised as quantum gravity, cosmology, or black-hole
   physics without a derived model;
6. the result does not change a calculation, expectation, or inference used by
   the broader community.

The paper therefore needs, from the same law rather than an attached collage:

- a finite-horizon activation or minimax consequence;
- an explicit small-network protocol distinguishing additive from
  multiplicative temporal composition;
- a comparison with locality, controllability, spectral nonresonance,
  equilibration, and recurrence literature;
- a clear answer to: **Can a finite interacting quantum world repeat
  exactly?**

## Research log

- 2026-07-30 — conjecture frozen before literature attack and proof
  engineering. Path-specific results motivated the jump but do not establish
  arbitrary graphs, arbitrary local dimensions, disconnected classification,
  edge fusion, or the simultaneous infinite-volume statement.

## First external priority attack — 2026-07-30

No exact collision was found in the first primary-source search. This is not a
completed priority audit.

Closest occupied results:

1. **Generic unrestricted matrices.** Riddell, Pagliaroli and Alhambra,
   *Concentration of quantum equilibration and an estimate of the recurrence
   time* (SciPost Physics 15, 165, 2023), prove that nongeneric spectra form a
   null subset of the full \(D\times D\) Hermitian space and use an all-order
   no-collision condition for equilibration and recurrence estimates. Their
   parameter space has \(D^2\) independent real directions. It does not prove
   maximal projective rank inside a polynomial-parameter tensor-local family.
2. **Free local models.** Riddell and Bertini, *Rationally independent free
   fermions with local hopping* (Physical Review E 110, 064101, 2024),
   construct rationally independent single-particle energies using local
   hopping and show that the many-body replica spectrum retains free-mode
   collisions. This is a direct conceptual parent and a sharp contrast: its
   independent rank is mode-linear, not \(D-1\).
3. **Local spectral assumptions.** Equilibration and localization literature
   commonly assumes nondegenerate gaps or stronger finite-order
   nonresonance. Such assumptions are consequences of `(2)` but do not prove
   it for a local family.
4. **Sparse symmetric matrices.** Pavlov, *Logarithmically sparse symmetric
   matrices* (Beiträge zur Algebra und Geometrie 65, 907--922, 2024), studies
   \(\mathbb Q\)-independence of generic eigenvalue functions for
   graph-sparse matrix spaces. Those spaces independently control all \(D\)
   diagonal entries. A tensor-local \(n\)-site family has \(D=\prod_vq_v\)
   levels but only polynomially many controls and cannot independently set
   computational-basis energies.
5. **Locality from spectra.** Cotler, Penington and Ranard, *Locality from the
   spectrum* (Communications in Mathematical Physics 368, 1267--1296, 2019),
   study whether a generic local Hamiltonian is determined by its spectrum.
   They use finite-size generic simplicity and explicitly warn that
   finite-size genericity need not pass naively to infinite systems. They do
   not establish all-order rational spectral independence.
6. **Exact driven recurrence.** Ruck, Cichy, Novakovic and Saha, *Quantum
   recurrences and the arithmetic of Floquet dynamics* (Quantum 10, 2074,
   2026), classify possible exact state-independent recurrence times in a
   broad selected Floquet family using cyclotomic arithmetic. This occupies
   model-specific exact-return classification, not the graph-universal
   local-Hamiltonian genericity law `(2)`.
7. **Many-body spectral density.** Keating, Linden and Wells, *Spectra and
   eigenstates of spin chain Hamiltonians* (Communications in Mathematical
   Physics 338, 81--102, 2015), prove Gaussian limiting density of states for
   broad local chains and discuss generic simple spectrum. Limiting density
   and order-zero simplicity do not exclude arbitrary rational affine
   relations.

Provisional novelty residue:
\[
\text{full exponential projective rank}
\quad+\quad
\text{arbitrary finite interaction graph and site dimensions}
\quad+\quad
\text{exact component/fusion law}.
\]

Required searches still include spectral Galois theory of tensor-local
Hamiltonians, quantum-control nonresonance, graph-local analytic pencils,
generic gap claims in mathematical statistical mechanics, and work citing the
2024 free-fermion paper.

## First truth attack — reduction obligations

The conjecture is not licensed by a path theorem alone. A proof must close all
of the following without changing the frozen statement:

1. **All-vertex endpoint induction.** A tree witness must retain a connected,
   non-bipartite observable transition graph at every old vertex while
   creating one at each newly attached leaf.
2. **Heterogeneous dimensions.** The induction must accept an arbitrary new
   local dimension \(q_v\), including the qubit non-bipartiteness obstruction,
   rather than using one common \(q\).
3. **Arbitrary connected graph.** Every connected graph must reduce to a
   spanning-tree witness, after which extra allowed edges cannot create a
   universal relation.
4. **Disconnected upper bound.** Kronecker-sum decomposition must prove that
   every spectrum has rank at most
   \(\sum_C(D_C-1)\).
5. **Disconnected sharpness.** Component spectra must be made mutually
   rationally transverse inside the same local parameter space; this cannot be
   asserted from separate component genericity.
6. **Small-edge density.** Maximal rank must occur in every neighborhood of
   the zero connecting edge, not merely at one uncontrolled interaction
   strength.
7. **One global genericity theorem.** Countably many rational relations and
   the discriminant must be excluded by proper polynomial or real-analytic
   zero sets in the physical Hermitian parameter space.
8. **Infinite product statement.** Product-measure-one and residual
   simultaneous finite-volume maximality must be proved from countable
   cylinder events; no infinite-volume trace or eigenvalue list may be used.

The current formal endpoint lemma uses a directed probe in a bilinear
eigenvector expression. It is not yet a physical Hermitian bra--ket
transition theorem. The all-vertex induction remains open until a
sesquilinear or real-symmetric bridge is proved.
