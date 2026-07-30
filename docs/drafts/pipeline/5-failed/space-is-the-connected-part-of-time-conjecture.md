# Space is the connected part of time

- **ID:** `space-is-the-connected-part-of-time`
- **Stage:** 5-failed
- **Type:** FALSIFIED; EXACT PARTITION-CURVATURE SURVIVOR
- **Statement:** Physical space is the irreducible nonfactorization geometry of
  observer-completed time; coordinate time is only a one-dimensional path
  through that generally higher-dimensional object.

## Conjecture discipline

This file freezes the truth-hunch before proof search. The conjecture is not
licensed by current Lean machinery, by a route already visible in the
literature, or by knowing how to prove it. It is allowed to fail. It is not
allowed to shrink merely because a nearby theorem is easier.

## The Einstein-style reversal

Standard kinematics begins with a spacetime and asks how states evolve in it.
Reverse that order:

> **There is no independently supplied space through which a system evolves.
> There is an observer-relative completed space of distinguishable histories.
> The connected, nonfactorizing structure of that time object is what appears
> as physical space.**

The one-dimensional variable displayed by a clock is not the whole of time.
It is a coordinate path through completed time, just as one worldline is not
the whole of spacetime.

Public-language version:

> **Space is the connected part of time. You do not pass along all of time;
> every clock traces one path through a larger space of possible
> distinctions.**

## Fundamental object

For each operational observer family \(\mathcal O\) and each physical region
or subsystem \(S\), let
\[
  \mathbb T_{\mathcal O}(S)
\]
be the completion of histories after identifying exactly those histories
that \(\mathcal O\) cannot distinguish. Inclusions of regions and refinements
of observers induce restriction or quotient maps. The complete assignment
\[
  (S,\mathcal O)\longmapsto\mathbb T_{\mathcal O}(S)
\]
is the **completed-time atlas**.

The atlas, not a background manifold and not a preferred external parameter,
is conjectured to be the primitive kinematic object.

For disjoint systems with no physical relation, completed time factorizes.
Interaction, common constraints and causal identification obstruct that
factorization. Let
\[
  \Delta_{\mathcal O}(A,B)
  :=
  \mathbb T_{\mathcal O}(A\cup B)
  \big/
  \bigl(\mathbb T_{\mathcal O}(A)\times
        \mathbb T_{\mathcal O}(B)\bigr)
\]
denote this symbolically; the exact construction may require a fibre,
cofiber, kernel, cokernel or derived obstruction in the eventual category.
The choice is part of the research problem and must be forced by operational
universality, not selected to make the conjecture true.

## Universal law

> **History–geometry duality.** The minimal physical spatial/causal geometry
> is uniquely reconstructible, up to operational gauge, from the complete
> hierarchy of nonfactorization obstructions of the completed-time atlas.
> Conversely, that geometry determines how completed time composes.

Thus:

- time is completed distinguishability;
- space is the connected obstruction to temporal factorization;
- interaction creates joint directions of time;
- recurrence is return geometry inside completed time;
- a horizon is an observer quotient that removes temporal directions and
  their connected obstructions;
- an external clock is only a chart and cannot be fundamental.

This is one proposed law, not six analogies. If these statements require
independent structures to be inserted by hand, the conjecture fails.

## Rank shadow: temporal cumulants

Whenever completed time has an intrinsic dimension, define
\[
  \tau_{\mathcal O}(S):=\dim\mathbb T_{\mathcal O}(S).
\]
For every finite nonempty subsystem \(S\), define its connected temporal
cumulant by Möbius inversion:
\[
  K_{\mathcal O}(S)
  :=
  \sum_{A\subseteq S}
  (-1)^{|S|-|A|}\tau_{\mathcal O}(A),
  \qquad \tau_{\mathcal O}(\varnothing)=0.
\]

Frozen prediction:

> **A subsystem is an irreducible connected spatial cell exactly when its
> conditional temporal cumulant is nonzero.**

Pair curvature is only the second cumulant. The entire hierarchy is required:
it must separate direct interaction, mediation, common cause and genuine
higher-body locality without receiving the interaction graph as input.

For finite generic local quantum systems, the conjecture predicts that the
support of \(K\) recovers every connected induced subsystem and that the
second cumulants recover the interaction graph. Higher cumulants then measure
connected spatial organization that no pairwise statistic records.

## Risky consequences frozen before proof

1. **Clock relativity.** Two observers using one-dimensional clocks can have
   completed times of different intrinsic dimension without either clock
   being defective.
2. **Weak-interaction birth of space.** An arbitrarily weak but nonzero generic
   coupling can create new temporal directions and a new connected spatial
   relation, while the scale needed to resolve them diverges as coupling
   vanishes.
3. **Timeless global states.** A globally stationary constrained state can
   contain nontrivial internal completed time because conditional
   distinguishability, not external parameter motion, is primitive.
4. **Locality from histories.** A local interaction net or its operational
   causal nerve can be recovered from the temporal atlas without coordinates,
   distances or adjacency being supplied first.
5. **Horizon rank loss.** Exterior and infalling observers can possess
   different temporal dimensions because the exterior atlas is a proper
   quotient. Any entropy claim requires a unique regulator-independent fibre
   capacity and an area law; until those are derived, no black-hole entropy
   statement belongs in a paper.
6. **Continuum survival.** In infinite systems, rank may diverge, but the full
   factorization-obstruction atlas remains meaningful and reconstructs
   locality through finite-region restrictions or an appropriate
   operator-algebraic limit.
7. **Metric emergence.** Spatial topology comes from which temporal
   cumulants exist; operational distance comes from the smallest
   observation/return scale at which those cumulants become resolvable.

## What would make this a discovery rather than a definition

The completed-time atlas must be defined only from observable history
equivalence. No graph, tensor locality, manifold or causal order may enter
its definition. A successful theorem must then reconstruct one of those
structures uniquely from the atlas.

The decisive finite theorem would state, for every finite interaction graph
and every assignment of finite local dimensions, that one generic
history-derived temporal atlas simultaneously recovers:

1. component structure from temporal dimensions;
2. adjacency from second temporal cumulants;
3. all connected induced subsystems from the full cumulant support;
4. recurrence dimension and return density from the same atlas;
5. the infinite-network limit from compatible finite restrictions.

The decisive physical extension would reconstruct a local
operator-algebraic net or causal nerve from history data alone and produce a
prediction not equivalent to spectral nonresonance.

## Hard falsifiers

Retire the universal law if any survives serious repair:

1. completed history equivalence is not canonical or not compositional;
2. the atlas cannot distinguish direct locality from mediated correlation;
3. inequivalent spatial/causal structures have identical complete atlases;
4. reconstruction requires supplying the target graph or tensor
   factorization in advance;
5. temporal cumulants are merely a renamed connected-correlation expansion
   with no new theorem or prediction;
6. the continuum atlas has no regulator-independent limit;
7. horizon quotients cannot be defined operationally;
8. existing literature already contains the same history-derived
   reconstruction law;
9. the only provable result is generic finite spectral rank;
10. no experimentally discriminating consequence follows from the ontology.

## Research order

1. Keep the universal conjecture frozen while proving or killing its finite
   temporal-cumulant shadow.
2. Prove the exact combinatorial support theorem for all subsystem cumulants,
   not only pairs.
3. Formalize that theorem unconditionally.
4. Audit whether the temporal atlas is independent of a supplied tensor
   factorization; if not, state precisely what has and has not been
   reconstructed.
5. Search external literature for the exact obstruction-functor and
   Möbius-reconstruction law.
6. Seek the operator-algebraic continuum version.
7. Derive a discriminating physical prediction.
8. Admit no ontology sentence to the manuscript unless its mathematical
   content has an unconditional formal theorem.

## Log

- 2026-07-30 — Frozen as a deliberately proof-route-independent
  reinterpretation. It strengthens “space is positive temporal curvature”:
  pair curvature is only a decategorified second-order shadow of a complete
  history–geometry duality.

## First antagonistic attack — scalar cumulants fail

The frozen scalar prediction

> \(K(S)\ne0\) exactly when \(G[S]\) is connected

is false.

Take four two-level sites whose interaction graph is \(K_4\) with one edge
removed. The full graph and all four induced three-vertex graphs are
connected; five pairs are connected and one pair is disconnected. Under the
generic temporal-rank law,
\[
  \tau(S)=
  \sum_{C\in\pi_0(G[S])}(2^{|C|}-1).
\]
Therefore the fourth Möbius cumulant is
\[
  15-4\cdot7+(5\cdot3+2)-4\cdot1=0.
\]
Connected temporal structure can cancel under scalar inclusion--exclusion.
No manuscript may claim that ordinary temporal cumulant support reconstructs
all connected induced subsystems.

This kills the scalar rank shadow, not history--geometry duality. It exposes
the correct survivor: factorization is partition-valued, not cumulant-valued.

## Positive survivor — temporal factorization lattice

For every nonempty finite subsystem \(S\) and every set partition
\(\Pi\) of \(S\), define partition curvature
\[
  \mathcal K_\Pi(S)
  :=
  \tau(S)-\sum_{B\in\Pi}\tau(B).
\]

For the finite generic local quantum law, the exact conjectured survivor is
\[
  \mathcal K_\Pi(S)\ge0,
  \tag{F1}
\]
with
\[
  \mathcal K_\Pi(S)=0
  \quad\Longleftrightarrow\quad
  \text{every connected component of \(G[S]\) lies inside one block of
  \(\Pi\)}.
  \tag{F2}
\]

Thus zero-curvature partitions are exactly the partitions across which
intrinsic completed time factorizes. A subsystem is connected exactly when
every nontrivial partition has strictly positive temporal curvature.
Adjacency is recovered by applying this statement to two-site subsystems.

Unlike one Möbius number, the complete zero-partition lattice cannot suffer
inclusion--exclusion cancellation. It is the finite rank shadow of the
categorical nonfactorization atlas in the universal conjecture.

### Paper proof of the survivor

Let \(C\) be one connected component of \(G[S]\). Intersect the blocks of
\(\Pi\) with \(C\), then refine each intersection into its induced connected
components \(F_1,\ldots,F_m\). Every component contributing to a block rank
is exactly one such \(F_j\). Put
\[
  d_j:=\prod_{v\in F_j}q_v\ge2.
\]
The contribution of \(C\) to the block-rank sum is
\[
  \sum_{j=1}^m(d_j-1),
\]
whereas its contribution to \(\tau(S)\) is
\[
  \prod_{j=1}^m d_j-1.
\]
For integers \(d_j\ge2\),
\[
  \prod_{j=1}^m d_j-1
  \ge
  \sum_{j=1}^m(d_j-1),
\]
with equality exactly when \(m=1\). Summing over \(C\) proves `(F1)`.
Moreover \(m=1\) exactly when all vertices of \(C\) occur in one block of
\(\Pi\), proving `(F2)`.

Status: dependency-closed on paper conditional only on the existing generic
arbitrary-graph temporal-rank theorem; not yet formalized as a Lean
capstone.

- 2026-07-30 — First attack killed Möbius-support reconstruction. Extracted
  exact partition-factorization survivor `(F1)`--`(F2)`. Universal ontology
  remains a conjecture; its finite rank shadow became sharper and less
  arbitrary.

## Second antagonistic attack — history-only reconstruction is circular

The universal ontology is retired.

If the input assignment
\[
  S\longmapsto\mathbb T_{\mathcal O}(S)
\]
is indexed by declared physical subsystems or regions, then the proposed
reconstruction has already been given the decomposition whose spatial
meaning it claims to derive. The finite partition theorem validly recovers
an interaction graph relative to that supplied decomposition, but it does
not derive space itself.

If subsystem and region labels are removed, the conjecture becomes the
already-retired future-factorization reconstruction route. Three exact
obstructions apply:

1. complete labelled operational histories determine at most a simultaneous
   similarity class; transforming every state, operation and reporter by one
   realization change leaves all finite reports invariant;
2. temporal-character data discard static operational probabilities, so a
   trivial temporal atlas can represent operationally inequivalent devices;
3. tensor-product and locality assignments are not uniquely selected by
   Hamiltonian or temporal data without an independent composition anchor.

Consequently no history-only invariant can both quotient presentation gauge
and uniquely select physical spatial factorization in the stated
generality.

### No-go closure

- **Exact killing mechanism:** supplied subsystem labels make spatial
  reconstruction circular; removing them leaves presentation and
  factorization gauge.
- **Strongest positive survivor:** relative to a supplied finite subsystem
  decomposition, the complete zero-partition curvature lattice exactly
  recovers which partitions separate connected interaction components.
  This is theorem `(F1)`--`(F2)`, not emergent spacetime.
- **New insight:** temporal succession and independent coexistence are
  logically independent operational structures. Perfect temporal knowledge
  cannot manufacture the missing notion of independent composition.
- **Prior internal no-gos:** `operational-history-reconstruction-conjecture`
  and `future-factorization-spectrum-conjecture`.
- **External boundary:** gate-set tomography retains similarity gauge, while
  Hamiltonian-only tensor-factor reconstruction admits infinitely many
  structures. The present route does not outrun those results.
- **Status:** universal ontology falsified; finite partition-curvature
  survivor dependency-closed on paper and awaiting Lean capstone.

- 2026-07-30 — Retired rather than weakened. “Space is the connected part of
  time” is unauthorized as a scientific claim. The exact surviving statement
  concerns interaction connectivity after a subsystem decomposition is
  supplied.
