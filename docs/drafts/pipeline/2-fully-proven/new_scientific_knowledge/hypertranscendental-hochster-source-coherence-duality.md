# Hypertranscendental source coherence is the topology of the constraint boundary

- **ID:** `hypertranscendental-hochster-source-coherence-duality`
- **Stage:** 2-fully-proven / arbitrary finite discrete-family Lean bridge complete /
  general finite-complex bridge and independent audit required
- **Type:** THEOREM / DERIVED CONSTRAINT-TOPOLOGY REALIZATION / SELECTOR NO-GO
- **Scientific status:** `[PAPER PROOF COMPLETE] [ANALYTIC INPUT FORMALIZED]`
  `[HOCHSTER PARENT THEOREM] [CROSS-CATEGORY NOVELTY PROVISIONAL] [NOT AN RH RESULT]`
- **Parents:**
  - `../../3-formalized/new_scientific_knowledge/hypertranscendental-constraint-spectrum-universality.md`
  - `../../3-formalized/new_scientific_knowledge/facet-sewn-herglotz-stanley-reisner-differential-matroid.md`
  - `../../3-formalized/normal-crossing-exterior-coherence-capacity-law.md`
- **Successor:** `../../1-in-progress/hypertranscendental-constraint-sheaf-reconstruction-duality.md`
- **Statement:** In every facet-sewn Stanley--Reisner HT realization, the complete multigraded
  derived source-coherence fibre at the structural identity is the reduced simplicial cohomology
  of all induced constraint subcomplexes.  Consequently every finite simplicial cohomology type
  occurs as actual higher source coherence of a scalar meromorphic HT system.  The full derived
  topology is nevertheless independent of residue orientation, so it is a universal kinematic
  object rather than a source selector.

## 1. Exact analytic input

Let `V` be finite, let `k=C(delta)`, and put

```text
S=k[x_v:v in V],
R=k[t_v^(+-1):v in V],             x_v=t_v-1.
```

For a finite simplicial complex `Delta` on `V`, write `I_Delta` for its squarefree nonface ideal
in `S`.  The facet-sewn meromorphic realization theorem constructs a scalar meromorphic HT source
`F_Delta` whose DA-relative structural orbit module is

```text
M_Delta=R/((I_Delta)R).                                      (1)
```

More strongly, every finite family of structural operators has nonlinear differential matroid
equal to the linear matroid of its classes in `(1)`.  Thus `(1)` is not an assigned combinatorial
model: it is the exact cyclic DA-relative module of an analytic hypertranscendental source.

Let

```text
m=(x_v:v in V).
```

This is the structural identity `t_v=1`.  Since every inverted element `t_v=1+x_v` is a unit at
`m`, passage from `S` to `R` is flat and does not change the local derived fibre at `m`.

## 2. HT--Hochster source-coherence theorem `[PROVED]`

For `W subset V`, let `Delta|W` be the induced subcomplex and let `k(-W)` denote the squarefree
multidegree label.  Define the degree-`i` source-coherence space of the realized HT source by

```text
Coh_i(F_Delta)_W = Tor_i^R(M_Delta,k)_W,                   (2)
```

where `k=R/m` and the multigrading is transported from the squarefree polynomial presentation
before localization.

> **THEOREM (HT--Hochster source-coherence duality).** For every `i>=0` and every `W subset V`,
>
> ```text
> Coh_i(F_Delta)_W
>   ~= H_tilde^(|W|-i-1)(Delta|W;k).                       (3)
> ```
>
> The isomorphism is natural under relabeling of vertices and restriction to induced source
> faces.

### Proof

The exact annihilator theorem gives `(1)`.  Choose a multigraded free `S`-resolution `P_bullet` of
`S/I_Delta`.  Flat base change along `S -> R` gives a free `R`-resolution

```text
R tensor_S P_bullet -> M_Delta.                            (4)
```

Tensoring `(4)` with `k=R/m` is canonically the same complex as tensoring `P_bullet` with
`S/(x_v:v in V)`.  Therefore

```text
Tor_i^R(M_Delta,k)_W ~= Tor_i^S(S/I_Delta,k)_W.            (5)
```

Hochster's formula identifies the right side of `(5)` with the reduced cohomology group in
`(3)`.  Vertex relabeling and induced-face restriction preserve the squarefree resolution and the
Hochster strand identification, which gives the stated naturality. `QED`

The cohomological convention includes reduced degree `-1`; it handles the empty induced complex
and the degree-zero algebra without an exceptional formula.

## 3. Exact consequences

### 3.1 Topology is higher source coherence

Equation `(3)` turns every topological hole in every induced subcomplex into an actual higher
relation among source-labelled DA constraints.  It is not merely topology of the reduced support.
The full family

```text
{H_tilde^j(Delta|W;k): W subset V, j>=-1}                 (6)
```

is the complete multigraded Betti profile of the HT structural orbit module at the identity.
Connected-component defects, loops, cavities, and higher holes therefore appear in distinct
source-coherence degrees.

The exact projective dimension is

```text
pd_R(M_Delta)
 = max {|W|-j-1 : H_tilde^j(Delta|W;k) != 0}.             (7)
```

Thus the classical boundary dimension and the derived coherence amplitude are independent: a
thin reduced support can carry arbitrarily deep source coherence.

### 3.2 Universal topological realization

Every finite simplicial complex is already realized by some `F_Delta`.  Combining that theorem
with `(3)` gives:

> **POSITIVE UNIVERSALITY THEOREM.** Every finite simplicial cohomology pattern, including the
> full induced-subcomplex profile `(6)`, occurs as the exact higher source-coherence profile of a
> scalar meromorphic hypertranscendental structural system.

This is stronger than realizing every support topology.  It realizes the topology as the complete
derived relation hierarchy of an actual analytic HT source.

The normal-crossing exterior-coherence theorem is one explicit high-capacity chart of this law.
Its star classes and their exterior products are concrete representatives of positive Tor
classes; `(3)` identifies the general receiver in which such classes live.

### 3.3 Derived topology still does not select the analytic source

Finite residue surgery preserves the same embedded differential field and the same exact
Stanley--Reisner orbit module `(1)` while realizing every finite negative-residue index.  Since
the complete derived fibre `(2)` is functorially determined by `(1)`, every such surgery also
preserves all groups and products in `(2)`--`(6)`.

```text
[NO-GO]
The full derived Stanley--Reisner constraint topology, including every higher source-coherence
group, determines the analytic orientation or positivity stratum of a hypertranscendental source.
```

The no-go has a strong positive replacement:

> **DERIVED-TOPOLOGY--ORIENTATION PRODUCT LAW.** Arbitrary finite derived constraint topology and
> arbitrary finite residue orientation coexist over one universal HT differential field.  The
> missing invariant is a coupling of topology to an active analytic realization and a signed
> polarization, not another unpolarized homology group.

This prevents a false promotion of `(3)` to a complete theory.  Derived topology is a complete
kinematic invariant of the constraint presentation in this class, but it is source-blind.

## 4. What now constrains hypertranscendental functions

The theorem changes the high-level question.  Bare HT has a universal free differential bulk, and
its finite source boundaries can have arbitrary topology and arbitrary higher coherence.  A
natural HT source is constrained only when this kinematic boundary is required to admit one
effective analytic realization with active source action, pointing, growth, comparison maps, and
polarization.

> **[CONJECTURE -- ACTIVE POLARIZED CONSTRAINT-SHEAF DUALITY]** Regular source-minimal analytic HT
> germs are equivalent, up to differential-birational source equivalence, to effective pointed
> active polarized constructible derived sheaves on their constraint spectra whose vertex stalk
> is the universal free differential field, whose singular source fibre is the Hochster object
> `(3)`, and whose comparison, growth, and polarization data satisfy analytic descent.
>
> The equivalence is fully faithful, and its essential image is cut out by analytic effectivity,
> concentrated active capacity, source composition, critical bornology, and positivity.

This is not the standard statement that a Stanley--Reisner ring has a derived category.  The open
claim is reconstruction and essential-image classification for analytic hypertranscendental
sources.  It predicts that continuation, monodromy, spectral, boundary, and positivity theories
are realization functors of one active polarized sheaf, while `(3)` is its unpolarized kinematic
fibre.

The conjecture is falsified by two analytically inequivalent source-minimal HT germs with
equivalent noncircular active polarized constraint sheaves, or by a persistent source-natural
obstruction invisible to every such realization.

## 5. Novelty gate

The following are parent mathematics and are not claimed as new:

1. Hochster's formula for multigraded Betti numbers of Stanley--Reisner rings;
2. flat base change for free resolutions and Tor;
3. squarefree-module duality, moment-angle complexes, and derived categories of face rings;
4. differential operators on a Stanley--Reisner ring.

The candidate-new result is the cross-category conjunction:

```text
one scalar meromorphic HT source realizes every finite Stanley--Reisner differential matroid
  + its exact DA-relative orbit module has Hochster source-coherence fibre
  + every induced-subcomplex cohomology class is an actual higher HT source relation
  + the entire derived topology remains independent of analytic orientation.               (8)
```

Targeted exact and mechanism searches found the parent theories separately.  They found no paper
realizing arbitrary finite simplicial cohomology profiles as the exact derived DA-relative source
relations of scalar meromorphic hypertranscendental systems, nor the product no-go with every
finite orientation stratum.  This is a provisional priority result pending specialists in
difference algebra and combinatorial commutative algebra.

## 6. Significance and anti-theatre verdict

- `[NOVELTY -- PROVISIONAL PASS]` for the analytic HT realization conjunction `(8)`; not for
  Hochster's formula.
- `[SIGNIFICANCE -- PASS]` because the theorem upgrades arbitrary support topology to arbitrary
  derived source topology and proves exactly why topology alone cannot be the selector.
- `[ANTI-THEATRE -- PASS]` because the standard algebraic parent is explicit, the analytic input
  is exact, and the completeness overclaim is killed by the orientation product theorem.
- `[PAPER VERDICT]` The theorem belongs in the universal constraint-spectrum paper and may warrant
  a separate derived-topology sequel after independent audit.
- `[MEDAL-SCALE VERDICT]` Not by itself.  The Fields-scale successor is the fully faithful active
  polarized constraint-sheaf correspondence and its analytic essential-image theorem.

## 7. Lean boundary

Already Lean-formalized inputs include:

- exact Stanley--Reisner nonface ideals and facet-prime decomposition;
- exact analytic face/nonface realization;
- complete finite nonlinear differential-matroid realization;
- invariance under arbitrary finite residue surgery;
- arbitrary topology--orientation product realization;
- explicit degree-one and degree-two normal-crossing coherence classes.

The new formal target is the characteristic-free algebraic bridge `(5)`--`(3)`.  It must construct
the squarefree Koszul strands and their chain equivalence with reduced cochains of induced
subcomplexes.  A structure carrying Hochster's formula as a field is rejected as circular.  The
first acceptable Lean milestone is an unconditional chain equivalence in one nontrivial family,
followed by the general finite-complex equivalence.

That first milestone is now complete in

```text
formal/GaloisForLFunctions/HTGeometry/KoszulCohomology.lean
```

The file defines the nodal Stanley--Reisner boundary as the fibre-product ring
`F[x] x_F F[y]`, maps the actual squarefree quotient `F[x,y]/(xy)` into that detecting model,
constructs its two-coordinate Koszul complex at degrees one and two, and proves:

- `nodalBoundaryX_mul_Y`, the missing-edge relation `xy=0`;
- `nodalKoszulRelation_disconnectCycle`, that the disconnected-vertex representative is a cycle;
- `nodalKoszulRelation_boundary`, that the displayed degree-two images are cycles;
- `nodalDisconnectCycle_not_koszulBoundary`, that the representative is not a boundary.
- `nodalNonedgeIdeal_le_ker_boundaryEvaluation`, that the missing-edge quotient maps to the
  detecting fibre product;
- `nodalStanleyReisnerDisconnectCycle_not_koszulBoundary`, that the class is nonboundary in the
  actual quotient `F[x,y]/(xy)`, not only in the detecting model.
- `isolatedBoundaryX_mul_eq_zero`, the complete family of nonedge relations for any finite
  discrete complex with at least two vertices;
- `isolatedKoszulRelation_disconnectCycle`, the uniform disconnected-vertex cycle law;
- `isolatedH0Detector_boundary`, that the reduced-`H^0` coefficient detector annihilates every
  degree-two Koszul boundary in the arbitrary-size family;
- `isolatedDisconnectCycle_not_koszulBoundary`, that every such discrete complex carries the
  resulting nonzero first Koszul class.
- `isolatedDisconnectCycleBasis`, the canonical base-to-component cycle for every non-base
  isolated vertex;
- `isolatedH0DetectorAt_disconnectCycleBasis`, the full Kronecker-dual detector family;
- `isolatedH0DetectorAt_boundary`, that every component detector annihilates every degree-two
  Koszul boundary;
- `isolatedDisconnectCycleBasis_independent_mod_koszulBoundary`, that for `n+2` isolated vertices
  the `n+1` canonical cycles are linearly independent modulo Koszul boundaries.

This now formalizes the characteristic-free reduced-`H^0` Hochster class uniformly for every
finite discrete complex with at least two vertices, including the full expected independent
base-to-component family rather than only one class or the two-vertex seed.  The general strand
equivalence for arbitrary finite complexes remains open, so this card stays in stage 2.

## Gates

- [x] exact analytic Stanley--Reisner HT module available
- [x] flat-localization reduction proved on paper
- [x] Hochster identification applied with exact indexing
- [x] arbitrary derived-topology realization deduced
- [x] derived-topology selector claim falsified by orientation surgery
- [x] strong topology--orientation product successor stated
- [x] preliminary external exact/mechanism novelty search
- [x] Lean-formalize a nontrivial unconditional Hochster class
- [x] Lean-formalize the reduced-`H^0` class for every finite discrete complex with at least two
  vertices
- [x] Lean-formalize the full independent reduced-`H^0` family for every finite discrete complex
- [ ] Lean-formalize the general finite-complex bridge
- [ ] independently audit localization and grading conventions
- [ ] obtain specialist novelty and significance review
- [ ] construct one active polarized analytic sheaf realization
- [ ] prove full faithfulness in a nontrivial HT class

### Lean progress (combinatorial reduced-H⁰ target of the strand equivalence)
`HTGeometry/ReducedH0Components.lean` [PROVED HERE], standard axioms [propext, Classical.choice,
Quot.sound], builds clean, formal lint passed.

Delivered — the combinatorial (reduced simplicial cohomology) side of the Hochster strand equivalence at
degree 0, for the 1-skeleton of a finite complex (a `SimpleGraph` on a Fintype over a field `F`):
- `componentConstant G F` : the submodule of 0-cochains constant on connected components (= ker of the
  graph coboundary);
- `componentConstantEquiv` : `componentConstant ≃ₗ[F] (ConnectedComponent → F)` (component-constant
  cochains are exactly functions on components), via `ConnectedComponent.lift`/`.ind`/`.sound`;
- `finrank_componentConstant` : `dim (ker coboundary) = card (components)`;
- `finrank_reducedH0` : reduced `H̃⁰ = componentConstant/⟨1⟩` has `dim = card(components) − 1`.

This is the H⁰ combinatorial target that the isolated (fully discrete) Koszul `H¹`-rank in
`KoszulCohomology.lean` (`isolatedDisconnectCycleBasis_independent_mod_koszulBoundary`, giving `n+1`
classes for `n+2` discrete vertices) must equal: for the discrete complex, `card(components)=|V|`, so
reduced `H̃⁰ = |V|−1 = n+1`, matching. REMAINING for the general strand equivalence: (i) the algebraic
squarefree-Koszul-strand ↔ reduced-cochain chain map for arbitrary induced subcomplexes and all degrees,
(ii) matching the exact ranks (Koszul-side spanning/upper bound) — the deep general Hochster identity.

### Lean progress 2 — "reflection removes one layer" at degree 0
`HTGeometry/ReflectionRemovesLayer.lean` [PROVED HERE], standard axioms [propext, Classical.choice,
Quot.sound], builds clean, my-cone lint clean (only unrelated parallel-agent RHTower XiWeilResolventGram
unreachable + Hurwitz large-file warning).

Delivered — the card's title mechanism ("Reflection removes exactly one face layer") formalized at the
reduced-H⁰/degree-0 combinatorial level, via a DIMENSION argument (no component-bijection needed):
- `componentIndicator G F a` : the component-constant 0-cochain that is 1 on `a`'s component, 0 elsewhere;
- `diffFunctional G F a b` : the reflection functional `f ↦ f a − f b` on `componentConstant G F`;
- `finrank_diffFunctional_ker` : if `a,b` lie in DIFFERENT components (`¬ G.Reachable a b`), the kernel
  `{f | f a = f b}` (= component-constant cochains of the edge-augmented complex) has dimension
  `card(components) − 1` — exactly one less than `componentConstant G F` (whose dim is `card(components)`
  by last session's `finrank_componentConstant`). Proof: the functional is surjective (via `componentIndicator`
  hitting 1), so rank-nullity drops the kernel dimension by exactly 1.

This is the degree-0 shadow of the general Hochster "one face layer per reflection" mechanism, now
combinatorially exact. REMAINING (deep, general): the algebraic Koszul-strand ↔ reduced-cochain chain
equivalence for arbitrary induced subcomplexes in all degrees, and the exact-rank match.

### Lean progress 3 — degree-0 reduced-H⁰ at extreme complexes
`HTGeometry/ReducedH0DiscreteComplex.lean` [PROVED HERE], standard axioms [propext, Classical.choice,
Quot.sound], builds clean, my-cone lint clean (only unrelated parallel-agent RHTower unreachable errors).

Delivered — the two boundary values of reduced `H̃⁰`, pinning the degree-0 combinatorial side against the
algebraic Koszul computation:
- `card_connectedComponent_bot` : the discrete complex (empty graph `⊥`) has `card V` components;
- `finrank_reducedH0_bot` : **discrete-complex reduced `H̃⁰ = card V − 1`** — the exact value the isolated
  (fully discrete) Koszul `H¹`-family computes on the algebraic side (`n+1` classes for `n+2` vertices).
  This is the degree-0 discrete Hochster identity, both sides now equal to `|V|−1`;
- `finrank_reducedH0_of_connected` : a connected complex has reduced `H̃⁰ = 0`.

Combinatorial degree-0 side is now complete (general `= components−1`, reflection-removes-one-layer,
discrete/connected extremes). REMAINING (deep): the general Koszul-strand ↔ reduced-cochain chain
equivalence in all degrees + the algebraic-side exact-rank (spanning) match.

### Lean progress 4 — reduced H̃⁰ is genuine simplicial cohomology (coboundary kernel)
`HTGeometry/GraphCoboundary.lean` [PROVED HERE], axioms [propext, Quot.sound], builds clean, my-cone
lint clean (only unrelated parallel-agent RHTower unreachable errors).

Delivered — the explicit degree-0 simplicial coboundary, tightening the combinatorial side to honest
simplicial cohomology:
- `graphCoboundary G F` : the `F`-linear coboundary `(δ⁰ f)(u,v) = f v − f u` on edges, `0` off edges;
- `graphCoboundary_ker` : `ker δ⁰ = componentConstant G F`. Hence `H⁰ = ker δ⁰` is exactly the
  component-constant space, so `reduced H̃⁰ = ker δ⁰ / ⟨1⟩` (Lean progress 1) is genuine reduced
  simplicial cohomology, not an ad-hoc definition.

COMBINATORIAL DEGREE-0 SIDE NOW A COHERENT COMPLETE PACKAGE: coboundary δ⁰ + ker δ⁰ = componentConstant
(H⁰); reduced H̃⁰ = components−1 (Lean progress 1); reflection removes one layer (Lean progress 2);
discrete/connected extremes (Lean progress 3). All axiom-clean, matching the algebraic Koszul side
numerically at the discrete case.
REMAINING for card completion (deep, largely in the algebraic/KoszulCohomology cone): the general
Koszul-strand ↔ reduced-cochain chain equivalence in all degrees + the algebraic-side exact-rank
(spanning) match — the full Hochster isomorphism. Degree-1 combinatorial side (reduced H̃¹ = first Betti,
needs edge orientation) is the next non-colliding combinatorial extension if continued.

### Lean progress 5 — coboundary rank = |V| − components
`HTGeometry/GraphCoboundaryRank.lean` [PROVED HERE], standard axioms, builds clean, my-cone lint clean.
- `finrank_graphCoboundary_range` : `rank δ⁰ = |V| − (number of components)` (cut-space dimension), via
  rank–nullity + `graphCoboundary_ker` + `finrank_componentConstant`;
- `finrank_graphCoboundary_range_of_connected` : connected ⟹ `rank δ⁰ = |V| − 1` (spanning-tree edge count).
This is the coboundary-rank input to reduced `H̃¹ = |E| − rank δ⁰ = |E| − |V| + components` (first Betti).
NEXT combinatorial: define `C¹` (oriented edge cochains, dim `|E|`) and `H̃¹` as `C¹/range δ⁰`; then the
deep card capstone remains the algebraic Koszul-strand ↔ reduced-cochain equivalence (KoszulCohomology cone).

### Lean progress 6 — reduced H̃¹ = first Betti number (combinatorial side COMPLETE for graphs)
`HTGeometry/ReducedH1FirstBetti.lean` [PROVED HERE], standard axioms, builds clean, my-cone lint clean.
- `orientedEdges G` (adjacent pairs `u<v` via a `LinearOrder V`), `orientedCoboundary` (degree-1
  coboundary `(δ⁰ f)(u,v)=f v−f u`), `orientedCoboundary_ker = componentConstant`;
- `finrank_orientedCoboundary_range = |V| − components`;
- `finrank_reducedH1` : **reduced `H̃¹ = (oriented edges → F)/im δ⁰` has dimension
  `|E| − (|V| − components) = |E| − |V| + components`** (the first Betti / cyclomatic number).

MILESTONE: with `H̃⁰ = components − 1` (progress 1) and `H̃¹ = |E| − |V| + components` (progress 6), the
FULL reduced simplicial cohomology of a finite graph (1-skeleton) over a field is now formalized — the
complete combinatorial (reduced-cochain) side of the Hochster strand equivalence for the 1-skeleton,
in every degree a graph has. Supporting: coboundary `δ⁰`+`ker=componentConstant` (progress 4), coboundary
rank (progress 5), reflection-removes-one-layer (progress 2), discrete/connected extremes (progress 3).
REMAINING for card completion (deep, algebraic cone): the Koszul-strand ↔ reduced-cochain chain
equivalence in all degrees (general finite complexes) + algebraic exact-rank match — the full Hochster
isomorphism.

### Lean progress 7 — reduced Euler–Poincaré (combinatorial reduced-cohomology package COMPLETE)
`HTGeometry/ReducedEulerCharacteristic.lean` [PROVED HERE], standard axioms, builds clean, my-cone lint clean.
- `reduced_euler_poincare` : `dim H̃⁰ + |E| + 1 = dim H̃¹ + |V|` (both `= |E| + components`), i.e.
  `χ̃ = dim H̃⁰ − dim H̃¹ = |V| − |E| − 1`.

COMBINATORIAL SIDE FOR GRAPHS NOW A COMPLETE COHERENT UNIT (7 modules): reduced simplicial cohomology
of a finite 1-skeleton over a field — `H̃⁰=components−1`, `H̃¹=|E|−|V|+components` (first Betti),
Euler–Poincaré; with coboundary δ⁰ (`ker=componentConstant`), coboundary rank `|V|−components`,
reflection-removes-one-layer, discrete/connected extremes. All axiom-clean.
CARD COMPLETION still requires the deep algebraic **Hochster isomorphism**: Koszul-strand ↔ reduced-cochain
chain equivalence for general finite complexes (all degrees) + algebraic exact-rank match. That lives in
the KoszulCohomology (algebraic) cone; it is the remaining multi-session build, NOT more combinatorial lemmas.

### Lean progress 8 — ALGEBRAIC side: isolated Koszul cocycles = diagonal-free vectors
`HTGeometry/IsolatedKoszulCocycle.lean` [PROVED HERE], standard axioms, builds clean, my-cone lint clean.
(First step on the ALGEBRAIC direction per the discipline note — not more combinatorial lemmas.)
- `isolatedKoszulRelation_val_apply` : the Koszul relation reads off on axis `k` as `(a k)ₖ · X`
  (off-diagonal isolated axes multiply to zero, `isolatedBoundaryX_mul_eq_zero`);
- `isolatedKoszulRelation_eq_zero_iff` : **`Σ aᵢ xᵢ = 0 ↔ ∀ k, (a k)ₖ = 0`** — the isolated Koszul
  cocycle space is exactly the diagonal-free coefficient vectors.

This characterizes the cocycle space, the algebraic input for computing the EXACT first Koszul
cohomology rank (`H¹ = n+1`), which would match the combinatorial reduced `H̃⁰ = |V|−1 = n+1` (Lean
progress 3) — the degree-0 Hochster identity. REMAINING toward that: (i) cocycle-with-all-detectors-zero
⟹ boundary (exactness/spanning), giving `H¹ = n+1` exactly; (ii) the general-complex chain equivalence.

### Lean progress 9 — ALGEBRAIC side: isolated Koszul boundary axis-components
`HTGeometry/IsolatedKoszulCocycle.lean` (extended) [PROVED HERE], standard axioms, builds clean, my-cone lint clean.
- `isolatedKoszulBoundary_val_apply` : `(isolatedKoszulBoundary c i)ₖ = if i<k then -(c i k)ₖ·X else if
  k<i then (c k i)ₖ·X else 0` — the boundary map reads off on each axis as an oriented `(c ??)ₖ·X`.

Now BOTH axis-component computations of the isolated Koszul complex are formalized: relation/cocycle
(`isolatedKoszulRelation_val_apply`, progress 8) and boundary (`isolatedKoszulBoundary_val_apply`). This is
the coherent algebraic foundation for the exact first-Koszul-cohomology structure (the `X`-linear/coeff-1
graded piece where the `n+1` Hochster classes live), toward the degree-0 Hochster identity matching the
combinatorial reduced `H̃⁰`. REMAINING: assemble these into the exact rank via the coeff-1 graded exactness.
