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

### Lean progress 10 — ALGEBRAIC side: linear part of the Koszul boundary is antisymmetric
`HTGeometry/IsolatedKoszulCoeffOne.lean` [PROVED HERE], standard axioms, builds clean, my-cone lint clean.
- `isolatedKoszulBoundary_coeff_one` : `((isolatedKoszulBoundary c i)ₖ).coeff 1 = if i<k then
  -(c i k)ₖ.coeff 0 else if k<i then (c k i)ₖ.coeff 0 else 0` — the `X`-linear part of a Koszul boundary
  is an ANTISYMMETRIC matrix in the position/axis indices `(i,k)`.

Algebraic foundations now assembled: cocycles = diagonal-free (progress 8), boundary axis-components
(progress 9), boundary linear part antisymmetric (progress 10). NOTE (multigraded insight): the exact
first-Koszul-cohomology rank is MULTIGRADED — the `n+1` Hochster classes live at a specific multidegree
(the reduced `H̃⁰` of the full complex), not the whole `coeff 1` piece (whose naive dimension is
`(n+2)(n+1)/2`, a lower-bound-only count). Completing the degree-0 Hochster identity therefore needs the
multigraded (per-vertex-subset) restriction, which is the deep remaining algebraic work.

### Lean progress 11 — explicit degree-0 Hochster identity (both sides connected)
`HTGeometry/HochsterDegreeZeroDiscrete.lean` [PROVED HERE], standard axioms, builds clean, my-cone lint clean.
- `finrank_reducedH0_bot_eq_isolatedBasis_card` : **`dim(reduced H̃⁰ of discrete complex on n+2 vertices)
  = Fintype.card (Fin (n+1))`** — the combinatorial reduced zeroth cohomology dimension equals the number
  of isolated-family first-Koszul Hochster classes (`isolatedDisconnectCycleBasis`, indexed by `Fin(n+1)`,
  independent mod boundary), both `= n+1`.

This is the FIRST explicit theorem CONNECTING the two sides built over these sessions: the combinatorial
(reduced-cochain) side and the algebraic (Koszul) side, at degree 0 for the discrete complex — the
degree-0 instance of the Hochster strand equivalence. The full card completion still needs the exact
algebraic rank (multigraded, so the count is currently a lower bound on the algebraic side) and the
general-complex/all-degree chain equivalence.

### Lean progress 12 — basis cycles diagonal-free + KEY structural analysis of the exact rank
`HTGeometry/IsolatedKoszulBasis.lean` [PROVED HERE], standard axioms, builds clean, formal lint passed.
- `isolatedDisconnectCycleBasis_diagonal_free` : each base-to-component basis cycle `(basis j)ₖ` has zero
  `k`-th component; `isolatedKoszulRelation_disconnectCycleBasis_of_diagonal_free` re-derives that they are
  cocycles via the diagonal-free characterization (progress 8), checking the characterization on the basis.

KEY STRUCTURAL ANALYSIS (recorded to guide the remaining capstone, from this session's derivation using
progress 8/9/10): the ISOLATED model `isolatedBoundarySubring ≅ F[x_0..x_{n+1}]/(x_i x_j : i≠j)` (discrete
SR ring). At the LINEAR (coeff-1) level: cocycles = zero-diagonal matrices `C_{ik}=((a_i)_k).coeff 1`
(dim `(n+2)(n+1)`); boundaries = ANTISYMMETRIC matrices (dim `C(n+2,2)`, progress 10 + free c-coefficients);
so the linear first Koszul cohomology `= zero-diagonal / antisymmetric ≅ SYMMETRIC-off-diagonal`, dim
`C(n+2,2)` — NOT `n+1`. Hence the `n+1` Hochster classes (matching reduced `H̃⁰`) are a specific
`n+1`-dim STRUCTURAL SUBSPACE (the star from vertex 0: `{x_{j+1} e_0}`) of the full `C(n+2,2)`-dim linear
`H₁`. The degree-0 Hochster identity (progress 11) therefore connects reduced `H̃⁰` to that subspace, and
the full card capstone requires the PRECISE MULTIGRADED Tor/Betti correspondence (β_{i,σ} = reduced
H̃^{|σ|-i-1}(Δ_σ)) selecting the right piece — the deep remaining homological-algebra work, now precisely
characterized.

### Lean progress 13 — cocycle coeff-1 diagonal vanishes (coeff-1 structural pair complete)
`HTGeometry/IsolatedKoszulCocycleCoeffOne.lean` [PROVED HERE], standard axioms, builds clean, formal lint passed.
- `isolatedKoszulRelation_eq_zero_coeff_one_diag` : a first Koszul cocycle has zero `coeff-1` diagonal.
Companion to progress 10 (boundary coeff-1 = antisymmetric). In the coeff-1 matrix `M_{ik}=((a i)_k).coeff 1`:
cocycles ⊆ zero-diagonal, boundaries = antisymmetric — the structural data of the linear first Koszul
cohomology (`= zero-diagonal/antisymmetric ≅ symmetric-off-diagonal`, dim `C(n+2,2)`; the Hochster `n+1`
is the specific structural subspace, needing the multigraded restriction).

### Lean progress — first non-discrete complex (single-edge Stanley–Reisner)

Toward the open "general strand equivalence for arbitrary finite complexes", the first complex type
beyond the discrete (all-isolated) and nodal (2-vertex) cases is now formalized unconditionally in
`GaloisForLFunctions.HTGeometry.SingleEdgeStanleyReisner` (axiom-clean, in the built HTGeometry
umbrella): the single-edge complex on `n + 2` vertices (one edge `{0,1}`, `n` isolated vertices).

- `singleEdgeBoundarySubring` — its Stanley–Reisner ring, realized concretely as the subalgebra of
  `MvPolynomial (Fin 2) F × (Fin n → Polynomial F)` glued at the common constant term (free
  two-variable edge block + `n` isolated one-variable axes).
- `singleEdgeX`, `singleEdgeIsoX` — the edge-vertex and isolated-vertex coordinates.
- `singleEdgeX_mul_edgeX_ne_zero` — the edge `{0,1}` is a face: `x₀x₁ ≠ 0` (the surviving product
  that distinguishes it from the discrete complex).
- `singleEdgeX_mul_isoX_eq_zero`, `singleEdgeIsoX_mul_isoX_eq_zero` — every nonedge product vanishes.
- `singleEdgeVertexX`, `singleEdgeKoszulRelation` — the vertex coordinate family (indexed
  `Fin 2 ⊕ Fin n`) and its first Koszul relation.
- `singleEdgeKoszulRelation_disconnectCycle` — the `n` base-to-isolated disconnect cycles are first
  Koszul cycles, i.e. the `n` reduced-`H⁰` Hochster classes, matching the `n + 1` connected
  components (reduced `H̃⁰` dimension `n`).

Next: linear independence of these `n` cycles modulo Koszul boundaries (the degree-0 Hochster
isomorphism for the single-edge complex), then higher-face complexes toward the general equivalence.

### Lean progress — single-edge degree-0 Hochster isomorphism complete

The single-edge complex now has its full degree-0 Hochster picture in
`GaloisForLFunctions.HTGeometry.SingleEdgeStanleyReisner` (all axiom-clean, umbrella-registered):

- `singleEdgeKoszulBoundary` — the first Koszul boundary submodule (trivial syzygies), written
  order-free via antisymmetrization over the vertex set `Fin 2 ⊕ Fin n`.
- `singleEdgeH0DetectorAt` — the reduced-`H⁰` detector family, one linear functional per isolated
  component `k`, symmetric between the base edge vertex (isolated-axis-`k` linear coefficient) and
  the isolated vertex (`x₀` edge coefficient).
- `singleEdgeH0DetectorAt_disconnectCycle` — Kronecker duality `Dₖ(cycleₗ) = δₖₗ`.
- `singleEdgeH0DetectorAt_boundary` — the symmetric detector annihilates every antisymmetric Koszul
  boundary.
- `singleEdgeDisconnectCycle_not_koszulBoundary` — each disconnect cycle is a nonzero first Koszul
  class.
- `singleEdgeDisconnectCycle_independent_mod_koszulBoundary` — the `n` disconnect cycles are linearly
  independent modulo Koszul boundaries: the first Koszul quotient contains the full reduced-`H̃⁰`
  rank `n` for the single-edge complex.

This completes the degree-0 Hochster isomorphism for the first non-discrete complex, alongside the
discrete (`isolated*`) and nodal (`nodal*`) cases. Next: complexes with a face of dimension ≥ 2
(higher Koszul strands), toward the general strand equivalence.

### Lean progress — general Stanley–Reisner nonface relation (arbitrary complexes)

Pivoting from concrete per-complex models to the corpus's general Stanley–Reisner quotient
framework (`stanleyReisnerIdeal`, `mem_stanleyReisnerIdeal_iff`, `IsFaceOf`), the defining relation
of every Stanley–Reisner ring is now proved uniformly for all finite complexes in
`GaloisForLFunctions.HTGeometry.StanleyReisnerVertexRelation` (axiom-clean, umbrella-registered):

- `stanleyReisnerRing`, `srVertexX` — the Stanley–Reisner ring `MvPolynomial α F ⧸ stanleyReisnerIdeal`
  and its vertex coordinates `x_v`.
- `srVertexX_mul_eq_zero_of_not_isFace` — **the general nonface relation**: for any finite complex,
  `x_u · x_v = 0` in the Stanley–Reisner ring exactly when `{u,v}` is a nonface.  This is the single
  relation that the concrete `isolatedBoundaryX_mul_eq_zero`, `nodalBoundaryX_mul_Y`, and
  `singleEdgeX_mul_isoX_eq_zero` each realized in a fixed complex, now stated once over every finite
  complex.

This is the foundation for a uniform Koszul-cohomology / Hochster treatment on arbitrary complexes.
Next: the general vertex Koszul relation and base-to-component disconnect cycles indexed by the
connected components of the complex's 1-skeleton, connecting to the corpus's combinatorial
`finrank_reducedH0` (= components − 1).

### Lean progress — general Koszul disconnect cycle (arbitrary complexes)

Building on the general nonface relation, the base-to-component Koszul cycle is now proved uniformly
for all finite complexes in `GaloisForLFunctions.HTGeometry.StanleyReisnerVertexRelation`:

- `srKoszulRelation` — the first Koszul relation `∑ v aᵥ xᵥ` of the vertex coordinate family.
- `srDisconnectCycle` — the base-to-`w` disconnect cycle (coordinate `x_w` at the base vertex).
- `srKoszulRelation_disconnectCycle` — whenever `{v₀, w}` is a nonface (in particular whenever `v₀`
  and `w` lie in different connected components of the 1-skeleton), the disconnect cycle is a first
  Koszul cycle.  This is the uniform form of the concrete `isolatedKoszulRelation_disconnectCycle`
  and `singleEdgeKoszulRelation_disconnectCycle` for arbitrary finite complexes.

Next: base-to-component detector functionals on the Stanley–Reisner quotient (well-defined on the
degree-1 part), boundary annihilation, and independence indexed by the `components − 1` non-base
components — the general degree-0 Hochster isomorphism connecting to `finrank_reducedH0`.

### Lean progress — general reduced-H⁰ detector on the SR quotient

The reduced-`H⁰` detector, the subtle piece (a functional well-defined on the quotient), is now built
uniformly for all finite complexes in `StanleyReisnerVertexRelation` (axiom-clean):

- `coeff_single_eq_zero_of_mem_stanleyReisnerIdeal` — the `x_w`-coefficient reader annihilates the
  Stanley–Reisner ideal whenever `{w}` is a face (nonface monomials have degree ≥ 2).
- `srH0Detector` — the base-to-component detector for a present vertex `w`, the `x_w`-coefficient
  reader descended to the Stanley–Reisner ring via `Submodule.liftQ` using the vanishing lemma.
- `srH0Detector_mk` — its computation rule on ring representatives.
- `srH0Detector_srVertexX` — **Kronecker duality** `Dₓ(x_v) = δ_{wv}`.

Next: the descended constant-term functional, the product-detector rule
`Dₓ(r · x_j) = if w = j then constTerm r else 0`, the symmetric family detector
`Φ_w(a) = Dₓ(a v₀) + D_{v₀}(a w)`, its Koszul-boundary annihilation, and independence indexed by the
non-base components — completing the general degree-0 Hochster isomorphism.

### Lean progress — GENERAL degree-0 Hochster isomorphism COMPLETE (arbitrary complexes)

The degree-0 case of the card's open "general strand equivalence for arbitrary finite complexes" is
now fully formalized unconditionally in `StanleyReisnerVertexRelation` (all axiom-clean, umbrella-
registered, lint green), superseding the concrete discrete/nodal/single-edge models:

- `srConstTerm` / `srConstTerm_mk` — the descended constant-term functional on the SR ring.
- `srH0Detector_mul_srVertexX` — the product-detector rule `D_w(r·x_j) = if w=j then constTerm r else 0`.
- `srKoszulBoundary` / `srH0Detector_srKoszulBoundary` — the first Koszul boundary submodule and the
  collapse of a boundary's detector to `constTerm (c i w − c w i)`.
- `srDisconnectCycle_independent_mod_koszulBoundary` — **the capstone**: for any finite complex with
  all vertices present and any base vertex `v₀`, the base-to-component disconnect cycles are linearly
  independent modulo first Koszul boundaries (all non-base coefficients of a boundary vanish).  The
  proof uses the symmetric detector `Φ_w(a) = D_w(a v₀) + D_{v₀}(a w)`, which reads off each
  coefficient by Kronecker duality yet annihilates every antisymmetric boundary.

This gives the full reduced-`H̃⁰` rank (`components − 1`) inside the first Koszul quotient, uniformly
over all finite complexes — the general degree-0 Hochster isomorphism.  The remaining open frontier
is degree ≥ 1 (complexes with 2-faces → higher Koszul strands and reduced `H̃¹`).

### Lean progress — 1-skeleton graph bridge

The algebraic degree-0 Hochster data is now bridged to the combinatorial graph side in
`GaloisForLFunctions.HTGeometry.StanleyReisnerOneSkeleton` (axiom-clean, umbrella-registered):

- `oneSkeletonGraph` — the 1-skeleton `SimpleGraph` of a finite complex (distinct vertices adjacent
  iff their pair is a face).
- `not_isFace_of_not_reachable` — two vertices in different connected components form a nonface pair.
- `srKoszulRelation_disconnectCycle_of_not_reachable` — the graph form of the disconnect-cycle law:
  when `v₀` and `w` are in different components of `oneSkeletonGraph`, the base-to-`w` disconnect
  cycle is a first Koszul cycle.

This indexes the reduced-`H̃⁰` Koszul classes (`srDisconnectCycle_independent_mod_koszulBoundary`) by
the non-base connected components of the 1-skeleton, aligning the algebraic side with the corpus's
combinatorial `componentConstant` / `finrank_reducedH0` (= `components − 1`).

### Lean progress — d₁∘d₂ = 0 (boundaries are cycles) for the general SR Koszul complex

`srKoszulRelation_srKoszulBoundary` (in `StanleyReisnerVertexRelation`, axiom-clean) proves the
fundamental Koszul-complex identity for every finite complex: every first Koszul boundary
`srKoszulBoundary c` is a first Koszul cycle (`srKoszulRelation` of it is `0`).  The antisymmetric
coefficients `c i j − c j i` pair against the symmetric products `xⱼ xᵢ` and cancel unconditionally
(via `Finset.sum_comm` + `mul_comm`, no characteristic hypothesis).

This makes the first Koszul homology `cycles / boundaries` a genuine subquotient, so the earlier
`srDisconnectCycle_independent_mod_koszulBoundary` is independence in an actual homology module — the
degree-0 Hochster line is now internally complete (complex condition + cycles + independence).

### Correction (2026-07-25): what the disconnect-cycle independence actually computes

An accuracy correction to the preceding "general degree-0 Hochster" entries.  The Lean theorems are
all correct and axiom-clean, but the *interpretation* connecting them to the whole-complex reduced
`H̃⁰ = components − 1` was a conflation of two different Hochster strands.

The first Koszul homology of the vertex multiplications on the Stanley–Reisner ring is
`H₁(x_•; S) = Tor₁^{poly}(k, S) = ⊕_σ H̃^{|σ|−2}(Δ_σ)`.  The disconnect cycle `x_w · e_{v₀}` sits at
multidegree `{v₀, w}` (so `|σ| = 2`), representing the strand
`Tor_{1,{v₀,w}} = H̃⁰(Δ_{{v₀,w}})` = `H̃⁰` of the induced **two-vertex** subcomplex, which is
`1`-dimensional exactly when `{v₀,w}` is a nonedge.  So:

- `srDisconnectCycle_independent_mod_koszulBoundary` / `srDisconnectCycle_not_koszulBoundary` correctly
  establish independent nonzero `Tor₁` classes at the two-element supports `{v₀, w}` — the **lowest**
  strand (`i = 1, |σ| = 2`) of Hochster's formula.
- These are **not** the whole-complex reduced `H̃⁰` (`= components − 1`), which is the **top** strand
  `Tor_{|V|−1, V}`.  The two coincide only for `|V| = 2`, and numerically (not as objects) for the
  fully discrete complex; for a connected complex with `|V| ≥ 3` they differ.
- Consequently `srKoszulRelation_disconnectCycle_of_not_reachable` and `oneSkeletonGraph` give a
  correct *sufficient* condition (different components ⇒ nonedge ⇒ cycle), but "indexed by the
  non-base components / `= components − 1`" overstates it; the honest index is the nonneighbors of the
  base vertex.

Net: the corpus now has, unconditionally over all finite complexes, the `|σ|=2` strand of Hochster's
`Tor₁` (independent classes + the `d₁∘d₂=0` complex condition).  The general strand equivalence for
`|σ| ≥ 3` (reduced `H̃^{≥1}` of induced subcomplexes) and the top-strand whole-complex `H̃⁰` remain
open.

### Lean progress — general nonface relation + first degree-1 (|σ|=3) cycle

Toward the genuine higher strands (`|σ| ≥ 3`), in `StanleyReisnerVertexRelation` (axiom-clean):

- `srProd_eq_zero_of_not_isFace` — the **full** Stanley–Reisner relation: the product of vertex
  coordinates over *any* nonface vanishes (arbitrary-cardinality generalization of the pairwise
  `srVertexX_mul_eq_zero_of_not_isFace`), via `VeroneseIdeal.prod_X_eq_monomial` + `mem_stanleyReisnerIdeal_iff`.
- `srKoszulRelation_emptyTriangleSyzygy` — the **first degree-1 object**: when `{a,b,c}` is a nonface
  (the empty triangle — three edges, no filling 2-face), the syzygy `xᵦxᵧ · eₐ` at multidegree
  `{a,b,c}` is a genuine first Koszul cycle (since `xᵦxᵧxₐ = 0`).  Modulo boundaries this carries
  `Tor_{1,{a,b,c}} = H̃¹(Δ_{{a,b,c}})` — the first place a genuine reduced `H̃¹` strand appears.

Next: prove this empty-triangle cycle is not a boundary — via the cyclic `|σ|=3` detector reading
the degree-2 coefficients of `xᵦxᵧ`, `xₐxᵧ`, `xₐxᵦ` (each descends to the quotient since the ideal
starts in degree ≥ 3 there) whose sum kills the three triangle boundaries — establishing the first
nonzero reduced-`H̃¹` Hochster class.

### Lean progress — degree-2 (pair) detector for the |σ|=3 strand

Foundation for proving the empty-triangle cycle nonzero, in `StanleyReisnerVertexRelation`
(axiom-clean):

- `coeff_eq_zero_of_isFace_support` — the **general** vanishing lemma: a monomial-coefficient reader
  annihilates the Stanley–Reisner ideal whenever the monomial's support is a face (unifying the
  degree-0, degree-1, and degree-2 cases).
- `srPairDetector` — the degree-two `x_u x_v`-coefficient reader descended to the Stanley–Reisner
  ring (well-defined when `{u,v}` is a face), with `srPairDetector_mk` and
  `srPairDetector_srVertexX_mul` (its value on `x_u x_v` is `1`).

Next: the pair-detector product rule `srPairDetector u v (r · x_j) = ` a degree-one detector of `r`
(`= D_v(r)` if `j=u`, `= D_u(r)` if `j=v`, else `0`), then the cyclic empty-triangle detector
`Φ(s) = D_{bc}(s_a) + D_{ac}(s_b) + D_{ab}(s_c)` whose value is `1` on the empty-triangle cycle and `0`
on every Koszul boundary (the degree-1 detector terms cancel in antisymmetric pairs) — giving the
first nonzero reduced-`H̃¹` Hochster class.

### Lean progress — FIRST nonzero reduced-H̃¹ Hochster class (empty triangle)

The degree-1 (|σ|=3) strand of Hochster's formula now has its first nonzero class, unconditional over
all finite complexes, in `StanleyReisnerVertexRelation` (axiom-clean):

- `srPairDetector_mul_srVertexX` — the pair-detector product rule linking the degree-two detector to
  the degree-one detectors (`D_{uv}(r·x_j) = D_v(r)` if `j=u`, `D_u(r)` if `j=v`, else `0`).
- `srPairDetector_srKoszulBoundary` — a boundary's pair-detector collapses to a sum of two degree-one
  detectors of antisymmetric coefficients.
- `srEmptyTriangleSyzygy_not_koszulBoundary` — **the capstone**: on an empty triangle `{a,b,c}` (three
  edges, no filling 2-face), the syzygy `xᵦxᵧ · eₐ` is not a first Koszul boundary, hence a nonzero
  class of `Tor_{1,{a,b,c}} = H̃¹(Δ_{{a,b,c}})`.  The cyclic detector `Φ = D_{bc}(sₐ)+D_{ac}(s_b)+D_{ab}(s_c)`
  is `1` on the syzygy and `0` on every boundary (its six degree-one detector terms cancel in
  antisymmetric pairs, closed by `linear_combination`).

Hochster's `Tor₁` is now formalized in both strands it reaches: `|σ|=2` (`H̃⁰` of 2-point subcomplexes,
the earlier disconnect cycles) and `|σ|=3` (`H̃¹` of the empty triangle).  Next: the general `|σ|=3`
`H̃¹` for arbitrary induced 3-vertex subcomplexes, and higher `|σ|`.

### Lean progress — degree-1 consolidation (packaged class + cyclic symmetry)

Consolidating the empty-triangle `H̃¹` milestone in `StanleyReisnerVertexRelation` (axiom-clean):

- `srEmptyTriangle_firstKoszulHomology_nonzero` — packages the result: the empty-triangle syzygy is a
  first Koszul cycle **and** not a first Koszul boundary, i.e. a nonzero class of `Tor₁` at
  `{a,b,c}` = `H̃¹(Δ_{{a,b,c}})`.
- `srEmptyTriangle_cyclic_syzygy_homologous` — the class is **cyclically symmetric**: the two cyclic
  syzygies `xᵦxᵧ · eₐ` and `xₐxᵧ · e_b` differ by an explicit first Koszul boundary
  (`srKoszulBoundary` of the single-entry coefficient `c_{a,b} = xᵧ`), hence represent the *same*
  class — the `1`-dimensional triangle-hole `H̃¹` is generated by any cyclic representative.

The degree-1 (`|σ|=3`) `Tor₁` strand is now complete and self-contained.  Deep next frontier: `Tor₂`
(the second Koszul homology, `ker d₂ / im d₃`), where the `4`-cycle `C₄` hole
(`H̃¹` at `|σ|=4`) first appears — requiring the third Koszul differential `d₃`.

### Lean progress — general face detector + H̃² cycle (hollow tetrahedron, |σ|=4)

Reaching second reduced cohomology without a new differential, in `StanleyReisnerVertexRelation`
(axiom-clean):

- `srFaceDetector` — the **general face detector**: the squarefree `∏_{v∈J} x_v`-coefficient reader
  descended to the Stanley–Reisner ring for any face `J` (`support_indicatorExponent`,
  `srFaceDetector_mk`, `srFaceDetector_prod` = `1` on `∏_{v∈J} x_v`).  It subsumes the degree-0
  (`J=∅`), degree-1 (`J={w}`), and degree-2 (`J={u,v}`) detectors under one construction.
- `srKoszulRelation_hollowTetrahedronSyzygy` — on a hollow tetrahedron `∂Δ³` (`{a,b,c,d}` nonface,
  every proper face present), the syzygy `xᵦxᵧx_d · eₐ` is a first Koszul cycle (via the general
  nonface relation `srProd_eq_zero_of_not_isFace`).  Modulo boundaries it carries
  `Tor_{1,{a,b,c,d}} = H̃²(Δ_{{a,b,c,d}})` — the first place **reduced `H̃²`** appears, still inside `Tor₁`.

Key structural insight: `H̃ⁿ` appears in `Tor₁` at `|σ|=n+2` (the boundary of the `(n+1)`-simplex), so
the whole reduced-cohomology tower is reachable through the single first-Koszul-homology machinery —
no higher Koszul differential `d₃, d₄, …` is needed for these "hollow simplex" classes.  Next: the
hollow-tetrahedron non-boundary via `srFaceDetector` + the degree-3→2 product rule and a 4-term
alternating detector, giving the first nonzero `H̃²` class.

### Lean progress — general face-detector product rule + boundary helper

Reusable generalizations enabling the uniform hollow-simplex `H̃ⁿ` classes, in
`StanleyReisnerVertexRelation` (axiom-clean):

- `srFaceDetector_mul_srVertexX` — the **general product rule**: `srFaceDetector J (r·x_j)` equals the
  deleted-vertex detector `srFaceDetector (J.erase j) r` when `j ∈ J`, and `0` otherwise (via
  `mk`-surjectivity, `coeff_mul_X'`, and the Finsupp identity `indicatorExponent_erase`).  Subsumes
  the degree-two `srPairDetector_mul_srVertexX`.
- `srFaceDetector_srKoszulBoundary` — the **general boundary helper**: `srFaceDetector J` of a Koszul
  boundary at position `i` is `∑_{j∈J} srFaceDetector (J.erase j) (c i j − c j i)` (via the product
  rule + `Finset.sum_ite_mem`).

Next: the uniform **hollow-simplex non-boundary** for all `n`, via the alternating(all-plus) detector
`Φ_σ(s) = ∑_{i∈σ} srFaceDetector(σ\{i})(s_i)`.  `Φ_σ(boundary) = ∑_{i≠j∈σ} srFaceDetector(σ\{i,j})(c_{ij}−c_{ji})`
vanishes by the `(i,j)↔(j,i)` involution (each transposed pair sums to `srFaceDetector(0)=0`,
unconditional — no characteristic-2 issue), while `Φ_σ(hollow-simplex syzygy) = 1`.  This gives every
`H̃ⁿ = H̃^{|σ|−2}(∂Δ^{|σ|−1})` Hochster `Tor₁` class in one theorem.

### Lean progress — general hollow-simplex cycle (all reduced-cohomology dimensions)

`srKoszulRelation_hollowSimplexSyzygy` (in `StanleyReisnerVertexRelation`, axiom-clean) is the uniform
cycle theorem: for any nonface `σ` and vertex `a ∈ σ`, the syzygy `(∏_{w∈σ∖a} x_w) · eₐ` at multidegree
`σ` is a first Koszul cycle, since `(∏_{w∈σ∖a} x_w) xₐ = ∏_{w∈σ} x_w = 0` (general nonface relation +
`Finset.mul_prod_erase`).  For a minimal nonface (`∂Δ^{|σ|−1}`) it carries `Tor_{1,σ} = H̃^{|σ|−2}(Δ_σ)`,
so this single theorem realizes the **entire reduced-cohomology tower** `H̃⁰, H̃¹, H̃², …` as first Koszul
cycles — subsuming the concrete triangle (`|σ|=3`) and tetrahedron (`|σ|=4`) syzygies.

Next: the uniform hollow-simplex **non-boundary** (all `H̃ⁿ` nonzero at once), via the detector
`Φ_σ(s) = ∑_{i∈σ} srFaceDetector(σ∖i)(sᵢ)` summed over `σ.attach` (the face proofs `IsFaceOf (σ∖i)`
depend on `i∈σ`), with boundary annihilation by the `(i,j)↔(j,i)` involution (`Finset.sum_involution`,
`Finset.erase_right_comm`) and `Φ_σ(syzygy)=1` by `srFaceDetector_prod`.

### Lean progress — UNIFORM hollow-simplex non-boundary (whole reduced-cohomology tower) [MILESTONE]

`srHollowSimplexSyzygy_not_koszulBoundary` (in `StanleyReisnerVertexRelation`, axiom-clean,
UNCONDITIONAL) is the general capstone for the Hochster `Tor₁` classes at every dimension:

For any nonface `σ` all of whose codimension-one faces `σ∖i` are faces (a minimal nonface = hollow
simplex `∂Δ^{|σ|−1}`) and any `a ∈ σ`, the syzygy `(∏_{w∈σ∖a} x_w)·eₐ` is **not** a first Koszul
boundary — a nonzero class of `Tor_{1,σ} = H̃^{|σ|−2}(Δ_σ)`.  Proof: the alternating(all-plus) detector
`Φ_σ(s) = ∑_{i∈σ} srFaceDetector(σ∖i)(sᵢ)` (built from the general face detector) evaluates to `1` on
the syzygy (`srFaceDetector_prod`) and to `0` on every boundary — its double sum over ordered pairs
cancels by the `(i,j)↔(j,i)` involution (`antisym_sigma_sum_zero` via `Finset.sum_involution` +
`Finset.erase_right_comm`), unconditionally (no characteristic-2 obstruction).

This single theorem realizes the **whole tower** `H̃⁰, H̃¹, H̃², …` of reduced simplicial cohomology as
nonzero first-Koszul-homology (Hochster `Tor₁`) classes, uniformly over all finite complexes.  With
the earlier general cycle, general nonface relation, descended detectors (all faces), product rule,
boundary helper, `d₁∘d₂=0`, and the 1-skeleton bridge, the `Tor₁` layer of the Hochster strand
equivalence is now formalized in full generality.  The remaining open frontier is the complete
multigraded isomorphism `Tor_{i,σ} ≅ H̃^{|σ|−i−1}(Δ_σ)` for higher `i` (`Tor₂, Tor₃, …`).

### Lean progress — Tor₁ layer main theorem (packaged, all dimensions)

`srHollowSimplex_firstKoszulHomology_nonzero` (axiom-clean) packages the general `Tor₁` result: for a
minimal nonface `σ` (hollow simplex) and `a ∈ σ`, the syzygy `(∏_{w∈σ∖a} x_w)·eₐ` is a first Koszul
cycle that is not a boundary — a nonzero class in `Tor_{1,σ} = H̃^{|σ|−2}(Δ_σ)`.  Ranging over
`|σ| = n+2` this is the whole reduced-cohomology tower `H̃⁰, H̃¹, H̃², …` as nonzero Hochster `Tor₁`
classes; it subsumes the empty-triangle (`H̃¹`) main theorem.

This completes the `Tor₁` layer of the Hochster strand equivalence in Lean, unconditionally over all
finite complexes.  The deep remaining frontier is the higher-`i` layer (`Tor₂, Tor₃, …`) of the
multigraded isomorphism `Tor_{i,σ} ≅ H̃^{|σ|−i−1}(Δ_σ)`, which needs the higher Koszul differentials
`d₃, d₄, …` (with their delicate alternating `d²=0`) — genuinely new homological infrastructure absent
from mathlib.

### Lean progress — third Koszul differential + d₂∘d₃=0 (Tor₂ foundation)

`srKoszulBoundary_srKoszulBoundary3` (in `StanleyReisnerVertexRelation`, axiom-clean) extends the
Koszul complex to degree three: for an `IsAlternating3` 3-tensor `b`, the second differential of the
third differential vanishes (`srKoszulBoundary (srKoszulBoundary3 b) = 0`), so the second Koszul
homology `Tor₂ = ker d₂ / im d₃` is a well-defined subquotient.

- `IsAlternating3` — the alternating 3-tensor predicate (antisymmetric under adjacent transpositions,
  vanishing on repeated indices).
- `srKoszulBoundary3` — the third differential `d₃(b)_{ij} = ∑_k b_{ijk} x_k`.
- `antisym_prod_sum_zero` — reusable helper: an antisymmetric, zero-diagonal function summed over
  `σ × σ` vanishes by the `Prod.swap` involution.

The proof: `d₃(b)` is antisymmetric, and each `∑_{j,k} b_{ijk} x_k x_j = 0` by the `(j,k)↔(k,j)`
involution (alternating coefficients vs symmetric products), so `d₂∘d₃` collapses — unconditional.
Next: a `Tor₂` class — the `4`-cycle `C₄` hole (`H̃¹` at `|σ|=4` = `Tor_{2,{a,b,c,d}}`) as an element
of `ker d₂ ∖ im d₃`, and its non-boundary via a `Tor₂` detector.

### Lean progress — first Tor₂ cycle (C₄ 4-cycle hole)

`srKoszulBoundary_c4Cycle` (in `StanleyReisnerVertexRelation`, axiom-clean) constructs the first
second-Koszul-homology representative: on the square `C₄` (`a–b–c–d–a`, diagonals `{a,c}`, `{b,d}`
absent), the syzygy `c_{ab} = x_c x_d`, `c_{cd} = x_a x_b` is annihilated by the second differential
(`srKoszulBoundary (c4Cycle …) = 0`), because every boundary term carries an absent-diagonal product
`x_a x_c` or `x_b x_d`, which vanishes.  Modulo `im d₃` this represents `Tor_{2,{a,b,c,d}} = H̃¹(C₄)` —
`H̃¹` reached at `Tor₂` rather than `Tor₁`, the first genuinely second-degree Koszul homology.

Combined with the `d₂∘d₃=0` foundation, the `Tor₂` layer now has both the well-definedness of the
homology and an explicit nonzero-candidate cycle.  Next: the `C₄` **non-boundary** (`c4Cycle ∉ im d₃`)
via a `Tor₂` detector, establishing it as a genuinely nonzero `Tor₂` class.

### Lean progress — Tor₂ antisymmetry + char-2 correction + unconditional representative

Two additions to `StanleyReisnerVertexRelation` (both axiom-clean):

1. `srKoszulBoundary3_antisymm` — `d₃` of an alternating 3-tensor is an antisymmetric 2-tensor, so
   `im d₃` lands in the alternating part `K₂` (the correct home for `Tor₂` representatives).

2. `srSquareEdgeCycle` + `srKoszulBoundary_srSquareEdgeCycle` — the single-edge syzygy
   `c_{ab} = x_c x_d` (all other entries zero) is a `d₂`-cycle in every characteristic.

**Char-2 correction (honesty).**  The earlier two-edge representative `c4Cycle` `(1,0,1,0)` is a
`d₂`-cycle unconditionally, but its `Tor₂` *class* is nonzero only away from characteristic two: solving
`(1,0,1,0) ∈ im d₃` over the edge basis forces `2 = 0`, so it is a boundary in char 2 (verified
numerically: in `im d₃` over `GF(2)`, not over `GF(3)`).  The **single edge** `(1,0,0,0)` instead forces
`0 = 1` in *every* field, so `srSquareEdgeCycle` is the unconditional `Tor₂` representative.  The
`c4Cycle` docstring is corrected accordingly.

Next: the unconditional non-boundary `srSquareEdgeCycle ∉ im d₃` via the alternating detector
`Φ = +{cd}∘c_{ab} − {ad}∘c_{bc} + {ab}∘c_{cd} − {bc}∘c_{da}` (`Φ(single edge) = 1`, `Φ(d₃ b) = 0`).

### Lean progress — MILESTONE: nonzero Tor₂ class (C₄ hole), unconditional

The `Tor₂` layer of the Hochster strand equivalence now has a genuine nonzero class, formalized
unconditionally (all axiom-clean, in `StanleyReisnerVertexRelation`):

- `srPairDetector_srKoszulBoundary3` — the degree-two detector of a `d₃`-entry collapses to two
  degree-one detectors (`srH0Det_v(b_{iju}) + srH0Det_u(b_{ijv})`) by the pair-product rule.
- `srSquareEdgeCycle_not_koszulBoundary3` — **the single-edge `C₄` cycle is not a `d₃`-boundary of any
  alternating 3-tensor, in every characteristic.**  The alternating detector `Φ = +{cd}∘t_{ab} −
  {ad}∘t_{bc} + {ab}∘t_{cd} − {bc}∘t_{da}` gives `Φ(cycle) = 1`, while `Φ(d₃ b) = 0`: the eight
  degree-one detector terms pair off by the cyclic (even-permutation) invariance of the alternating
  coefficient (`b_{bca} = b_{abc}`, `b_{dab} = b_{abd}`, `b_{cdb} = b_{bcd}`, `b_{dac} = b_{cda}`).  A
  boundary would force `1 = 0`.
- `srSquareEdge_secondKoszulHomology_nonzero` — packaged capstone: cycle (`d₂` kills it) ∧ non-boundary
  (`∉ im d₃`), so `srSquareEdgeCycle` represents a nonzero class in `Tor_{2,{a,b,c,d}} = H̃¹(C₄)`.

This is the first genuinely second-degree Hochster homology in the corpus, and it closes the char-2 gap
found last fire (the unconditional single-edge representative, not the char-2-vanishing two-edge sum).
Next: `Tor₃` (the tetrahedron-boundary `S²` class via the fourth Koszul differential `d₄`, `d₃∘d₄=0`),
or the general strand equivalence `Tor_{i,σ} ≅ H̃^{|σ|−i−1}` for arbitrary `i`.

### Lean progress — fourth Koszul differential + d₃∘d₄=0 (Tor₃ foundation)

`srKoszulBoundary3_srKoszulBoundary4` (in `StanleyReisnerVertexRelation`, axiom-clean) extends the
Koszul complex to degree four: for an `IsAlternating4` 4-tensor `b`, the third differential of the
fourth differential vanishes (`srKoszulBoundary3 (srKoszulBoundary4 b) = 0`), so the third Koszul
homology `Tor₃ = ker d₃ / im d₄` is a well-defined subquotient.

- `IsAlternating4` — the alternating 4-tensor predicate (antisymmetric under adjacent transpositions,
  vanishing on repeated indices).
- `srKoszulBoundary4` — the fourth differential `d₄(b)_{ijk} = ∑_l b_{ijkl} x_l`.

The composite is `∑_{k,l} b_{ijkl} xₗxₖ`, killed by the same `(k,l)↔(l,k)` involution
(`antisym_prod_sum_zero`) as `d₂∘d₃` — and cleaner, since `d₃` needs no internal antisymmetrization.
The pattern `d_{p-1}∘d_p = 0` now holds concretely for `p = 2, 3, 4` via one uniform involution.

Next: a `Tor₃` class — the pentagon `C₅` (`H̃¹` at `|σ|=5` = `Tor_{3}`) as a 3-cycle `∉ im d₄`, via a
degree-three alternating detector (the `Tor₂` construction one level up); or the general
`d_{p-1}∘d_p=0` unification over `Fin p → α` tensors.

### Lean progress — Tor₃ foundation complete (im d₄ ⊆ K₃)

`srKoszulBoundary4_alternating` (in `StanleyReisnerVertexRelation`, axiom-clean): `d₄` of an
alternating 4-tensor is an alternating 3-tensor (`IsAlternating3 (srKoszulBoundary4 b)`), so `im d₄`
lands in the alternating part `K₃` of the Koszul complex — the correct home for `Tor₃` representatives.
Each of the three alternation fields reduces to the corresponding field of the 4-tensor termwise
(`antisym12`/`antisym23` via `eq_neg_of_add_eq_zero_left` + `Finset.sum_add_distrib`; `alt` via
`Finset.sum_eq_zero` with the repeat pushed into the summand).

Together with `d₃∘d₄=0` this completes the `Tor₃` **foundation**, exactly parallel to the `Tor₂`
foundation (`d₂∘d₃=0` + `srKoszulBoundary3_antisymm`).

Next: a `Tor₃` class — the pentagon `C₅` (`H̃¹` at `|σ|=5`) or a disconnected 4-vertex complex (`H̃⁰`
at `|σ|=4`, the top strand) as a 3-cycle `∉ im d₄`, via a degree-three detector; or the general
`d_{p-1}∘d_p=0` over `Fin p → α` tensors (the `Fin.snoc` swap identity is the crux — heavy, deferred).

### Lean progress — MILESTONE: nonzero Tor₃ class (C₅ pentagon hole), unconditional

The `Tor₃` layer now has a genuine nonzero class, formalized unconditionally (all axiom-clean, in
`StanleyReisnerVertexRelation`):

- `srKoszulBoundary3_srPentTripleCycle` — the single-entry pentagon syzygy `c_{abc} = x_d x_e` is a
  third Koszul cycle (its only boundary term `x_c x_d x_e` hits the absent diagonal `{c,e}`).
- `srPairDetector_srKoszulBoundary4` — the degree-two detector of a `d₄`-entry collapses to two
  degree-one detectors.
- `srPentTripleCycle_not_koszulBoundary4` — **the single-entry `C₅` cycle is not a `d₄`-boundary of any
  alternating 4-tensor, in every characteristic.**  The **all-ones** edge detector `Φ = ∑_{5 edges}
  {opposite pair}∘t_{triple}` (odd cycle → unsigned, unlike `C₄`'s alternating detector) gives
  `Φ(cycle) = 1`, `Φ(d₄ b) = 0`: the ten degree-one detector terms pair off by the odd-permutation
  antisymmetry of the alternating coefficient (`b_{cdeb} = −b_{bcde}`, …, each a 1–5 step transposition
  chain).  A boundary would force `1 = 0`.  (Numerically pre-certified non-boundary over `GF(2,3,5,7)`.)
- `srPentTriple_thirdKoszulHomology_nonzero` — packaged capstone: cycle ∧ non-boundary, so
  `srPentTripleCycle` represents a nonzero class in `Tor_{3,{a,b,c,d,e}} = H̃¹(C₅)`.

This is the first third-degree Hochster homology in the corpus.  The cycle family `C_n → Tor_{n−2}`
(`H̃¹` at `|σ|=n`) is now formalized for `n = 4` (`Tor₂`) and `n = 5` (`Tor₃`).

Next: `Tor₄` (`C₆ → H̃¹`) via `d₅`, `d₄∘d₅=0`, and a degree-four detector; or the general
`C_n → Tor_{n−2}` family / general strand equivalence.

### Lean progress — Tor₄ foundation (d₄∘d₅=0 + im d₅ ⊆ K₄)

Two additions to `StanleyReisnerVertexRelation` (both axiom-clean), extending the vertex Koszul complex
to degree five:

- `IsAlternating5` / `srKoszulBoundary5` — the alternating 5-tensor predicate and the fifth
  differential `d₅(b)_{ijkl} = ∑_m b_{ijklm} x_m`.
- `srKoszulBoundary4_srKoszulBoundary5` — **`d₄∘d₅=0`**: the composite `∑_{l,m} b_{ijklm} xₘxₗ` cancels
  by the `(l,m)↔(m,l)` involution, so `Tor₄` is a well-defined subquotient.
- `srKoszulBoundary5_alternating` — **`im d₅ ⊆ K₄`**: `d₅` of an alternating 5-tensor is alternating.

The vertex Koszul complex is now `K₀ ← K₁ ← K₂ ← K₃ ← K₄ ← K₅`, with `d_{p-1}∘d_p = 0` verified for
`p = 2,3,4,5` (one uniform involution) and `im d_p ⊆ K_{p-1}` at every level.  This completes the `Tor₄`
foundation, ready for the hexagon `C₆` class (`H̃¹` at `|σ|=6`).

Next: the `Tor₄` class — `C₆` single-entry 4-tensor cycle `∉ im d₅` via a degree-four detector
(even cycle → alternating detector, matching `C₄`; numerically pre-certify first).  The module is at
1200 lines, so a split by Tor-degree is the housekeeping step to take alongside the next class.

### Lean progress — module split + C₆ Tor₄ cycle

Housekeeping + progress:

- **Module split.**  `StanleyReisnerVertexRelation.lean` (was 1200 lines) split into infrastructure +
  `Tor₁` (890 lines) and a new `StanleyReisnerCycleClasses.lean` (383 lines) holding the concrete
  cycle-graph classes (`C₄` `Tor₂`, `C₅` `Tor₃`, `C₆` cycle).  Both build green, axiom-clean; the split
  is behaviour-preserving (no external references to the moved declarations).
- `srPairDetector_srKoszulBoundary5` — the `d₅` detector pushthrough (degree-two detector of a
  `d₅`-entry → two degree-one detectors), the helper for the `C₆` non-boundary.
- `srKoszulBoundary4_srHexTupleCycle` — the single-entry hexagon syzygy `c_{abcd} = x_e x_f` is a fourth
  Koszul cycle (its only boundary term `x_d x_e x_f` hits the absent diagonal `{d,f}`).  Modulo `im d₅`
  this represents `Tor_{4,{a,b,c,d,e,f}} = H̃¹(C₆)`.

Next: the `C₆` **non-boundary** (`srHexTupleCycle ∉ im d₅`) via the degree-four detector — even cycle,
so an **alternating** edge detector (matching `C₄`, unlike `C₅`'s all-ones); numerically pre-certify
the representative and detector signs first.

### Lean progress — MILESTONE: nonzero Tor₄ class (C₆ hexagon hole), unconditional

The `Tor₄` layer now has a genuine nonzero class (all axiom-clean, in `StanleyReisnerCycleClasses`):

- `srHexTupleCycle_not_koszulBoundary5` — **the single-entry `C₆` cycle is not a `d₅`-boundary of any
  alternating 5-tensor, in every characteristic.**  Detector `Φ = +ab+bc+cd+de+ef−fa` (even cycle: a
  single sign flip on `fa`, forced by the two 5-cycle pairings among the twelve degree-one detector
  terms; the other four pairings are transpositions).  `Φ(cycle)=1`, `Φ(d₅ b)=0` via six permutation
  relations (`b_{cdefb}=b_{bcdef}`, `b_{adefc}=−b_{cdefa}`, … chains of 1–7 adjacent transpositions),
  then `simp[map_neg]; abel`.  Numerically pre-certified over `GF(2,3,5,7)`.
- `srHexTuple_fourthKoszulHomology_nonzero` — packaged capstone: cycle ∧ non-boundary, a nonzero class
  in `Tor_{4,{a,b,c,d,e,f}} = H̃¹(C₆)`.

The cycle family `C_n → Tor_{n−2}` (`H̃¹` at `|σ|=n`) is now formalized for `n = 4,5,6` — `Tor₂,Tor₃,Tor₄`
— with the detector-sign pattern (`C₄` alternating, `C₅` all-ones, `C₆` one-flip) understood via the
5-cycle-vs-transposition parity of the pairings.

Next: the general `C_n → Tor_{n−2}` family in one uniform theorem (over `Fin p → α` tensors), or `Tor₅`
via `C₇`; the vertex Koszul complex now runs `K₀ ← … ← K₅` with `d²=0` throughout.

### Lean progress — GENERAL d²=0 (degree-uniform Koszul backbone)

`GeneralKoszulComplex.lean` (new, axiom-clean) gives the Koszul complex `d²=0` at **every** degree in a
single theorem, no longer degree by degree:

- `cons_cons_comp_swap` — the leading-pair swap identity `k ∷ l ∷ u = (l ∷ k ∷ u) ∘ swap 0 1` (the
  previously-blocking `Fin` lemma, cracked with `Fin.cases` on positions `0,1` and `swap_apply_*`).
- `koszulD` — the general Koszul differential of an arbitrary commuting family `x : α → S` in any
  commutative ring, on index-tensors `(Fin p → α) → S`, prepending the contracted index:
  `d(b)(w) = ∑_k b(k ∷ w) x_k`.
- `koszulD_koszulD_eq_zero` — **`d² = 0`** for any tensor antisymmetric under, and vanishing on, an
  equal leading pair: the composite `∑_{k,l} b(l ∷ k ∷ u) x_l x_k` cancels by the same `(k,l)↔(l,k)`
  involution (`antisym_prod_sum_zero`) used at each concrete degree, the swap identity supplying the
  sign.  Unconditional, all characteristics, all `p`.

This is the degree-uniform backbone behind `srKoszulBoundary,…,srKoszulBoundary5` and their pairwise
`d²=0` laws — the whole vertex Koszul complex is a chain complex at every degree in one statement, over
any commuting family (not just Stanley–Reisner vertex coordinates).

Next: connect the concrete curried differentials to `koszulD` (a representation bridge), or the general
`C_n → Tor_{n−2}` family; the full Hochster iso `Tor_i ≅ H̃^{|W|−i−1}` remains the deep capstone.

### Lean progress — general single-entry Koszul cycle criterion

`koszulD_koszulSingleEntry_eq_zero` (in `GeneralKoszulComplex`, axiom-clean) gives the degree-uniform
cycle criterion complementing the general `d²=0`:

- `koszulSingleEntry v₀ r` — the one-entry index-tensor (value `r` at tuple `v₀`, zero elsewhere).
- `koszulD_koszulSingleEntry_eq_zero` — **a single-entry tensor is a Koszul cycle exactly when
  `r · x_{v₀ 0} = 0`**: every boundary term sits at the truncated tuple `Fin.tail v₀` and reads off
  `r · x_{v₀ 0}` (via `Fin.cons_self_tail` / `Fin.tail_cons`), so the differential vanishes iff that
  single product does.

This is the general form of the concrete cycles `srSquareEdgeCycle, srPentTripleCycle, srHexTupleCycle`
(where `r` is a two-vertex product and `r · x_{v₀ 0}` is an absent-diagonal monomial of the cycle
graph) — the "easy direction" of every `C_n → Tor_{n−2}` class now proved once, for all degrees, over
any commuting family.

Next: the general non-boundary is the remaining piece, but its detector signs are `n`-parity dependent
(`C₄` alternating, `C₅` all-ones, `C₆` one-flip), so a uniform statement needs the sign law; or the
full Hochster iso.

### Lean progress — general Koszul complex is a chain complex on alternating tensors

`GeneralKoszulComplex.lean` now exhibits the vertex Koszul complex as a bona-fide chain complex on
alternating index-tensors (all axiom-clean):

- `cons_comp_swap` — prepend-shift of a transposition: `k ∷ (v ∘ swap i j) = (k ∷ v) ∘ swap i⁺ j⁺`
  (via mathlib `Function.Injective.map_swap`).
- `IsAltTensor` — alternating index-tensor: sign-reversing under every positional transposition and
  vanishing on non-injective tuples.
- `koszulD_isAltTensor` — **`koszulD` preserves alternation**: prepending conjugates each transposition
  (transporting the sign) and a repeated index survives the prepend (transporting the vanishing).
- `koszulD_koszulD_eq_zero_of_isAltTensor` — **`d²=0` on the alternating complex**: for alternating `b`
  the leading-pair hypotheses hold automatically, so the differential squares to zero.

So the general vertex Koszul complex (over any commuting family, any commutative ring, all degrees, all
characteristics) is a genuine chain complex on alternating tensors — `Tor` is well-defined at every
degree in a single uniform statement, no longer degree by degree.

Next: define the general homology `Tor = ker/im` and connect to the concrete classes, or the full
Hochster iso `Tor_i ≅ H̃^{|W|−i−1}`.

### Lean progress — module/map layer for general Koszul homology

`GeneralKoszulComplex.lean` now carries the linear-algebra layer needed to take `Tor` (all axiom-clean):

- `koszulDₗ` — the Koszul differential packaged as an `S`-linear map `((Fin (p+1)→α)→S) →ₗ[S]
  ((Fin p→α)→S)`.
- `koszulAltTensors p` — the alternating index-tensors as an `S`-submodule of all `p`-tensors (closed
  under `+`, `•`, `0` via the `IsAltTensor` fields).
- `koszulDₗ_mem_koszulAltTensors` — `koszulDₗ` carries the alternating submodule into the alternating
  submodule, so it restricts to a differential `koszulAltTensors (p+1) → koszulAltTensors p`.

Together with `koszulD_koszulD_eq_zero_of_isAltTensor` (`d²=0` on the alternating complex), the pieces
for the homology `Tor_p := ker ⧸ im` are now in place as genuine `S`-modules and `S`-linear maps.

Next: assemble the restricted differential and the `Tor = ker/im` quotient module (the homological-
algebra API needs care — `LinearMap.restrict` on these submodules stalled instance resolution this
fire), or the full Hochster iso `Tor_i ≅ H̃^{|W|−i−1}`.

### Lean progress — general Koszul homology Tor as an S-module

`GeneralKoszulComplex.lean` now defines the general vertex-Koszul `Tor` and characterizes nonzero
classes (all axiom-clean):

- `koszulCycles` / `koszulBoundaries` — degree-`(p+1)` cycles (`ker koszulDₗ ⊓` alternating) and
  boundaries (`Submodule.map koszulDₗ` of the alternating `(p+2)`-tensors), as `S`-submodules.
- `koszulBoundaries_le_koszulCycles` — **boundaries are cycles** (`d²=0` + `koszulD_isAltTensor`), so
  the homology is a well-defined subquotient.
- `koszulTor` — the degree-`(p+1)` Koszul homology `koszulCycles ⧸ koszulBoundaries` as an `S`-module —
  the general vertex-Koszul `Tor` whose graded pieces Hochster's formula identifies with `H̃`.
- `koszulTor_mk_ne_zero` — **a cycle's `Tor` class is nonzero iff it is not a boundary** — the exact
  module statement behind every concrete non-boundary theorem (`srSquareEdgeCycle_not_…`, etc.).

So the card's object `Tor_i^R(M_Δ,k)` now exists as a genuine Lean `S`-module (in the general vertex
Koszul representation), with the homology well-defined and its nonzero classes characterized.

Next: the representation bridge, so the concrete `Tor₁–₄` non-boundaries populate `koszulTor` with
explicit nonzero classes; or the Hochster iso `koszulTor ≅ H̃` (the deep capstone).

### Lean progress — degree-1 bridge: general koszulD recovers the concrete SR Koszul relation

`koszulD_srVertexX_eq_srKoszulRelation` (in `GeneralKoszulComplex`, axiom-clean) connects the general
vertex-Koszul framework to the concrete Stanley–Reisner differentials: over the SR ring, with the
vertex coordinates as the commuting family, the general Koszul differential `koszulD` in degree one is
exactly the concrete first Koszul relation `srKoszulRelation` (`∑_v a_v x_v`).

The two conventions coincide in degree one because there are no index pairs to antisymmetrize — the
general `koszulD` (prepend/alternating) and the concrete `srKoszulBoundary` family (append/antisymmetrize)
agree there, though they differ by a characteristic-sensitive factor at higher degree.  So the general
`koszulTor` at degree 1, over the SR ring, IS the concrete first Koszul homology (`Tor₁`), now linked
by an explicit identity rather than by analogy.

Next: higher-degree bridges need the convention reconciliation (a reindexing/sign map); or the full
Hochster iso `koszulTor ≅ H̃^{|W|−i−1}` (the deep capstone).

### Lean progress — general koszulTor populated with a concrete nonzero class

`GeneralKoszulComplex.lean` now proves the general vertex-Koszul homology is genuinely nontrivial over
the Stanley–Reisner ring (all axiom-clean):

- `srDisconnectKoszulCycle` — the degree-one disconnect cycle (single-entry `x_w` at the tuple `(v₀)`).
- `srDisconnectKoszulCycle_mem_koszulCycles` — it is a Koszul cycle (`x_w x_{v₀}=0` on a nonface pair;
  alternation vacuous in degree one).
- `srDisconnectKoszulCycle_not_mem_koszulBoundaries` — it is not a boundary: the two-point detector
  `Φ(t)=srH0Det_w(t(v₀))+srH0Det_{v₀}(t(w))` reads the cycle as `1` and every `koszulD`-boundary as `0`
  (the two constant-term readings `srConstTerm(b_{w,v₀})` and `srConstTerm(b_{v₀,w})=−srConstTerm(b_{w,v₀})`
  cancel by alternation).
- `srDisconnectKoszulTor_ne_zero` — **the disconnect cycle represents a nonzero class in `koszulTor`** —
  the abstract homology module is populated with an explicit nonzero element, realizing `H̃⁰` of a
  disconnected pair as an actual general-`Tor` class.

So `koszulTor` is not just defined but proven non-vacuous, connected to a concrete cycle via
`koszulTor_mk_ne_zero`.  The general vertex-Koszul side — complex, homology module, characterization,
and a concrete nonzero class — is complete.

Next: higher-degree nonzero `koszulTor` classes (the `C_n` cycles via the general framework), or the
full Hochster iso `koszulTor ≅ H̃^{|W|−i−1}`.

### Lean progress — general antisymmetrization operator

`GeneralKoszulComplex.lean` now carries the reusable tool for producing alternating tensors at any
degree (axiom-clean):

- `koszulAlt t = ∑_σ sign(σ) • t(· ∘ σ)` — the antisymmetrization of an index-tensor over the
  permutation group `Perm (Fin p)`.
- `koszulAlt_isAltTensor` — **`koszulAlt t` is always alternating**: sign reversal follows from
  reindexing the permutation sum by a transposition (`Fintype.sum_bijective` on `σ ↦ (i j)·σ` +
  `sign_swap`), and vanishing on a repeated index from the fixed-point-free involution `σ ↦ (i j)·σ`
  pairing off equal-magnitude opposite-sign contributions (`Finset.sum_involution`).

This turns *any* tensor into an alternating one — the uniform source of alternating Koszul cycles at
every degree, so higher-degree `koszulTor` classes can be built as `koszulAlt` of a single-entry tensor
rather than by bespoke case analysis.

Next: use `koszulAlt (koszulSingleEntry …)` to lift the `C_n` cycles into `koszulTor` at degrees ≥ 2,
giving higher-degree nonzero classes; or the Hochster iso.

### Lean progress — degree-2 antisymmetrization formula

`koszulAlt_two_apply` (in `GeneralKoszulComplex`, axiom-clean): over `Perm (Fin 2) = {1, (0 1)}`, the
antisymmetrization reduces to the two-term form `koszulAlt t = t − t(· ∘ (0 1))` (the permutation sum
enumerated via `decide` + `Finset.sum_pair`).

This makes `koszulAlt (koszulSingleEntry ![a,b] r)` computable as the explicit two-entry alternating
tensor (`r` at `![a,b]`, `−r` at `![b,a]`), the `C₄` `Tor₂` cycle in the general framework — with its
alternation supplied for free by `koszulAlt_isAltTensor`.

Next: assemble the degree-2 `C₄` `koszulTor` class — `koszulAlt (koszulSingleEntry ![a,b] (x_c x_d))`
as a cycle (`koszulD = 0` via the two-term form + `koszulD_koszulSingleEntry_eq_zero` on each entry)
and non-boundary (degree-2 detector), giving the first higher-degree nonzero `koszulTor` class; the
`Fin 2` tuple-swap helpers (`![a,b] ∘ (0 1) = ![b,a]`) are the remaining plumbing.

### Lean progress — degree-2 C₄ cycle in the general koszulTor framework

`GeneralKoszulComplex.lean` now carries the `C₄` `Tor₂` cycle in the general (Fin-tensor) framework
(all axiom-clean), demonstrating the antisymmetrization tool at work:

- `srC4KoszulCycle = koszulAlt (koszulSingleEntry ![a,b] (x_c x_d))` — the `C₄` degree-two cycle, whose
  alternation is supplied for free by `koszulAlt_isAltTensor`.
- `srC4KoszulCycle_eq` — it equals the explicit two-entry tensor (`x_c x_d` at `![a,b]`, `−x_c x_d` at
  `![b,a]`), via the degree-two antisymmetrization formula + the `Fin 2` tuple-swap `![a,b] ∘ (0 1) =
  ![b,a]`.
- `koszulD_srC4KoszulCycle` — it is a Koszul cycle: written as `single ![a,b] − single ![b,a]`,
  `koszulD` is linear and kills each entry (`koszulD_koszulSingleEntry_eq_zero`, the boundary products
  `x_a x_c` and `x_b x_d` absent).
- `srC4KoszulCycle_mem_koszulCycles` — so it lies in the degree-two Koszul cycles `koszulCycles`.

This is the first *higher*-degree cycle built via `koszulAlt (koszulSingleEntry …)` rather than bespoke
case analysis — the alternation is automatic, and only the `Fin 2` swap plumbing was needed.

Next: the `C₄` non-boundary (degree-two `srPairDetector`, the analogue of the concrete `C₄` cancellation
lifted to `koszulD`), giving the first higher-degree nonzero `koszulTor` class; or the Hochster iso.

### Lean progress — permutation-sign law + koszulD pair-detector pushthrough

Two reusable infrastructure lemmas for the general higher-degree non-boundaries (both axiom-clean):

- `IsAltTensor.comp_perm` — **alternating tensors transform by the sign under any permutation**:
  `b(v ∘ σ) = sign(σ) • b(v)`, by induction on `σ` as a product of transpositions
  (`Equiv.Perm.swap_induction_on` + `swap_neg`).  This turns every cyclic-permutation identity
  (`b(![c,a,b]) = b(![a,b,c])`, sign of a 3-cycle `= 1`) into a one-liner, replacing bespoke swap chains.
- `srPairDetector_koszulD` — the pair detector of a `koszulD`-entry over the Stanley–Reisner ring
  collapses to two degree-one detectors: `srPairDetector_{u,v}(koszulD b (w)) = srH0Det_v(b(u∷w)) +
  srH0Det_u(b(v∷w))` (the Fin-representation analogue of `srPairDetector_srKoszulBoundary4`).

Together these are the machinery for the `C₄` non-boundary: the detector `Φ(t) = ∑ {opp pair}∘t_{edge}`
evaluates `srC4KoszulCycle` to `1` and every `koszulD`-boundary to `0` (the eight degree-one terms pair
off by `comp_perm` with even 3-cycles).

Next: assemble `Φ`, prove `Φ(srC4)=1` and `Φ(koszulD b)=0`, giving the first higher-degree nonzero
`koszulTor` class (degree 2); or the Hochster iso.

### Lean progress — degree-2 nonzero koszulTor class (C₄) complete in the general framework

The degree-2 `C₄` example is now closed end-to-end in the general vertex-Koszul framework (all
axiom-clean `[propext, Classical.choice, Quot.sound]`):

- `srC4KoszulCycle_not_mem_koszulBoundaries` — the `C₄` edge cycle is **not** a `koszulD`-boundary of
  any alternating 3-tensor, in every characteristic.  The edge detector
  `Φ(t) = +{cd}∘t_{ab} − {ad}∘t_{bc} + {ab}∘t_{cd} − {bc}∘t_{da}` reads the cycle as `1`
  (via `srC4KoszulCycle_eq` + `srPairDetector_srVertexX_mul`) and every boundary as `0`: after
  `srPairDetector_koszulD` the eight degree-one detector terms pair off into four cancellations, each
  discharged by the even-3-cycle permutation invariance `IsAltTensor.comp_perm` of the alternating
  coefficient (`sign` of a 3-cycle `= 1`).
- `srC4KoszulTor_ne_zero` — packaged capstone: the `C₄` edge cycle represents a **nonzero class in
  `koszulTor`**, the first higher-degree nonzero class of the *general* vertex-Koszul homology
  (realizing `H̃¹(C₄) = Tor₂`), connected through `koszulTor_mk_ne_zero` and
  `srC4KoszulCycle_mem_koszulCycles`.

This upgrades the general framework from "has a degree-1 nonzero class (disconnect) + a degree-2
*cycle*" to "has a degree-2 *nonzero homology class* built entirely from `koszulAlt(koszulSingleEntry)`
+ automatic alternation" — no bespoke case analysis, unlike the curried `Tor₂` tower.

Next: the same recipe at degree 3 (`C₅` nonzero `koszulTor` via a triple-detector pushthrough +
`comp_perm` 4/5-cycle cancellation); or the Hochster iso `koszulTor ≅ H̃`.

### Lean progress — topological side of Hochster's iso for C₄ (H̃¹) meets the algebraic Tor₂

New module `HTGeometry/HochsterCycleRealization.lean` bridges the two sides of Hochster's formula
`Torᵢ(k[Δ],k)_W ≅ H̃^{|W|−i−1}(Δ|W)` at the `C₄` instance (`i=2`, `|W|=4`, `H̃^{4−2−1}=H̃¹`).  The
`4`-cycle is one-dimensional, so its simplicial `H̃¹` is the graph reduced first cohomology already
built in `ReducedH1FirstBetti` (`finrank_reducedH1 = |E| − |V| + components`).  All axiom-clean:

- `card_connectedComponent_eq_one` — a connected finite graph has one component (reusable; every
  component is the class of a base vertex via `ConnectedComponent.ind` + `sound`).
- `finrank_reducedH1_cycleGraph4` — `dim H̃¹(C₄) = 4 − (4 − 1) = 1` (mathlib `cycleGraph 4` +
  `cycleGraph_connected`; `|orientedEdges| = 4` by `decide`).
- `reducedH1_cycleGraph4_nontrivial` — hence `H̃¹(C₄) ≠ 0`, the topological witness.
- `hochster_C4_both_nonzero` — the capstone: for any Stanley–Reisner realization of `C₄` (four distinct
  vertices, consecutive pairs edges, both diagonals non-faces) the **algebraic** `Tor₂`
  (`srC4KoszulTor_ne_zero`) and the **topological** `H̃¹(C₄)` are simultaneously nonzero — the concrete
  realization of the Hochster iso at this instance, both invariants one-dimensional.

This connects the general vertex-Koszul homology (algebraic) to the reduced simplicial cohomology
(topological) inside one Lean statement, moving the card from "algebraic side only" to "both sides
matched at `C₄`".

Next: a concrete `C₄` Stanley–Reisner complex instance (construct `facets`, discharge the face /
non-face hypotheses) to fully instantiate `hochster_C4_both_nonzero`; then the iso *map*
`koszulTor ≅ H̃`, or the same both-sides match for `Cₙ`.

### Lean progress — fully unconditional C₄ Hochster realization (concrete square complex)

`HochsterCycleRealization.lean` now carries a concrete, hypothesis-free instance:

- `c4Facets : Finset (Finset (Fin 4)) := {{0,1},{1,2},{2,3},{0,3}}` — the square complex (four sides as
  maximal faces).
- `c4_ac_not_face`, `c4_bd_not_face` — the two diagonals `{0,2}`, `{1,3}` are non-faces
  (`simp only [IsFaceOf, c4Facets, Finset.mem_coe]; decide`).
- `hochster_C4_realization (F) [Field F]` — instantiating `hochster_C4_both_nonzero` at `c4Facets`
  (all sixteen distinctness / face / non-face hypotheses discharged by `decide`), the **algebraic**
  `Tor₂` of the concrete `C₄` Stanley–Reisner ring and the **topological** `H̃¹(C₄)` are both nonzero
  **with no remaining hypotheses**.

This closes the `C₄` instance of Hochster's formula end-to-end: a self-contained Lean statement, over
any field, in which both sides of `Torᵢ(k[Δ],k)_W ≅ H̃^{|W|−i−1}(Δ|W)` are exhibited nonzero on a
concrete simplicial complex — no abstract facet hypotheses left open.

Next: upgrade "both nonzero" to the iso *map* `koszulTor ≅ H̃` (a linear equivalence, not just matched
nonvanishing); or the concrete unconditional realization for `Cₙ`.

### Lean progress — empty-triangle C₃ Hochster realization (the Tor₁ strand meets H̃¹)

`HochsterCycleRealization.lean` now also bridges the card's **primary first-Koszul hollow-simplex
strand** to topology (the C₄ realization used the *separate* general `koszulTor` `Tor₂`; this uses the
card's own `srEmptyTriangle` `Tor₁`).  All axiom-clean:

- `finrank_reducedH1_cycleGraph3` / `reducedH1_cycleGraph3_nontrivial` — `dim H̃¹(C₃) = 3 − (3−1) = 1`,
  hence nonzero (mathlib `cycleGraph 3` = triangle; `|orientedEdges| = 3` by `decide`).
- `hochster_C3_both_nonzero` — for any empty-triangle complex `{a,b,c}`, the algebraic `Tor₁` class
  `x_b x_c · e_a` (`srEmptyTriangle_firstKoszulHomology_nonzero`: a first Koszul cycle, not a boundary)
  and the topological `H̃¹(C₃)` are simultaneously nonzero — the `i=1`, `|W|=3` instance of
  `Torᵢ ≅ H̃^{|W|−i−1}`.
- `c3Facets := {{0,1},{1,2},{0,2}}` + `c3_abc_not_face` + `hochster_C3_realization` — the fully
  unconditional concrete instance (triangle-boundary complex, all hypotheses discharged).

Note the multigraded signature of Hochster's formula now visible in Lean: the *same* topological
invariant — `H̃¹` of a cycle — sits at **different** Tor degrees, `Tor₁` for `C₃` (`|σ|=3`) and `Tor₂`
for `C₄` (`|σ|=4`).  Both bridged, both unconditional.

Next: the exact-rank (upper-bound/spanning) at a fixed multidegree — e.g. `Tor₁` at `{a,b,c}` is
*exactly* one-dimensional (`Φ = D_bc + D_ac + D_ab` is an iso onto `F`) — the deep direction the card
names as open; or higher hollow simplices (need `H̃^{≥2}` simplicial cohomology topologically).

### Lean progress — EXACT first-Koszul rank at the empty triangle (degree-1 Hochster EQUALITY)

The deep-open "exact-rank / spanning upper bound" direction now has its first case, unconditional over
all finite complexes, in new module `HTGeometry/StanleyReisnerEmptyTriangleRank.lean` (axiom-clean).
This upgrades the empty-triangle result from *nonvanishing* (`srEmptyTriangleSyzygy_not_koszulBoundary`)
to the exact Hochster **equality**:

- `srEmptyTriangleSyzygyVec` — the three-parameter multidegree-`{a,b,c}` syzygy
  `w(λ) = λₐ·x_b x_c·eₐ + λ_b·x_a x_c·e_b + λ_c·x_a x_b·e_c`.
- `srKoszulBoundary_add`, `srKoszulBoundary_smul` — linearity of the first Koszul boundary in its
  `2`-chain (reusable).
- `srEmptyTriangleSyzygyVec_isCycle` — every `w(λ)` is a first Koszul cycle (each term is a multiple of
  `x_a x_b x_c = 0`).
- `srEmptyTriangleSyzygyVec_boundary_iff` — **the capstone**: `w(λ)` is a first Koszul boundary **iff**
  `λₐ+λ_b+λ_c = 0`.  Forward: the cyclic detector `Φ = D_bc+D_ac+D_ab` reads `w` as the coefficient sum
  and annihilates every boundary.  Reverse (the genuine *spanning* content): every sum-zero combination
  is `−λ_b·⟨a,b⟩⊗x_c − λ_c·⟨a,c⟩⊗x_b` as a boundary, via `srKoszulBoundary` linearity + the existing
  cyclic-homology β-lemma.

Consequence: the 3-dimensional cycle space collapses to a **1-dimensional** homology detected by the
coefficient sum — `Tor_{1,{a,b,c}} ≅ k = H̃¹(∂Δ²)` as an exact equality of ranks, not just both-nonzero.
This is the first instance of the card's "deep general Hochster identity (exact-rank match)".

Next: the same exact-rank at higher hollow simplices `∂Δ^{n}` (`|σ|=n+1`, using `srFaceDetector` +
the alternating spanning `2`-chain); or the multigraded statement that these syzygies exhaust the
degree-`σ` cycles, closing `Tor_{1,σ} = H̃^{|σ|−2}` as a full multigraded isomorphism.

### Lean progress — general hollow-simplex exact-rank core (β-lemma for all σ)

Toward the uniform (all-`|σ|`) exact-rank Hochster equality, new module
`HTGeometry/StanleyReisnerHollowSimplexRank.lean` builds the reusable core (axiom-clean), generalizing
last session's empty-triangle pieces from `|σ|=3` to every minimal nonface `σ`:

- `srHollowSimplexSyzygyVec facets σ l` — the `|σ|`-parameter multidegree-`σ` syzygy family
  `∑_{i∈σ} l_i (∏_{w∈σ∖i} x_w) e_i`.
- `srHollowSimplexSyzygyVec_isCycle` — every such syzygy is a first Koszul cycle (each term is a
  multiple of `∏_{w∈σ} x_w = 0`, via `Finset.prod_erase_mul` + `srProd_eq_zero_of_not_isFace`).
- `srHollowSyzygy_single_boundary` — **the general single-entry boundary lemma**: the first Koszul
  boundary of the `2`-chain `⟨i₀,k⟩ ⊗ ∏_{w∈σ∖{i₀,k}} x_w` equals the difference of the two basis
  syzygies `∏_{σ∖i₀}·e_{i₀} − ∏_{σ∖k}·e_k`.  This is the all-`σ` generalization of
  `srEmptyTriangle_cyclic_syzygy_homologous`, proved uniformly via `Finset.mul_prod_erase` /
  `prod_erase_mul` / `erase_right_comm`.

With this β-lemma, any two basis hollow-simplex syzygies are homologous, so the `|σ|`-dim syzygy space
already collapses toward the `1`-dim class — the exact spanning input.

Next: assemble the full exact-rank iff for general `σ` — `w(l)` is a boundary `↔ ∑_{i∈σ} l_i = 0` — via
finite additivity of `srKoszulBoundary` summing the β-lemma over `σ∖i₀` (`←`) and the uniform face
detector `Φ_σ = ∑_{i∈σ} srFaceDetector(σ∖i)` (`→`), closing `Tor_{1,σ} ≅ H̃^{|σ|−2}(∂Δ^{|σ|−1})` as an
exact rank equality in every dimension.

### Lean progress — UNIFORM hollow-simplex exact-rank iff (Hochster equality, every dimension)

The exact-rank Hochster equality now holds for **every** hollow simplex `σ` (all `|σ|`), completing the
uniform degree-`1` strand, in `HTGeometry/StanleyReisnerHollowSimplexRank.lean` (axiom-clean):

- `srHollowSimplexSyzygyVec_sum_zero_of_boundary` (`→`) — a boundary syzygy has coefficient sum zero,
  via the uniform face detector `Φ_σ = ∑_{i∈σ} srFaceDetector(σ∖i)` (reads `w(l)` as `∑_{i∈σ} l_i`,
  kills every boundary by the `(i,j)↔(j,i)` involution `antisym_sigma_sum_zero`).
- `srHollowSimplexSyzygyVec_boundary_of_sum_zero` (`←`) — every sum-zero syzygy is a boundary: fixing a
  base `i₀∈σ`, the `2`-chain `∑_{j∈σ∖i₀} −l_j·⟨i₀,j⟩⊗∏_{σ∖{i₀,j}} x` has boundary `w(l)` (the general
  spanning construction, using `Finset.sum_ite_mem`/`sum_smul`/`sum_neg_distrib`/`add_sum_erase` +
  `prod_erase_mul`).
- `srHollowSimplexSyzygyVec_boundary_iff` — **the capstone**: `w(l)` is a first Koszul boundary **iff**
  `∑_{i∈σ} l_i = 0`.

So for every minimal nonface `σ` the `|σ|`-parameter syzygy space collapses to **exactly one dimension**,
detected by the coefficient sum: `Tor_{1,σ} ≅ k = H̃^{|σ|−2}(∂Δ^{|σ|−1})` as an exact rank equality, in
every dimension — the uniform "deep general Hochster identity (exact-rank match)" the card names, now
proved for the whole first-Koszul hollow-simplex tower (`H̃⁰, H̃¹, H̃², …`) at once.

Next: upgrade the rank equality to a genuine module isomorphism (the multigraded statement that these
syzygies *exhaust* the degree-`σ` cycles); or the higher `Tor_{i≥2}` strands (cycles `Cₙ` needing higher
Koszul differentials).

### Lean progress — class-level exact 1-dimensionality + concrete C₃ exact Hochster iso

Two capstones on the uniform hollow-simplex exact-rank (axiom-clean):

- `srHollowSimplexSyzygyVec_sub` — the syzygy is `R`-linear in its coefficient family
  (`w(l) − w(l') = w(l − l')`).
- `srHollowSimplexSyzygy_homologous_iff` (in `StanleyReisnerHollowSimplexRank.lean`) — **the homology
  class of `w(l)` is determined exactly by `∑_{i∈σ} l_i`**: two hollow-simplex syzygies are homologous
  (differ by a first Koszul boundary) iff their coefficient sums agree.  Direct corollary of the
  boundary-iff + `w`-linearity — the exact one-dimensionality of `Tor_{1,σ}` at the class level.
- `hochster_C3_exact_rank` (in `HochsterCycleRealization.lean`) — **the exact Hochster iso at the
  concrete empty triangle**: the topological `H̃¹(C₃)` has dimension exactly `1`
  (`finrank_reducedH1_cycleGraph3`), and the algebraic multidegree-`{0,1,2}` syzygy space collapses
  exactly by the coefficient sum (`w(l)` a boundary `↔ ∑ l = 0`, via the uniform iff).  Both sides
  exactly one-dimensional — upgrading `hochster_C3_realization` from both-nonzero to
  **both-dimension-`1`**, the exact-rank Hochster equality on a concrete complex.

Next: the full module isomorphism `Tor_{1,σ} ≅ H̃^{|σ|−2}` (the multigraded statement that these
syzygies exhaust the degree-`σ` cycles); or the higher `Tor_{i≥2}` cycle strands (`Cₙ`).

### Lean progress — module-level exact rank (Koszul homology module + syzygy classes ≅ R)

Lifting the degree-`1` exact-rank from the Prop level (boundary-membership iffs) to the actual homology
*module*, in `StanleyReisnerHollowSimplexRank.lean` (axiom-clean):

- `srKoszulBoundaryₗ` — the first Koszul boundary map as an honest `R`-linear map on `2`-chains
  (`map_add'`/`map_smul'` from the boundary's additivity/homogeneity).
- `srKoszulBoundaries` — the boundaries submodule `= LinearMap.range srKoszulBoundaryₗ`, giving the
  first Koszul homology module `(α → S) ⧸ srKoszulBoundaries`.
- `srHollowSimplexSyzygy_mk_eq_zero_iff` — in that module, the class of a hollow-simplex syzygy `w(l)`
  is zero **iff** `∑_{i∈σ} l_i = 0`.
- `srHollowSimplexSyzygy_mk_eq_iff` — two syzygy classes coincide **iff** their coefficient sums agree.

Together: the hollow-simplex syzygy classes form a **copy of `R` inside `Tor_{1,σ}`**, parametrized by
the coefficient sum — the module-level statement of `Tor_{1,σ} ≅ H̃^{|σ|−2}(∂Δ^{|σ|−1})`, no longer just
a Prop-level rank equality.

Next: package this as an explicit `LinearEquiv R ≃ₗ (syzygy-class submodule)`; the multigraded statement
that these syzygies exhaust *all* degree-`σ` cycles (upgrading to the full `Tor_{1,σ} ≅ R`); or the
higher `Tor_{i≥2}` cycle strands.

### Lean progress — degree-1 Hochster iso as an explicit LinearEquiv (strongest form)

The degree-`1` exact rank now stands in its strongest form, an actual isomorphism of `R`-modules
(axiom-clean, in `StanleyReisnerHollowSimplexRank.lean`):

- `srHollowSimplexSyzygyVec_smul` — the syzygy is `R`-homogeneous (`r • w(l) = w(r • l)`).
- `srHollowBaseClass` — the base first-Koszul homology class (unit-coefficient syzygy `w(𝟙_{i₀})`).
- `srHollowBaseClass_toSpanSingleton_injective` — `r ↦ r • [base]` is injective (its kernel is
  `r = ∑_{i∈σ}(r·𝟙_{i₀})_i = 0`, from the module-level exact rank).
- `srHollowClassEquiv` — **`R ≃ₗ[R] R·[base class]`**: the hollow-simplex syzygy classes form a free
  rank-one `R`-module inside the first Koszul homology.  This is the isomorphism form of
  `Tor_{1,σ} ≅ H̃^{|σ|−2}(∂Δ^{|σ|−1})` — no longer a Prop-level iff or a rank equality, but a genuine
  `LinearEquiv`.

The degree-`1` hollow-simplex strand is now a complete package: nonzero classes → exact-rank iff →
class determined by coefficient sum → concrete C₃ topological match → homology module → and the
`R`-module isomorphism.

Next: the multigraded statement that these syzygies exhaust *all* degree-`σ` cycles (upgrading to the
full `Tor_{1,σ} ≅ R`); or the higher `Tor_{i≥2}` cycle strands (`Cₙ`).

### Lean progress — R is a direct summand of the first Koszul homology (detector retraction)

Companion to the base-class embedding: the uniform `σ`-detector descends to a *retraction* of the first
Koszul homology, exhibiting `R` as a direct summand of `Tor_{1,σ}` (axiom-clean, in
`StanleyReisnerHollowSimplexRank.lean`):

- `srHollowDetectorₗ` — `Φ_σ = ∑_{i∈σ} srFaceDetector(σ∖i)` as an `R`-linear functional on `1`-chains.
- `srHollowDetectorₗ_apply_boundary` — `Φ_σ` annihilates every first Koszul boundary (double sum over
  ordered pairs cancels by the `(i,j)↔(j,i)` involution, `antisym_sigma_sum_zero`).
- `srHollowDetectorTor` — hence `Φ_σ` descends to `Tor₁ = (α → S)⧸srKoszulBoundaries →ₗ[R] R`.
- `srHollowDetectorTor_base` — **the descended detector is `1` on the base syzygy class**, so it splits
  the base-class embedding `R → Tor₁`.  Together with `srHollowClassEquiv` this exhibits `R` as a
  *direct summand* of `Tor_{1,σ}`.

The degree-`1` hollow-simplex `Tor` now carries a full split copy of `R` (embedding + retraction), in
every dimension.

Next: the multigraded statement that these syzygies exhaust *all* degree-`σ` cycles (making the split
copy the whole `Tor_{1,σ}`); or the higher `Tor_{i≥2}` cycle strands.

### Lean progress — concrete C₃ degree-1 Hochster module iso (direct summand + topological finrank)

`hochster_C3_direct_summand` (in `HochsterCycleRealization.lean`, axiom-clean) ties the full degree-1
module machinery to the concrete empty triangle and its topology:

- **topological:** `dim H̃¹(C₃) = 1` (`finrank_reducedH1_cycleGraph3`);
- **algebraic:** the descended `σ`-detector `srHollowDetectorTor` is `1` on the base first-Koszul
  homology class (`srHollowDetectorTor_base`) — so, together with the embedding `srHollowClassEquiv`,
  `R` is a **direct summand** of the first Koszul homology of the concrete `c3Facets` complex.

Both sides realize the same rank-one `Tor_{1,{0,1,2}} ≅ H̃¹(∂Δ²)` at the module level — the concrete
capstone of the degree-1 hollow-simplex strand (nonzero → exact-rank → module iso → embedding →
retraction → direct summand → concrete match).

Deep frontiers (each needs substantial new infrastructure, not in mathlib): the fine multigrading of
`k[Δ]` for the exhaust `Tor_{1,σ} ≅ R` (whole degree-`σ` part, not just the syzygy summand); the higher
`Tor_{i≥2}` module structure (the general `koszulTor` is over `S = k[Δ]` with zero divisors, so its
scalar/torsion structure differs from the degree-1 base-ring `R`-module).

### Lean progress — fine multigrading of k[Δ]: degree-J graded piece = R·∏_J x (started)

Beginning the fine (per-multidegree) grading of the Stanley–Reisner ring that mathlib does not provide
(it has only total-degree `homogeneousComponent`) — the prerequisite for the multigraded exhaust
`Tor_{1,σ} ≅ R`.  New module `HTGeometry/StanleyReisnerMultigrading.lean` (axiom-clean):

- `srMk_smul` — the quotient map `k[x] → k[Δ]` is `R`-linear (via the `R`-algebra structure;
  `Ideal.Quotient.mk` as a `RingHom` needs this bridged through `Algebra.smul_def`).
- `srFaceDetector_smul_prod` — the face detector is a *retraction* onto `R·∏_J x`:
  `srFaceDetector J (r · ∏_J x) = r`.
- `srMk_homogeneous_eq` — **the graded-piece fact**: a degree-`J`-homogeneous element (lift supported
  on the single squarefree exponent `indicatorExponent J`) equals `(srFaceDetector J p)·∏_J x`.  Hence
  the degree-`J` part of `k[Δ]` (for a face `J`) is the free rank-one `R`-module `R·∏_J x`, with the
  detector as its coordinate.

This is the atomic multigrading fact: for each face `J`, the fine-degree-`J` slice is one-dimensional
and read by `srFaceDetector J`.  Next: package the degree-`J` part as a submodule / the graded
decomposition of the free Koszul module `(α → k[Δ])`, then the exhaust (a degree-`σ` first-Koszul cycle
has each `a_v` degree-`(σ∖v)`-homogeneous, hence a scalar multiple of `∏_{σ∖v} x` — i.e. a syzygy),
collapsing the direct-summand `R` to the *whole* `Tor_{1,σ}`.

### Lean progress — exhaust given componentwise homogeneity (multigrading, step 2)

`srHollowSimplexSyzygyVec_of_homogeneous` (in `StanleyReisnerMultigrading.lean`, axiom-clean) is the
second multigrading step: a `1`-chain `a` supported on `σ`, each of whose components `a_v` (`v∈σ`) is
homogeneous of squarefree multidegree `σ∖v` (lifts to a polynomial supported on the single exponent
`indicatorExponent (σ.erase v)`), **equals the hollow-simplex syzygy** read off by the face detectors
`a = w((srFaceDetector(σ∖v) a_v)_v)`.

Proof: componentwise `srMk_homogeneous_eq` — at `v∈σ`, `a_v = srFaceDetector(σ∖v)(a_v)·∏_{σ∖v} x`, which
is exactly `w(c)_v`; off `σ`, both are `0`.

So **every multidegree-`σ` `1`-chain is a syzygy** — the syzygy submodule is the whole degree-`σ` part
of the Koszul `1`-chains.  This is the exhaust modulo one remaining input: that a *multidegree-`σ`
cycle* is componentwise homogeneous, i.e. the fine grading of the free module `(α → k[Δ])`.  With that
last piece, the direct-summand `R` of previous fires becomes the entire `Tor_{1,σ} ≅ R`.

Next: the fine grading of the free Koszul module — a first-Koszul cycle of multidegree `σ` has each
`a_v` in fine-degree `σ∖v` (from `∑ a_v x_v` being multidegree `σ` and `x_v` degree `{v}`) — closing
the exhaust `Tor_{1,σ} ≅ R` for the whole degree-`σ` homology.

### Lean progress — degree-1 multigraded exhaust CLOSED (Tor_{1,σ} = R·[base])

`srHollowExhaust_class` (in `StanleyReisnerMultigrading.lean`, axiom-clean) closes the exhaust: for any
multidegree-`σ` `1`-chain `a` (componentwise homogeneous of degree `σ∖v` — the `σ`-graded piece of the
free Koszul module), its class in the first Koszul homology is

`[a] = (∑_{v∈σ} srFaceDetector(σ∖v) a_v) · [base]`.

Proof chain: `a` is a syzygy (`srHollowSimplexSyzygyVec_of_homogeneous`), and syzygy classes are
determined by their coefficient sum (`srHollowSimplexSyzygy_mk_eq_iff`), so `[a] = (∑ c)·[base]`.

Consequence: **the entire degree-`σ` part of `Tor₁` is `R·[base]`** — every multidegree-`σ` class is a
scalar multiple of the base syzygy class.  Combined with the injective base embedding
(`srHollowClassEquiv`, a free rank-one `R`) and the splitting retraction (`srHollowDetectorTor`), this is
the full degree-1 Hochster identity `Tor_{1,σ} ≅ R = H̃^{|σ|−2}(∂Δ^{|σ|−1})` as an isomorphism of the
whole multigraded homology, not just the syzygy summand.

The degree-1 Hochster strand is now complete end to end: nonzero classes → exact-rank iff → module iso →
LinearEquiv → embedding → retraction → direct summand → concrete C₃ match → fine multigrading →
exhaust.  Next: the higher `Tor_{i≥2}` strands (the general `koszulTor` over `S = k[Δ]`).

### Lean progress — degree-2 (Tor₂) module structure of C₄ (higher-Tor arc opened)

Opening the higher-`Tor` (`i≥2`) arc, `C4KoszulTorModule.lean` (axiom-clean) gives the module structure
of the `4`-cycle `Tor₂` class over a field `F`, mirroring the degree-1 embedding:

- `srC4KoszulTorClass` — the `C₄` second-Koszul-homology class in the general `koszulTor` framework.
- `srC4KoszulTor_smul_ne_zero` — **torsion-free**: `r·[C₄] ≠ 0` for `r ≠ 0` (over a field the homology
  is an `F`-vector space, so the nonzero class of `srC4KoszulTor_ne_zero` has no `F`-torsion).
- `srC4KoszulTorEquiv` — **`F ≃ₗ[F] F·[C₄]`**: the `C₄` `Tor₂` class spans a free rank-one `F`-line in
  the second Koszul homology (`LinearEquiv.ofInjective` on `toSpanSingleton`, injectivity from
  `smul_eq_zero` + `srC4KoszulTor_ne_zero`).

This is the `Tor₂` analogue of the degree-1 base-class embedding (`srHollowClassEquiv`), realizing the
`|W|=4, i=2` Hochster cell `Tor₂ ⊇ F = H̃¹(C₄)` as a rank-one submodule.  The general `koszulTor` is an
`F`-vector space (over a field), so field torsion-freeness gives the embedding without re-running the
edge detector.

Next: the degree-2 exact rank / retraction (whole `Tor₂` at `{a,b,c,d} ≅ F`, needing the third Koszul
differential `d₃`), then the `C₅`/`C₆` classes in `Tor₃`/`Tor₄`.

### Lean progress — higher-cycle classes torsion-free (C₅ Tor₃, C₆ Tor₄)

`HigherCycleTorsionFree.lean` (axiom-clean) extends the degree-2 module structure up the tower: over a
field, the pentagon (`C₅`, `Tor₃`) and hexagon (`C₆`, `Tor₄`) Koszul classes are torsion-free.

- `IsAlternating4_smul` / `IsAlternating5_smul` — scaling an alternating tensor stays alternating.
- `srKoszulBoundary4_smul` / `srKoszulBoundary5_smul` — the fourth/fifth Koszul differentials are
  `R`-linear in their tensor.
- `srPentTripleCycle_smul_not_koszulBoundary4` — for `r ≠ 0`, `r·C₅` is not a `d₄`-boundary.
- `srHexTupleCycle_smul_not_koszulBoundary5` — for `r ≠ 0`, `r·C₆` is not a `d₅`-boundary.

Proof (both): if `r·cycle = d(b)` then `cycle = d(r⁻¹·b)` with `r⁻¹·b` still alternating, contradicting
the established non-boundary (`srPentTriple_thirdKoszulHomology_nonzero` /
`srHexTuple_fourthKoszulHomology_nonzero`).  So each `Cₙ` class has a free rank-one `F`-span in `Tor_{n-2}`
— the torsion-free / embedding step of the degree-1 program replayed at degrees 3 and 4.

Next: package these into `Tor₃`/`Tor₄` module classes (via `LinearEquiv.toSpanNonzeroSingleton`, mathlib);
then the higher exact ranks (whole `Tor_{i}` at the cycle multidegree ≅ `F`).

### Lean progress — C₅ Tor₃ and C₆ Tor₄ as module classes (embeddings)

Extending `HigherCycleTorsionFree.lean` (axiom-clean), the pentagon and hexagon Koszul classes now carry
the same module structure the `C₄` `Tor₂` class has — a free rank-one `F`-line inside the homology, via
mathlib's `LinearEquiv.toSpanNonzeroSingleton` (a nonzero element of a torsion-free module over a domain
spans a free rank-one submodule; over a field the homology is a vector space).

Infrastructure built (both degrees): `IsAlternating4_add/zero`, `IsAlternating5_add/zero`,
`alternating4Submodule` / `alternating5Submodule` (alternating tensors form a submodule),
`srKoszulBoundary4ₗ` / `srKoszulBoundary5ₗ` (`d₄`, `d₅` as `R`-linear maps),
`srPentTripleBoundaries` / `srHexTupleBoundaries` (image submodules `d₄(alt⁴)`, `d₅(alt⁵)`).

- `srPentTripleTorClass` / `srPentTripleTorClass_ne_zero` / `srPentTripleTorEquiv` — `F ≃ₗ[F] F·[C₅]` in
  `(α→α→α→S) ⧸ d₄(alt⁴)`.  Nonzero because the pentagon cycle is not a `d₄`-boundary
  (`srPentTriple_thirdKoszulHomology_nonzero`).
- `srHexTupleTorClass` / `srHexTupleTorClass_ne_zero` / `srHexTupleTorEquiv` — `F ≃ₗ[F] F·[C₆]` in
  `(α→α→α→α→S) ⧸ d₅(alt⁵)`.  Nonzero via `srHexTuple_fourthKoszulHomology_nonzero`.

So each `Cₙ` (`n = 4,5,6`) class spans a free rank-one `F`-module in `Tor_{n-2}` — the degree-1 embedding
replayed at degrees 2, 3, 4.  Next: the higher exact ranks (whole `Tor_i` at the cycle multidegree `≅ F`,
the multigraded exhaust one degree up, needing `d_{n+1}`).

### Lean progress — Hochster realization for C₅ (Tor₃) and C₆ (Tor₄)

`HochsterCycleRealization.lean` (axiom-clean) now connects the new algebraic `Tor` embeddings to the
topological reduced first cohomology for the whole cycle family:

- `finrank_reducedH1_cycleGraph5` / `finrank_reducedH1_cycleGraph6` — `dim H̃¹(Cₙ) = 1` (`= n − (n−1)`).
- `reducedH1_cycleGraph5_nontrivial` / `reducedH1_cycleGraph6_nontrivial`.
- `hochster_C5_both_nonzero` / `hochster_C6_both_nonzero` — for any complex realizing the pentagon/hexagon,
  the algebraic `srPentTripleTorClass` (`Tor₃`) / `srHexTupleTorClass` (`Tor₄`) and the topological
  `H̃¹(Cₙ)` are simultaneously nonzero — the `i = n−2`, `|W| = n` instances of
  `Torᵢ(k[Δ],k)_W ≅ H̃^{|W|−i−1}(Δ|W)`.
- `c5Facets` / `c6Facets` + `hochster_C5_realization` / `hochster_C6_realization` — fully unconditional at
  the concrete pentagon/hexagon complexes (all hypotheses discharged by `decide`).

Together with the existing `C₃` (`Tor₁`) and `C₄` (`Tor₂`) realizations, the Hochster iso is now realized
(both sides nonzero, unconditionally) across the cycle family `C₃…C₆`, i.e. `Tor₁…Tor₄`.  Next: upgrade
`both_nonzero` to `both_dimension_1` (exact rank) for `C₄…C₆` as done for `C₃` (`hochster_C3_exact_rank`).

### Lean progress — concrete C₄ Tor₂ module class: cycle family now uniform

`HigherCycleTorsionFree.lean` now carries the square (`C₄`) `Tor₂` class in the *same* concrete
`(chains) ⧸ (d-boundaries)` framework as `C₅`/`C₆` (the general `koszulTor` `C₄` class lives in a
different `Fin`-indexed module):

- `IsAlternating3_add/zero/smul`, `alternating3Submodule`, `srKoszulBoundary3ₗ` (`d₃` as an `R`-linear
  map), `srSquareEdgeBoundaries` (`d₃(alt³)`).
- `srSquareEdgeTorClass` / `srSquareEdgeTorClass_ne_zero` / `srSquareEdgeTorEquiv` — `F ≃ₗ[F] F·[C₄]` in
  `(α→α→S) ⧸ d₃(alt³)`, nonzero via `srSquareEdge_secondKoszulHomology_nonzero`.
- `hochster_C4_concrete_realization` (in `HochsterCycleRealization.lean`) — the uniform both-nonzero
  statement at `c4Facets` using this concrete class.

So `C₄`, `C₅`, `C₆` now realize `H̃¹` through **one uniform family** of concrete `Tor_{n−2}` module classes
`srSquareEdgeTorClass` / `srPentTripleTorClass` / `srHexTupleTorClass`, each a free rank-one `F`-line, each
paired with the topological `H̃¹(Cₙ)`.  Next: the exact ranks (both-dimension-`1`) for `C₄…C₆`; the card's
open gate remains the general finite-complex bridge `(5)–(3)`.

### Lean progress — C₄ Tor₂ explicit direct summand (detector retraction)

`HigherCycleTorsionFree.lean` now upgrades the concrete `C₄` embedding to an explicit direct summand,
the degree-2 analogue of `hochster_C3_direct_summand`:

- `srEval2ₗ` — evaluation of a `2`-tensor at a fixed index pair, as an `R`-linear map.
- `srSquareEdgeDetectorₗ` — the alternating edge detector `+{cd}∘c_{ab} − {ad}∘c_{bc} + {ab}∘c_{cd} −
  {bc}∘c_{da}` as an `R`-linear map `(α→α→S) →ₗ R`.
- `srSquareEdgeDetectorₗ_srSquareEdgeCycle` — it is `1` on the square cycle.
- `srSquareEdgeDetectorₗ_srKoszulBoundary3` — it annihilates every `d₃`-boundary of an alternating
  `3`-tensor.
- `srSquareEdgeDetectorTor` — the detector descended through the `d₃`-boundary quotient, a retraction
  `Tor₂ → R`; `srSquareEdgeDetectorTor_class` proves it is `1` on the `Tor₂` class.
- `hochster_C4_concrete_direct_summand` (in `HochsterCycleRealization.lean`) — packages `dim H̃¹(C₄) = 1`
  with the explicit retraction `∃ ρ : Tor₂ → F, ρ[C₄] = 1`, so `F` is a genuine (not merely
  vector-space-generic) direct summand of the concrete second Koszul homology.

Now `C₃` (`Tor₁`) and `C₄` (`Tor₂`) both carry the explicit-retraction direct summand.  Next: the same
detector retraction for `C₅`/`C₆` (`Tor₃`/`Tor₄`), then the exact ranks (`both_dimension_1`).

### Lean progress — C₅/C₆ detector retractions: direct summand across the whole family

Completing the explicit-retraction direct summand up the tower (`HigherCycleTorsionFree.lean`,
axiom-clean):

- `srEval3ₗ` / `srEval4ₗ` — `3`- and `4`-tensor evaluation as `R`-linear maps.
- `srPentTripleDetectorₗ` / `srHexTupleDetectorₗ` — the alternating pentagon/hexagon detectors as
  `R`-linear maps, `1` on their cycle (`_srPentTripleCycle` / `_srHexTupleCycle`) and `0` on every
  `d₄`- / `d₅`-boundary of an alternating tensor (`_srKoszulBoundary4` / `_srKoszulBoundary5`).
- `srPentTripleDetectorTor` / `srHexTupleDetectorTor` — descended retractions `Tor₃ → R`, `Tor₄ → R`;
  `_class` lemmas prove each is `1` on its `Tor` class.
- `hochster_C5_concrete_direct_summand` / `hochster_C6_concrete_direct_summand`
  (`HochsterCycleRealization.lean`) — `dim H̃¹(Cₙ) = 1` with `∃ ρ, ρ[Cₙ] = 1`.

**The whole cycle family `C₃…C₆` (`Tor₁…Tor₄`) now carries the explicit-retraction direct summand:**
`F` is a genuine (not vector-space-generic) direct summand of `Tor_{n−2}`, matched with the topological
`dim H̃¹(Cₙ) = 1`.  The retraction `ρ` is the surjective half of every exact rank; the remaining half is
its injectivity on the multidegree strand (every cycle with `ρ = 0` is a boundary) — the degree-`(n−2)`
multigraded exhaust.

### Lean progress — §3.1 thesis: boundary dimension ⊥ coherence amplitude

`hochster_thin_support_deep_coherence` (`HochsterCycleRealization.lean`, axiom-clean) formalizes the
card's central structural consequence (§3.1).  It packages the cycle family into the independence
statement: each of `C₄`, `C₅`, `C₆` is one-dimensional (every facet an edge, `card = 2`, by `decide`)
yet carries a nonzero source-coherence `Tor` class in degree `2`, `3`, `4` respectively (via the
concrete realizations).  So one fixed thin reduced support (boundary dimension `1`) realizes strictly
growing derived coherence amplitude — the classical boundary dimension and the derived source-coherence
amplitude are independent invariants, a thin support carrying arbitrarily deep coherence.

This lifts the whole `C₃…C₆` cycle-family infrastructure (embeddings, realizations, explicit-retraction
direct summands) into the card's headline thesis as a single proven Lean theorem.  Next: the exact ranks
(`both_dimension_1`) via the degree-`(n−2)` multigraded exhaust, and the general finite-complex bridge.

### Lean progress — rank-2 reduced H̃¹ source coherence (independent Tor₁ classes)

`WedgeBettiRank.lean` (axiom-clean) gives the degree-1 analogue of the reduced-H⁰ independent-class family
(`isolatedDisconnectCycleBasis_independent_mod_koszulBoundary`): a single **connected** complex realizing
coherence rank `> 1` at reduced cohomological degree `1`.

- `srPairDetector_srVertexX_mul_eq_zero` — the pair detector of a product at a *different* squarefree
  multidegree is `0` (the cross-term, via `coeff_monomial` + `if_neg`).
- `srEmptyTriangleDetector_koszulBoundary_zero` — reusable form of the empty-triangle detector vanishing
  on every first Koszul boundary.
- `wedgeFacets` — the wedge of two empty triangles `{0,1,2}`, `{0,3,4}` at the shared apex `0`: a
  connected one-dimensional complex with `H̃¹ = F²`.
- `hochster_wedge_classes_independent` — the two triangle-hole first Koszul classes `x₁x₂·e₀` and
  `x₃x₄·e₀` are **linearly independent** modulo Koszul boundaries (any boundary equal to their
  combination forces both scalars to `0`), each triangle detector separating its own class from the
  other's multidegree and killing boundaries.

So the multigraded Betti profile of one connected HT source can carry **rank-≥2** source coherence at
degree `1` — the card's "complete multigraded Betti profile `{H̃^j(Δ|W)}`" realized with a nontrivial
rank.  Next: the topological finrank `H̃¹(wedge) = 2` (custom graph), and higher-rank realizations.

### Lean progress — unbounded source-coherence rank at fixed reduced degree 1

`bouquet_classes_independent` (`WedgeBettiRank.lean`, axiom-clean) generalizes the rank-2 wedge to
arbitrary `k`: a bouquet of `k` empty triangles sharing one apex (petal pairs `(p i, q i)` of pairwise
distinct squarefree multidegree) carries `k` **linearly independent** first Koszul homology classes
`x_{p i} x_{q i}·e_apex`.  Any first Koszul boundary equal to a combination `∑ c i · classᵢ` forces every
`c i = 0`, read off by the `i`-th triangle detector — `1` on `classᵢ`, `0` on every other class (via the
cross-term `srPairDetector_srVertexX_mul_eq_zero`), vanishing on boundaries
(`srEmptyTriangleDetector_koszulBoundary_zero`), collapsed by `Finset.sum_eq_single_of_mem`.

So the degree-`1` Hochster source coherence of one connected HT source has **arbitrarily large rank `k`**
at fixed reduced cohomological degree — the rank analogue of the §3.1 amplitude independence (which fixed
topology and grew the `Tor` degree; this fixes the degree and grows the coherence rank).  The concrete
wedge (`hochster_wedge_classes_independent`) is the `k = 2` witness.  Next: a fully concrete unconditional
bouquet on `Fin (2k+1)` (discharging the structural hypotheses), and the exact ranks.

### Lean progress — concrete unconditional bouquet: rank k realized for every k

`bouquet_concrete_independent` (`WedgeBettiRank.lean`, axiom-clean) instantiates the abstract bouquet at
an explicit complex, discharging every structural hypothesis:

- `bqVtx k := Option (Fin k × Bool)` — vertices: `none` = apex, `some (i, b)` = the `b`-petal of triangle
  `i` (clean injectivity for the distinctness/multidegree facts).
- `bqFacets k` — the `k`-triangle bouquet as a `Finset.biUnion` of the 3 edges per triangle, with
  membership lemmas `bqFacets_{ap,aq,pq}_mem`.
- `bouquet_concrete_independent` — for every field `F` and every `k`, the `k` first Koszul classes on the
  concrete bouquet are linearly independent modulo boundaries, **with no remaining hypotheses**.

So "the degree-`1` Hochster source coherence of a connected HT source has rank exactly `k`" is now an
unconditional theorem for every `k` — unbounded coherence rank at fixed reduced degree, matching the
card's realization standard.  Next: a bouquet of hollow `n`-simplices (rank *and* dimension free
simultaneously), and the exact ranks.

### Lean progress — hollow-simplex bouquet: rank AND dimension free simultaneously

`HollowSimplexBouquet.lean` (axiom-clean) unifies the two independence axes into one theorem:

- `srHollowDetectorₗ_base` — the hollow-simplex detector is `1` on its own base syzygy.
- `srHollowDetectorₗ_disjoint` — it vanishes on a syzygy supported on a *disjoint* simplex (the class is
  supported off `σ`, so every detector term is `srFaceDetector _ 0 = 0` — the cross-term is trivial via
  disjointness, no coefficient lemma needed).
- `hollow_bouquet_independent` — for `k` pairwise disjoint hollow simplices, the `k` base first Koszul
  homology classes are linearly independent modulo boundaries (any boundary equal to `∑ c m · classₘ`
  forces every `c m = 0`), via `srHollowDetectorₗ_apply_boundary` + the two facts + `Finset.sum_eq_single`.

Taking all `σ_m` of size `n+1` realizes `H̃ⁿ⁻¹` at rank `k` — an **arbitrary `(dimension, rank)` cell** of
the multigraded Betti profile of one HT source, unifying §3.1's dimension-free axis (hollow simplices at
rank 1) with the bouquet's rank-free axis (triangles at degree 1).  Next: a concrete unconditional
disjoint-`∂Δⁿ` instantiation, and the exact ranks.

### Lean progress — concrete unconditional (dimension, rank) realizer for every (n, k)

`hollow_bouquet_concrete_independent` (`HollowSimplexBouquet.lean`, axiom-clean) instantiates the abstract
hollow-simplex bouquet at an explicit complex, discharging every hypothesis:

- `hbSigma k n m := {m} ×ˢ univ` on vertex type `Fin k × Fin (n+1)` — the `m`-th hollow `n`-simplex.
- `hbFacets k n` — the disjoint-`∂Δⁿ` bouquet: the codimension-one faces of each simplex (so each
  `hbSigma m` has all proper faces present and the simplex itself absent), with `hbFacets_erase_mem`.
- `hbSigma_disjoint` — distinct simplices are disjoint (first-coordinate argument on `{m} ×ˢ univ`).
- `hollow_bouquet_concrete_independent` — for every field `F` and every `(n, k)`, the `k` base first
  Koszul classes (each at reduced degree `n−1`) are linearly independent modulo boundaries, **with no
  remaining hypotheses**.

So **every `(dimension, rank) = (n−1, k)` cell of the multigraded Betti profile is realized by an explicit
finite Stanley–Reisner complex** — the concrete backbone of the §3.2 universality claim along the whole
hollow-simplex strand.  Next: the exact ranks (still gated on a Koszul-homology-of-regular-sequence bridge
absent from mathlib), or the §3.2 universality packaging.

### Lean progress — rank k as `LinearIndependent` in the Koszul homology module

`hollow_bouquet_concrete_linearIndependent` (`HollowSimplexBouquet.lean`, axiom-clean) gives the rank
realization its canonical module-theoretic form: the `k` base first Koszul homology classes of the
concrete disjoint-`∂Δⁿ` bouquet are `F`-**linearly independent** (mathlib `LinearIndependent`) in the
Koszul homology module `(V → S) ⧸ srKoszulBoundaries`.  So the degree-`(n−1)` source coherence of one HT
source has `F`-dimension `≥ k`, connecting the rank realization to mathlib's rank/dimension theory.

Proof: `Fintype.linearIndependent_iff` reduces to `∑ c m • [classₘ] = 0 → c = 0`; the vanishing sum
pushes through `Submodule.mkQ` to `∑ c m · classₘ ∈ srKoszulBoundaries = range srKoszulBoundaryₗ`, giving
an explicit boundary `cc`, and `hollow_bouquet_concrete_independent` closes it.

**Exact-rank status:** the `Tor_{n−2} ≅ F` upgrade (the one deep open target) needs a
Koszul-homology-of-regular-sequence bridge — probed and confirmed absent from mathlib (`Tor` there is only
the abstract categorical derived functor; no `koszulComplex`).  So the exact rank requires either a
mathlib-scale commutative-algebra contribution (Koszul resolution of a regular sequence → `Tor₂ = k`) or
a self-contained multidegree-strand computation; both remain genuinely open.

### Lean progress — §3.2 universality in canonical form (arbitrary Betti pattern, LinearIndependent)

`hollow_bouquet_linearIndependent` (`HollowSimplexBouquet.lean`, axiom-clean) states the card's positive
universality (§3.2) in mathlib's rank language: for **any** finite family of pairwise disjoint hollow
simplices — arbitrary sizes, hence an arbitrary reduced-cohomology-dimension pattern — the base first
Koszul homology classes are `F`-linearly independent in the Koszul homology module.  So the source
coherence of one HT source realizes any finite `(dimension, rank)` Betti pattern as a genuine independent
family.  `hollow_bouquet_concrete_linearIndependent` is now the one-line concrete instance at the explicit
disjoint-`∂Δⁿ` complex.

This closes the realization/universality side of the source-coherence duality: every finite Betti pattern
is realized (abstract, arbitrary; concrete, unconditional for `∂Δⁿ`), each with its `LinearIndependent`
witness.  The two remaining deep targets — the exact ranks (gated on a mathlib-absent Koszul-homology-of-
regular-sequence bridge) and the general finite-complex chain equivalence (needs the general simplicial
cochain complex, whose `d²=0` requires a `Fin.succAbove` simplicial identity not readily in mathlib) —
are mathlib-scale constructions.

### Lean progress — arbitrary Betti pattern realized (mixed-dimension bouquet)

`mixed_bouquet_concrete_linearIndependent` (`HollowSimplexBouquet.lean`, axiom-clean) is the full concrete
§3.2 positive universality: for **any** dimension assignment `s : Fin k → ℕ`, the mixed-dimension bouquet
(block `m` a hollow `(s m)`-simplex, vertex type `Σ m, Fin (s m + 1)`) carries `k` linearly independent
base first Koszul homology classes, the `m`-th at reduced degree `s m − 1`.

- `mbVtx s := Σ m : Fin k, Fin (s m + 1)`, `mbSigma s m := univ.image (Sigma.mk m)` (the `m`-th fiber),
  `mbFacets s` the codim-1 faces of each block, with `mbFacets_erase_mem` and `mbSigma_disjoint`
  (distinct blocks disjoint, by `Sigma.fst`).
- A one-line instance of `hollow_bouquet_linearIndependent`.

So one explicit HT source realizes **any finite multiset of reduced-cohomology dimensions** as an
independent source-coherence family — the realization/universality side of the source-coherence duality
is now complete both abstractly and concretely, for arbitrary patterns.

The two remaining deep targets (exact ranks; general finite-complex chain equivalence) stay gated on
mathlib-scale infrastructure absent from mathlib (Koszul-homology-of-regular-sequence; the general
simplicial cochain `d²=0`, whose `Fin.succAbove` commutation identity is not available by name —
`Fin.succAbove_succAbove` does not exist; only `Fin.succAbove_succAbove_predAbove`).

### Lean progress — the general reduced simplicial cochain complex (the missing topological half)

The previously recorded blocker ("the general finite-complex chain equivalence needs the general
simplicial cochain complex, whose `d²=0` requires a `Fin.succAbove` simplicial identity not readily in
mathlib") is **removed**.  The `Fin.succAbove` route was the wrong presentation.  Indexing cochains by
*finite vertex sets* instead of ordered tuples makes the whole complex degree-uniform and the `d²=0`
cancellation identical to the Koszul one already used throughout the corpus.

`SimplicialCochainComplex.lean` (axiom-clean, build green):

- `faceSign F σ v = (-1)^{#\{u ∈ σ : u < v\}}` — the incidence sign, with the only two facts needed:
  `faceSign_erase_of_lt` (erasing a smaller vertex flips it), `faceSign_erase_of_gt` (erasing a larger
  vertex preserves it), and `faceSign_mul_self` (it is `±1`).
- `faceSign_mul_faceSign_erase_antisymm` — the incidence-sign antisymmetry
  `faceSign σ u · faceSign (σ∖u) v + faceSign σ v · faceSign (σ∖v) u = 0`, the entire content of `δ²=0`.
- `simplicialCoboundary F f σ = ∑_{v∈σ} faceSign σ v · f (σ∖v)`, its linear form
  `simplicialCoboundaryₗ`, and **`simplicialCoboundary_simplicialCoboundary` : `δ ∘ δ = 0`** —
  unconditional, over any commutative ring, in **every degree at once** (the formula never mentions
  `#σ`), with the empty face present so the complex is the *reduced* one.  The cancellation is the
  `(u,v) ↔ (v,u)` involution via the corpus lemma `antisym_sigma_sum_zero`, exactly the device behind
  `koszulD_koszulD_eq_zero` — so both halves of the Hochster correspondence now rest on one principle.
- `cardCochains F c` and `simplicialCoboundary_mem_cardCochains` — the cardinality grading, exhibiting
  `C⁰ → C¹ → C² → ⋯` as an honest graded complex.
- `faceVanishingCochains F facets` (cochains vanishing on all faces of `Δ`) is `δ`-stable because faces
  are closed downwards, so the cochain complex of an arbitrary finite complex is the quotient
  `complexCochains`, with `complexCoboundary_complexCoboundary` : **`δ_Δ² = 0` for every finite
  complex**.  No decidability of `IsFaceOf` is required.

### Lean progress — exact reduced cohomology of a hollow simplex in EVERY dimension

`HollowSimplexReducedCohomology.lean` (axiom-clean, build green) uses the new complex to supply the
topological half of the `Tor₁` strand uniformly, matching the already-exact algebraic half
`srHollowSimplexSyzygyVec_boundary_iff`:

- `hollowFacets σ` (the boundary complex `∂σ`) with `isFaceOf_hollowFacets_iff` (its faces are exactly
  the proper subsets of `σ`), `isFaceOf_hollowFacets_erase`, `not_isFaceOf_hollowFacets_self`.
- `simplicialCoboundary_mem_faceVanishing_of_card` — top-degree cochains of `∂σ` are cocycles.
- `hollowPrimitive F σ i₀ a` — the explicit primitive supported on the codimension-two faces
  `σ ∖ {i₀,k}` through a base vertex, sign-corrected; `simplicialCoboundary_hollowPrimitive_of_ne`
  and `simplicialCoboundary_hollowPrimitive_base` compute its coboundary on every facet.  It is the
  topological mirror of the algebraic spanning `2`-chain of
  `srHollowSimplexSyzygyVec_boundary_of_sum_zero`.
- **`hollowSimplex_coboundary_iff`** : `(∃ h, ∀ i ∈ σ, (δh)(σ∖i) = a i) ↔ ∑_{i∈σ} faceSign σ i · a i = 0`.
  Only values on `(|σ|−2)`-subsets of `σ` can contribute, so no degree bookkeeping is needed: this is
  exactly `H̃^{|σ|−2}(∂Δ^{|σ|−1}) ≅ F`, for **every** `|σ|`, over any commutative ring.
- `hollowSimplex_reducedCohomology_nonzero` — the top cochain concentrated on one facet is not a
  coboundary, so the reduced cohomology is nonzero in every dimension.

### Lean progress — the uniform-degree Hochster correspondence (both sides, all dimensions)

- **`hochster_hollowSimplex_boundary_iff`** : for a hollow simplex `σ`, the multidegree-`σ` first
  Koszul syzygy `w(l)` is a Koszul boundary **iff** the matching top simplicial cochain
  `i ↦ faceSign σ i · l i` is a simplicial coboundary.  Both sides are cut out by a single linear
  functional, so `Tor_{1,σ}` and `H̃^{|σ|−2}(Δ_σ)` are each exactly one-dimensional and correspond.
- `hochster_hollowFacets_boundary_iff` — the same statement on the explicit boundary complex `∂σ`,
  with every structural hypothesis discharged (only `σ.Nonempty`).
- `hochster_hollowFacets_both_nonzero` — on `∂σ` the basis syzygy at any vertex is not a Koszul
  boundary **and** the matching top cochain is not a simplicial coboundary: the Hochster class is
  nonzero on both sides simultaneously, in every dimension, over any nontrivial commutative ring.

This upgrades the concrete degree-`1` cycle-graph instances `hochster_C3/C4/C5/C6_*` of
`HochsterCycleRealization` (which relied on graph-specific Betti formulas) to a single theorem valid
in every dimension, and it replaces the previously recorded "mathlib-scale, gated" status of the
general chain-equivalence half with an actual unconditional construction.

### Lean progress — Hochster's formula at `Tor₁` for ARBITRARY complexes and ARBITRARY multidegrees

This closes the card's long-standing "general finite-complex bridge" gate at the first Koszul level.
`HochsterMultidegreeTorOne.lean` (axiom-clean, build green) proves the strand equivalence
`Tor_{1,σ} ≅ H̃^{|σ|−2}(Δ_σ)` for **every** finite complex and **every** multidegree `σ` — not only for
hollow simplices, and not only in reduced degree `1`.

The multidegree-`σ` strand of the Koszul `1`-chains is exactly the family
`srHollowSimplexSyzygyVec F facets σ l`; its `i`-th slot vanishes automatically when `σ ∖ i` is a
nonface, matching the fact that a cochain of `Δ_σ` lives only on faces.  The dictionary is the
incidence sign, `l i ↦ faceSign σ i · l i`.

- `erase_erase_eq_erase_erase_iff` — two double deletions from `σ` agree exactly when the deleted
  pairs agree (the combinatorial identification of codimension-two faces with unordered pairs).
- `signedPair_symm`, `signedPair_symm'` — the sign-corrected pair weight is invariant under the swap,
  on antisymmetric and on symmetric coefficient families respectively.
- `pairCochain F σ b` and `pairCochain_erase_erase` — the codimension-two cochain attached to a
  coefficient family, with the ordered-pair guard `p < q` that keeps the construction
  **characteristic-free** (an unguarded symmetrization would produce a factor `2`).
- `srKoszulRelation_srHollowSimplexSyzygyVec` — the strand's Koszul differential is
  `(∑_{i∈σ} l i) · ∏_σ x`; hence `srHollowSimplexSyzygyVec_isCycle_iff`: for a face `σ` a strand
  element is a cycle iff `∑_{i∈σ} l i = 0`, which is exactly the topological cocycle condition
  `(δa)(σ) = ∑_{i∈σ} faceSign σ i · a i = 0` in the slot that exists only when `σ ∈ Δ`.
- **`hochster_multidegree_boundary_iff`** — the boundary halves agree:
  `(∃ cc, ∂ cc = w(l)) ↔ (∃ h, ∀ i ∈ σ with σ ∖ i a face, (δh)(σ ∖ i) = faceSign σ i · l i)`.
  Forward: the face detectors `srFaceDetector (σ ∖ i)` applied to the boundary equation produce an
  antisymmetric scalar family `b` with `∑_{j ∈ σ∖i} b i j = l i`, and `pairCochain σ b` is the
  primitive.  Backward: the sign-corrected `pairCochain` of the given cochain, placed on the
  codimension-two monomials of `σ`, is the `2`-chain; slots where `σ ∖ i` is a nonface impose no
  condition because the corresponding monomial vanishes.
- **`hochster_multidegree_torOne_correspondence`** — the two halves packaged: cycles ↔ cocycles and
  boundaries ↔ coboundaries under the incidence-sign dictionary.  This is Hochster's formula at
  `i = 1`, unconditional, over any commutative ring, for arbitrary finite complexes and arbitrary
  multidegrees.

Status of the card's two previously "mathlib-scale, gated" targets: the general finite-complex chain
equivalence is now **done at `Tor₁`** (the strand the card's whole realization programme lives in),
with the general reduced simplicial cochain complex supplied from scratch.  What remains open is the
higher-`i` layer `Tor_{i,σ} ≅ H̃^{|σ|−i−1}(Δ_σ)` for `i ≥ 2` (the corpus has the Koszul complex in all
degrees, `koszulD` with `d² = 0`, and the cochain complex in all degrees, so the remaining work is the
multidegree-strand identification one level up), and the exact ranks for non-hollow `σ`.

### Lean progress — the strand CHAIN MAP (cochains of `Δ_σ` → multidegree-`σ` Koszul strand)

The card's Lean target asks for the squarefree Koszul strands *and their chain equivalence with
reduced cochains of induced subcomplexes*.  The chain-map half is now explicit and unconditional
(`HochsterMultidegreeTorOne.lean`, axiom-clean):

- `strandOne F facets σ a` — a cochain on the codimension-one faces of `σ` becomes the multidegree-`σ`
  Koszul `1`-chain with incidence-sign corrected coefficients.
- `strandTwo F facets σ g` — a cochain on the codimension-two faces of `σ` becomes the multidegree-`σ`
  Koszul `2`-chain in strictly-upper-triangular form, the representative of an alternating tensor that
  keeps the construction characteristic-free.
- `srKoszulRelation_strandOne` : `d₁ (strandOne a) = (δa)(σ) · ∏_σ x` — the degree-`1` chain-map
  identity; the target slot survives exactly when `σ` is a face, matching `C^{|σ|}(Δ_σ)`.
- **`srKoszulBoundary_strandTwo`** : `d₂ (strandTwo g) = strandOne (δg)` — the degree-`2` chain-map
  identity.  So the strand maps intertwine the reduced simplicial coboundary of `Δ_σ` with the Koszul
  differential, for every finite complex and every multidegree.
- `srHollowSimplexSyzygyVec_congr` — coefficients at nonface slots are invisible (the monomial
  vanishes), which is why the chain map is insensitive to the values a cochain takes off `Δ_σ`.

With `hochster_multidegree_boundary_iff` (which now reads off the chain map directly in its backward
direction) this gives the chain equivalence at the `Tor₁` level: the chain map carries coboundaries
onto Koszul boundaries and, conversely, every strand boundary comes from a coboundary.

**Convention note for the next level.**  The corpus differential `srKoszulBoundary c i = ∑_j (c_ij −
c_ji) x_j` is the standard alternating `d₂` read on *upper-triangular* representatives, while
`srKoszulBoundary3` produces *antisymmetric* `2`-tensors; composing them directly costs a factor `2`.
The characteristic-free `Tor₂` statement therefore has to pass through the upper-triangular
representative of `d₃`, i.e. `srKoszulBoundary (upperTri (srKoszulBoundary3 n)) = 0` for alternating
`n`, which is the standard `d₂ ∘ d₃ = 0`.  That is the next increment.
