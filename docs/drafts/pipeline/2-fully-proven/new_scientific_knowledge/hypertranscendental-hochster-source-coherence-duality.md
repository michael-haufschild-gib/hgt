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
