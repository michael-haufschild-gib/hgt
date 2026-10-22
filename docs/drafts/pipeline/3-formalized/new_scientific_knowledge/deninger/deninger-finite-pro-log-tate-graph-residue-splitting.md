# Finite pro-log Tate graph residue is split strict

- **ID:** `deninger-finite-pro-log-tate-graph-residue-splitting`
- **Stage:** 3-formalized
- **Type:** POSITIVE SURVIVOR THEOREM
- **Label:** `DAC_FINITE_PRO_LOG_TATE_GRAPH_RESIDUE_SPLITTING`
- **Parent:** `deninger-unbounded-rank-fixed-sobolev-residue-no-go`
- **Scientific status:** `[NEW SOURCE ASSEMBLY; LOCAL ANALYTIC PARENTS STANDARD]`
- **Statement:** on every finite split pro-log Stein chart, intersecting
  the compact-open holomorphic logarithmic-form topology with all
  Tate-transverse graph seminorms makes Poincare residue a continuous
  split surjection; its source-defined section commutes with every
  graph monomial, and finite packet evaluation is continuous in the
  horizontal holomorphic factor.

## Projective graph chart

Use the finite-stage splitting

\[
 \overline Z_{L,v}=D_{L,v}\times\mathbb C_z,
 \qquad D_{L,v}=D_{L,v}\times\{0\}.                         \tag{1}
\]

Let (mathcal E_{L,v}) be logarithmic forms on `(1)`, tensored with
the smooth transverse source, and equip it with all seminorms

\[
 p_{K,j,m}(\omega)
 =\sup_{(x,z)\in K}
   \|\partial_z^j\widehat A^{,m}\omega(x,z)\|,             \tag{2}
\]

where (K) ranges over a compact exhaustion, (j,m\ge0), and
(widehat A) is the Tate-normalized transverse generator.  Use the
analogous seminorms on boundary forms (mathcal F_{L,v}).

Every logarithmic form has unique local expression

\[
 \omega=\alpha+{dz\over z}\wedge\beta.                      \tag{3}
\]

Define

\[
 R\omega=\beta|_{z=0},
 \qquad
 S\gamma={dz\over z}\wedge\pi_D^*\gamma.                   \tag{4}
\]

## Theorem

`[PROVED HERE] [DAC_FINITE_PRO_LOG_TATE_GRAPH_RESIDUE_SPLITTING]`

For every finite stage `(1)`:

1. (R:\mathcal E_{L,v}\to\mathcal F_{L,v}) and
   (S:\mathcal F_{L,v}\to\mathcal E_{L,v}) are continuous for
   topology `(2)`;
2. (RS=1);
3. for every transverse graph monomial (P_i),
   
   \[
    R P_i=P_iR,
    \qquad
    S P_i=P_iS;                                               \tag{5}
   \]
4. (R) is therefore a split strict surjection on the common graph
   cores and every target graph seminorm has a source lift with the
   same transverse bound;
5. restriction to the finite actual packet
   (Y_{L,v}\subset D_{L,v}) is continuous.  It is split onto
   (operatorname{Map}(Y_{L,v},\mathbb C)).

### Proof

Coefficient extraction in `(3)` and restriction to (z=0) are
continuous in compact-open holomorphic topology.  More explicitly,
Cauchy's formula on a compact normal circle bounds every boundary
derivative seminorm by a compact source seminorm.  Formula `(4)` for
(S) is pullback followed by multiplication by the fixed logarithmic
normal form, so it is continuous.  Direct substitution gives (RS=1).

The transverse generator acts on the smooth suspension/packet factor,
while (R,S) act only on log-normal and horizontal character factors.
They commute on elementary tensors, hence on the completed projective
tensor product, proving `(5)`.

If a target vector belongs to every monomial domain, `(5)` puts its
lift under (S) in every source monomial domain; applying (R)
returns the vector.  Conversely (R) maps every source domain to the
corresponding target domain.  Thus the same section splits the map on
common graph cores.  The graph-seminorm estimates follow from `(5)`
and continuity of (R,S).

Finally (Y_{L,v}) is finite.  Evaluation is continuous in
compact-open topology.  Coordinate ring of the affine torus
(D_{L,v}) separates its distinct points, so the Chinese remainder
theorem supplies functions (e_y) with
(e_y(y')=\delta_{y,y'}).  The finite map sending a tuple
((c_y)) to (sum_yc_ye_y) is a continuous right inverse.  Packet
restriction is therefore split.

## Finite relative-cell consequence

The residue square is a morphism on the free unit cdga.  Each finite
relative Sullivan/Milnor attachment is formed from finite sums,
shifts, and completed projective tensor products.  Nuclear Frechet
spaces preserve split exact sequences under these operations.
Therefore every finite relative cell inherits the split residue map
and graph commutation before cohomology.

This statement does not pass an infinite cell tower or all pro-log
stages automatically.

## Hostile audit and scope

- The section (S) depends on a finite-stage splitting/uniformizer;
  residue does not.  Compatibility of these sections across all
  transition maps is not asserted or needed for local strictness.
- Fixed-stage constants may depend on compact set, lattice rank, and
  packet cardinality.  The theorem supplies no uniform pro-stage
  estimate.
- Compact-open holomorphic seminorms are load-bearing.  Removing them
  returns the two proved evaluation no-gos.
- The theorem closes finite-stage residue/core graph strictness, not
  all-prime Green summability, global Cauchy conservativity, or Meyer
  comparison.
- No Xi divisor, zero, RH premise, or numerical calculation occurs.

## Lean interface

The source-independent graph-core mechanism is formalized in
`DeningerTwoColumnCauchyFlowGraphDescent.lean`:

- `DeningerGraphIntertwining` records domain preservation and `(5)`;
- `deningerGraphCoreMap` restricts an intertwiner to common graph cores;
- `deningerGraphCoreMap_comp_rightInverse` proves a right inverse
  remains one on graph cores;
- `deningerGraphCoreMap_surjective_of_rightInverse` proves split
  graph-core surjectivity;
- `deningerGraphSeminorm_map_le` transfers ambient bounds to every
  graph seminorm.

The analytic input instantiating these declarations is formulas
`(3)`--`(5)`.

## Lean status

### Analytic structures landed

The split chart `(1)`, the normal decomposition `(3)`, the maps `(4)`, the seminorm
family `(2)` and the finite packet of clause 5 are represented directly in
`formal/GaloisForLFunctions/RHTower/Deninger/DeningerFiniteProLogTateGraphResidueSplitting.lean`
(41 declarations; axiom audit for every one of them:
`[propext, Classical.choice, Quot.sound]`).

The chart and the two maps:

- `DeningerLogForms D V = C(D × ℂ, V) × C(D × ℂ, V)` is the space of logarithmic forms in the
  unique normal decomposition `ω = α + (dz/z) ∧ β`, and `DeningerBoundaryForms D V = C(D, V)`
  the boundary forms on `D = D × {0}`; `deningerNormalZeroSection` and
  `deningerChartProjection` are the two structure maps of the splitting `(1)`.
- `deningerResidue : DeningerLogForms D V →L[ℂ] DeningerBoundaryForms D V` is `R ω = β|_{z=0}`
  and `deningerLogSection : DeningerBoundaryForms D V →L[ℂ] DeningerLogForms D V` is
  `S γ = (dz/z) ∧ π_D^* γ`.  Both are bundled as **continuous** linear maps for the
  compact-open topology, which is clause 1; `deningerPrecomp` is the underlying
  compact-open continuity of precomposition.
- `deningerResidue_comp_logSection` is clause 2 (`R S = 1`), and
  `deningerResidue_surjective` its split surjectivity.

The transverse graph scale:

- `DeningerTransverseCore A f` is the graph core of the Tate-normalized transverse generator
  `A`: every transverse monomial `A ^ m` leaves the field continuous.  For an unbounded
  generator this is a proper condition, so it is the honest analytic domain of the seminorms
  `(2)`; `deningerTransverseMonomial` produces `A ^ m f` as a continuous field.
- `deningerResidue_transverseCore` and `deningerLogSection_transverseCore` prove both maps
  preserve that core, and `deningerResidue_transverseMonomial_comm`,
  `deningerLogSection_transverseMonomial_comm` are the two commutations `(5)` of clause 3.
- `deningerLogSection_graphSeminorm_le_iff` proves the section's graph seminorm bound is
  *identical* to the boundary one, and `deningerResidue_graphSeminorm_le` transfers the
  source bound to the residue with the same constant — clause 4's "same transverse bound".
- `deningerResidue_splitStrict_graphCore` is clause 4 assembled: every boundary graph-core
  form is the residue of a source graph-core log form with exactly the same transverse graph
  seminorms and with vanishing higher normal derivatives
  (`deningerLogSection_iteratedDeriv_normal`).

The Cauchy input of the proof:

- `deningerNormalCircle_iteratedDeriv_le` is Cauchy's estimate on a normal circle:
  `‖∂_z^j g(x, ·)|_{z=0}‖ ≤ j! · C / r^j` whenever `‖g(x, z)‖ ≤ C` on `|z| = r`.
- `DeningerTateGraphField` is the analytic domain of the full seminorm family `(2)` (every
  transverse monomial continuous *and* holomorphic in the normal coordinate), and
  `deningerTateGraphField_boundary_deriv_le` bounds every boundary derivative seminorm
  `p_{K,j,m}` by the compact source seminorm `p_{circle,0,m}`.
  `deningerLogSection_tateGraphField` shows the section lands in that domain.

Clause 5, the finite packet:

- `deningerPacketRestriction Y : C(D, ℂ) →L[ℂ] (↥Y → ℂ)` is evaluation on a finite packet,
  continuous for the compact-open topology.
- `deningerPacketIdempotent_exists` supplies the separating functions `e_y` with
  `e_y(y') = δ_{y,y'}` from Urysohn separation on a `T1` normal horizontal factor — this is
  the Lean form of "the coordinate ring of the affine torus separates its points".
- `deningerPacketSection` is the resulting continuous right inverse
  `(c_y) ↦ ∑_y c_y e_y`, and `deningerPacketRestriction_comp_section`,
  `deningerPacketRestriction_surjective` prove packet restriction is a continuous split
  surjection onto `Map(Y, ℂ)`.

The finite relative-cell consequence:

- `deningerSplitSurjection_prodMap` proves a finite direct sum of continuous split surjections
  is a continuous split surjection, so each finite relative cell assembled from the residue
  square inherits the splitting.

### What is deliberately not in Lean

The uniform pro-stage estimate is not formalized because it is not proved: it is the successor
conjecture `DAC_PRO_LOG_TATE_PROJECTIVE_GRAPH_STRICTNESS` below, and the card's hostile audit
states explicitly that this theorem supplies no uniform pro-stage constant.

## Next exact claim

`[CONJECTURE] [DAC_PRO_LOG_TATE_PROJECTIVE_GRAPH_STRICTNESS]`

Choose a countable cofinal lattice/compact/cell system and prove its
transition maps form a regular strict nuclear inductive system for
topology `(2)`.  Establish stage-compatible residue/corestriction and
power maps, then prove the ((\log p)^2)-weighted all-prime Green forms
are summable on every defining Banach disk.

## Gates

- [x] finite-stage topology and source maps frozen
- [x] complete paper proof
- [x] hostile scope audit
- [x] Lean graph-core split infrastructure
- [x] analytic structures represented directly in Lean
- [ ] uniform pro-stage strictness *(successor conjecture, not this theorem)*

## Log

- 2026-08-01 — Proved finite-stage Poincare residue/evaluation remain
  split strict after intersecting holomorphic and Tate graph scales;
  isolated uniform pro-system passage as remaining topology gate.
- 2026-08-02 — All five clauses formalized unconditionally in
  `DeningerFiniteProLogTateGraphResidueSplitting.lean`: split chart, log-form
  decomposition, continuous `R` and `S`, `RS = 1`, transverse graph core with both
  monomial commutations, identical-bound seminorm lift, Cauchy normal-circle
  derivative estimate, and the Urysohn-split finite packet evaluation.  Axiom audit
  over all 41 declarations returns only `propext`, `Classical.choice`, `Quot.sound`.

- 2026-08-06 — Lean modules re-audited on this toolchain (`#print axioms` = `propext, Classical.choice, Quot.sound` for every capstone); every gate except the declared successor conjecture is closed, so the card moves to `3-formalized`.
