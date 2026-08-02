# Finite pro-log Tate graph residue is split strict

- **ID:** `deninger-finite-pro-log-tate-graph-residue-splitting`
- **Stage:** 2-fully-proven
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
- [ ] analytic structures represented directly in Lean
- [ ] uniform pro-stage strictness

## Log

- 2026-08-01 — Proved finite-stage Poincare residue/evaluation remain
  split strict after intersecting holomorphic and Tate graph scales;
  isolated uniform pro-system passage as remaining topology gate.
