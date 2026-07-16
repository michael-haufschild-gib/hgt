# Active quasi-Abelian palettes classify finite full HT constraint geometry

- **ID:** `active-quasi-abelian-palette-exact-ht-dimension-classification`
- **Stage:** 1-in-progress
- **Type:** CORRECTED CONJECTURE / ACTION-RELATIVE HT DIMENSION CLASSIFICATION
- **Scientific status:** `[CONJECTURE] [ACTIVE-FAITHFUL NECESSITY PROVED]`
- **Statement:** The intrinsic analytic dimension of a finite full Stanley--Reisner HT constraint
  geometry is governed by quasi-Abelian facet quotients in which every structural facet lattice is
  faithful on the quotient by the maximal compact complex subtorus.

## Correction forced by the elliptic-shadow theorem

The retired invariant `qaDim` required:

- a noncompact quasi-Abelian period quotient for each facet;
- exact complement incidence;
- a faithful facet lattice in that quotient;
- generalized Riemann relations.

That data does not prevent the facet lattice from lying entirely in a compact Abelian factor of a
noncompact product.  On `E x C*`, such an action has unbounded aggregate capacity but finite cyclic
capacity for every observable.  Therefore the source selector must be action-relative.

## Active quotient

Let `X` be a noncompact quasi-Abelian group and let

```text
B(X) subset X
```

be its maximal compact connected complex subgroup.  This is an Abelian variety.  Define

```text
Act(X)=X/B(X).                                             (1)
```

For a finitely generated free subgroup `H subset X`, call `(X,H)` **active-faithful** when

```text
H -> Act(X)
```

is injective.

This condition is stronger than `H -> X` being injective and weaker than asking `X` to be Stein.
It retains noncompact Cousin directions; it removes only compact complex shadows which have finite
cyclic orbit capacity.

## Active quasi-Abelian palette dimension

Let `Delta` be a finite essential simplicial complex on `V`.  An active quasi-Abelian palette in
ambient dimension `d` consists of `Q`-linearly independent vectors

```text
a_v in C^d,  v in V,                                      (2)
```

and for each facet `A` a closed period group `P_A`, discrete quotient lattice `Gamma_A`, and
quasi-Abelian group

```text
X_A=(C^d/E_A)/Gamma_A                                     (3)
```

satisfying the six clauses of the retired `qaDim` palette, together with:

```text
Z^A -> Act(X_A),
n |-> sum_(v in A)n_v a_v mod P_A mod B(X_A)               (4)
```

is injective.

Define

```text
aqaDim(Delta)=min{d:an active quasi-Abelian palette exists}.              (5)
```

Forgetting (4) gives

```text
qaDim(Delta)<=aqaDim(Delta).                              (6)
```

Every periodic pencil has no compact complex shadow in its active `C*` quotient, so

```text
aqaDim(Delta)<=ppDim(Delta).                               (7)
```

## Corrected exact classification `[CONJECTURE]`

For every finite essential simplicial complex,

```text
htDim(Delta)=aqaDim(Delta).                                (8)
```

The expected hierarchy is

```text
peDim(Delta)<=qaDim(Delta)<=aqaDim(Delta)
                               =htDim(Delta)<=ppDim(Delta)<=ffsDim(Delta). (9)
```

## Active-faithful necessity `[PROVED HERE]`

The established facet separator extracts a meromorphic facet observable `G_A` whose integral
facet orbit is completely differentially free.  Its full period quotient supplies `X_A`, exact
incidence, noncompactness, the generalized Riemann relations, and faithfulness in `X_A`.

The required relative theorem now holds.

> **Compact-kernel finite-capacity theorem `[PROVED HERE]`.** Let `B` be a compact complex subtorus
> of a quasi-Abelian group `X`.  If a nonzero free Abelian subgroup `K` lies in `B`, then for every
> `g in Mer(X)` the complete `K`-translation orbit has finite differential transcendence degree over
> the rational universal-cover field.

The quotient `X -> X/B` is a proper holomorphic Abelian fibration.  On its generic fibre every
meromorphic `g` belongs to a finitely generated relative function field over `Mer(X/B)` and uses
only finitely many base coefficient functions.  Fibre translation acts algebraically inside that
one relative field and introduces no new coefficients.  An invariant derivation is determined on
a finite relative generating set by finitely many further base coefficients, so the differential
field of the complete compact-kernel orbit is finitely differentially generated.

If (4) failed for the facet lattice, its nonzero kernel would give such a subgroup `K`, contradicting
the already proved complete freeness of the facet orbit.  Hence

```text
aqaDim(Delta)<=htDim(Delta).                               (10)
```

The kernel-to-injectivity implication is formalized as
`activeQuotient_injective_of_fullOrbitFree_of_kernelCyclic_not` in
`formal/GaloisForLFunctions/HTGeometry/FiniteShadowCapacity.lean`.

## Sufficiency program

Let `Y_A=Act(X_A)`.  If (4) holds, the integral facet lattice acts faithfully on `Y_A`.  The needed
analytic theorem is:

> **Torusless all-order packet theorem `[CONJECTURE]`.** On every torusless noncompact
> quasi-Abelian group satisfying the generalized Riemann relations, one fixed ample automorphic
> factor has a Frechet section space whose evaluation map onto every finite jet packet is
> surjective.

Abe proves arbitrary finite point separation and first-tangent separation in the same fixed
automorphic-factor space.  His Poincare-series proof has two stability properties needed for the
extension:

1. polynomial multipliers and finite powers preserve the subquadratic growth class;
2. after any fixed finite number of derivatives, the complement-lattice terms are a polynomial in
   the damping parameter times an exponentially decaying factor.

The new proof must run Abe's subgroup-rank induction on finite local Artin algebras rather than on
point values.  Multiplication by the damping exponential acts invertibly on each truncated local
algebra, while the complement contribution tends to zero.  This should give simultaneous
surjectivity for arbitrary finite jet packets without changing the automorphic factor.

The already formalized affine jet-packet Baire theorem then produces a meromorphic ratio on each
`Y_A` whose faithful facet orbit is completely differentially free.  Pullback to `X_A`, facetwise
sum, and the localized Stanley--Reisner matroid theorem yield

```text
htDim(Delta)<=aqaDim(Delta).                               (11)
```

## The higher object: active constraint spectrum

The constraint spectrum alone is universal and therefore cannot select a special HT function.  A
source-selected finite HT geometry carries three layers:

```text
1. support:    Spec(R/Ann_DA(F));
2. activity:   the faithful lattice representation on Act(X_A) at every minimal prime;
3. sewing:     compatibility or polarization between the active facet quotients.        (12)
```

Layer 1 records which finite constraints coexist.  Layer 2 records whether infinite capacity is
concentrated in one structural observable.  Layer 3 is where positivity, self-duality, monodromy,
continuation, and boundary-condition compatibility may become different representations of one
global obstruction.

This is the current unified-field conjecture: the obstruction chains do not meet merely in a
topological space, but in an **active, sewn constraint spectrum**.

## Obstruction dictionary `[CONJECTURE]`

For a source-selected active constraint spectrum:

- **spectral incompleteness** means the active lattice representation is not jointly faithful;
- **continuation failure** means local active charts do not descend to a global meromorphic
  observable;
- **positivity failure** means the Hermitian forms on the active quotients do not admit a positive
  compatible sewing;
- **monodromy** is the holonomy of that sewing around nontrivial loops of the constraint spectrum;
- **noncanonical boundary conditions** mean the sewing torsor has no distinguished global section.

This dictionary is a research hypothesis, not an RH theorem.  Its value is that every entry now
refers to one mathematical object with independently testable layers.

## Novelty and anti-theatre gate

Standard parents include Remmert--Morimoto decomposition, quasi-Abelian reduction, generalized
Riemann relations, relative function fields of Abelian fibrations, Abe's automorphic forms, Baire
genericity, and Stanley--Reisner geometry.  None of those parents appears to define the
action-relative active quotient invariant (5), the attained-versus-dispersed capacity dichotomy,
or the active sewn constraint spectrum (12).

The route is not promoted as new scientific knowledge until:

- the nonsplit compact-kernel theorem is proved;
- the torusless all-order packet theorem is proved;
- equality (8) is proved rather than assumed;
- an exact-formulation literature audit finds no equivalent action-relative classification;
- examples separate `qaDim`, `aqaDim`, and `ppDim`, or prove a collapse theorem;
- the finite and geometric theorem surfaces are formalized without analytic axioms.

## Current exact boundary

Proved:

- the original ambient-noncompact full-orbit conjecture is false;
- the proper compact-kernel finite-capacity theorem;
- every finite capacity occurs in the split elliptic model;
- the split active quotient criterion;
- the exact finite-shadow matrix rank core in Lean.

Open:

- all-order fixed-factor jet interpolation on torusless quasi-Abelian groups;
- the exact active dimension equality (8);
- the sewing law selecting special functions inside the universal constraint class.

## Gates

- [x] old conjecture falsified rather than patched cosmetically
- [x] strong positive theorem extracted from the no-go
- [x] action-relative invariant defined
- [x] necessity and sufficiency reduced to named geometric theorems
- [x] active sewn constraint spectrum stated
- [x] prove nonsplit compact-kernel finite capacity
- [ ] prove torusless all-order packet interpolation
- [ ] prove `htDim=aqaDim`
- [ ] separate or collapse `qaDim`, `aqaDim`, and `ppDim`
- [ ] complete primary-literature novelty audit
- [ ] full Lean formalization of every promoted theorem surface
