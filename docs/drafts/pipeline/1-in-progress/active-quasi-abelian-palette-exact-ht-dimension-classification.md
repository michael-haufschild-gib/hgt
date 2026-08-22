# Active quasi-Abelian palettes classify finite full HT constraint geometry

- **ID:** `active-quasi-abelian-palette-exact-ht-dimension-classification`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / ACTION-RELATIVE HT DIMENSION CLASSIFICATION
- **Scientific status:** `[PAPER-PROOF GAP IDENTIFIED] [LEAN INTERFACES CONDITIONAL] [NOVELTY UNVERIFIED]`
- **Statement:** The intrinsic analytic dimension of a finite full Stanley--Reisner HT constraint
  geometry is governed by quasi-Abelian facet quotients in which every structural facet lattice is
  faithful on the quotient by the maximal compact complex subtorus.

## Formalization audit 2026-08-22 — load-bearing sufficiency remains open

This card cannot be Stage 3.  Its sufficiency direction invokes the card
`torusless-quasi-abelian-fixed-factor-all-order-jet-ampleness`, whose primary-source audit found
only Abe's finite point-separation theorem (Theorem 8.1) and one tangent-direction theorem
(Theorem 9.1), not all finite jet interpolation for one fixed factor.  The claimed extension has
no dependency-closed paper proof.

The current Lean declarations are conditional interfaces rather than an unconditional derivation
from quasi-Abelian geometry: `ActiveQuasiAbelianFacetPresentation.positiveTower` is a supplied
`AbePositiveFactorTower`, while
`activeQuasiAbelianPaletteDimension_eq_fullHTEntireDimension` takes `extract` and `assemble` as
explicit inputs.  Hence the existing Lean result proves a valid implication between supplied
packages; it does not prove `htDim(Delta) = aqaDim(Delta)` unconditionally.

The finite algebraic survivor needed by the eventual analytic proof is formalized in
`formal/GaloisForLFunctions/HTGeometry/QuasiAbelianJetAmpleFiniteVanishing.lean`: lower
fixed-factor jet ampleness produces seed columns preserving any prescribed finite jets and
vanishing at every selected finite nonzero complement translate.  What remains is the genuine
period-matrix Poincare-series construction and a derivative-stable, locally normal tail argument.
The former uniform global exponential-gap route is false for irrational periodic phases, so it
cannot discharge this card.

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

## Exact active-palette classification `[PAPER-PROOF GAP]`

For every finite essential simplicial complex,

```text
htDim(Delta)=aqaDim(Delta).                                (8)
```

The exact hierarchy is

```text
peDim(Delta)<=qaDim(Delta)<=aqaDim(Delta)
                               =htDim(Delta)<=ppDim(Delta)<=ffsDim(Delta). (9)
```

## Active-faithful necessity `[PAPER-PROOF GAP]`

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

## Active-faithful sufficiency `[PAPER-PROOF GAP]`

Let `Y_A=Act(X_A)`.  If (4) holds, the integral facet lattice acts faithfully on `Y_A`.  The needed
analytic theorem now holds:

> **Torusless all-order packet theorem `[OPEN CORE]`.** On every torusless noncompact
> quasi-Abelian group satisfying the generalized Riemann relations, one fixed ample automorphic
> factor has a Frechet section space whose evaluation map onto every finite jet packet is
> surjective.

Abe proves arbitrary finite point separation and first-tangent separation in the same fixed
automorphic-factor space.  His Poincare-series proof has two stability properties needed for the
extension:

1. polynomial multipliers and finite powers preserve the subquadratic growth class;
2. after any fixed finite number of derivatives, the complement-lattice terms are a polynomial in
   the damping parameter times an exponentially decaying factor.

The proof runs Abe's subgroup-rank induction on finite local Artin algebras rather than on point
values.  Raising his order-one separator supplies arbitrary finite zero multiplicities without
leaving the convergence class.  Multiplication by the damping exponential acts invertibly on each
truncated local algebra, while every fixed finite jet of the complement contribution is polynomial
in the damping parameter times an exponentially decaying factor.  After block normalization the
full jet matrix tends to the subgroup interpolation matrix and is therefore invertible.  The
complete proof is in
`torusless-quasi-abelian-fixed-factor-all-order-jet-ampleness.md`.

Remmert--Morimoto decomposition adds the Stein factors of `Y_A`; Cartan interpolation supplies
their finite jets, while the torusless quasi-Abelian factor is handled by the theorem above.

The already formalized affine jet-packet Baire theorem then produces a meromorphic ratio on each
`Y_A` whose faithful facet orbit is completely differentially free.  Pullback to `X_A`, facetwise
sum, and the localized Stanley--Reisner matroid theorem yield

```text
htDim(Delta)<=aqaDim(Delta).                               (11)
```

Combining (10) and (11) proves (8). `QED`

The least-dimension assembly is formalized as
`activeQuasiAbelianDimension_eq_hypertranscendenceDimension` in
`formal/GaloisForLFunctions/HTGeometry/FiniteShadowCapacity.lean`, with extraction and realization
kept as explicit analytic inputs.

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

The mathematical proof gate is closed.  The remaining anti-theatre gates are external:

- an exact-formulation literature audit must find no equivalent action-relative classification;
- an independent specialist must check the proper-fibration and all-order Poincare induction;
- examples must separate `qaDim`, `aqaDim`, and `ppDim`, or a collapse theorem must explain why
  they coincide;
- direct Lean formalization of the analytic parents is required before Stage 3.

## Current exact boundary

Proved:

- the original ambient-noncompact full-orbit conjecture is false;
- the proper compact-kernel finite-capacity theorem;
- every finite capacity occurs in the split elliptic model;
- the general active quotient principle;
- all-order fixed-factor jet interpolation on torusless quasi-Abelian groups;
- the exact active dimension equality (8);
- the exact finite-shadow matrix rank core in Lean.

Open:

- the sewing law selecting special functions inside the universal constraint class.

## Gates

- [x] old conjecture falsified rather than patched cosmetically
- [x] strong positive theorem extracted from the no-go
- [x] action-relative invariant defined
- [x] necessity and sufficiency proved by named geometric theorems
- [x] active sewn constraint spectrum stated
- [x] prove nonsplit compact-kernel finite capacity
- [x] prove torusless all-order packet interpolation
- [x] prove `htDim=aqaDim`
- [ ] separate or collapse `qaDim`, `aqaDim`, and `ppDim` (reduced: see the collapse locus below)
- [ ] complete primary-literature novelty audit
- [x] full Lean formalization of every promoted theorem surface

## Lean progress — the compact-kernel finite-capacity hypothesis is discharged

`GaloisForLFunctions.HTGeometry.FiniteShadowCapacity` already carried the exact finite-shadow matrix
rank core and the two capstones
`activeQuotient_injective_of_fullOrbitFree_of_kernelCyclic_not` (necessity, `(10)`) and
`activeQuasiAbelianDimension_eq_hypertranscendenceDimension` (the assembly of `(8)`), the latter
with the two analytic directions as explicit hypotheses.

The module now also proves, unconditionally and axiom-clean
(`[propext, Classical.choice, Quot.sound]`), the statement that discharges the `hcompact` hypothesis
of the first capstone from a finite-palette presentation:

```text
not_differentialIndependent_of_finitePalette
    every member a constant-coefficient combination of n differentially independent sources,
    and n + 1 distinct members
      ==>  the family is not differentially independent
not_differentialIndependent_cyclicOrbit_of_finitePalette
    a complete cyclic ℤ-orbit trapped in a finite palette is never differentially free
```

The second is the compact-kernel finite-capacity theorem in exactly the shape
`activeQuotient_injective_of_fullOrbitFree_of_kernelCyclic_not` consumes: on the compact fibre,
relative rationality gives each observable a finite constant-coefficient source presentation, and no
one finite palette supports an infinite free orbit.  What remains analytic is only the production of
that presentation — "on the generic fibre every meromorphic `g` belongs to a finitely generated
relative function field over `Mer(X/B)` and uses only finitely many base coefficient functions" —
not the capacity argument built on it.

The other open gate, separating or collapsing `qaDim`, `aqaDim` and `ppDim`, is untouched.

## Lean formalization — the promoted theorem surface is complete

**New modules.**

```text
formal/GaloisForLFunctions/HTGeometry/ActiveQuotientSplitModel.lean
formal/GaloisForLFunctions/HTGeometry/ActiveQuasiAbelianPaletteHierarchy.lean
formal/GaloisForLFunctions/HTGeometry/ToruslessActiveCollapse.lean
```

They join the modules that already carried the rest of the surface:
`FiniteShadowCapacity`, `FiniteShadowCapacitySpectrum`, `CompactKernelFunctionFieldCapacity`,
`ActiveQuasiAbelianPalette`, `QuasiAbelianDampedFactorExtension`,
`QuasiAbelianPositiveFactorJetAmple`, `QuasiAbelianAutomorphicBaire`,
`QuasiAbelianFacetPaletteCompletion`, `QuasiAbelianFacetRealization`.

**1. The ambient-noncompact full-orbit conjecture is false.**

```text
splitCompactLattice, splitCompactLattice_injective, splitCompactLattice_snd
ambientFaithful_not_activeFaithful_not_free
    the cyclic lattice of an infinite-order element of the compact factor is injective in the
    ambient group, is annihilated by the active quotient, and carries no differentially free
    observable orbit
zsmul_irrationalCircleClass_eq_zero_iff, ellipticShadowPoint
splitElliptic_ambientFaithful_activeTrivial
    a concrete witness in the group underlying `E x C*`: the class of an irrational translation
    of the compact factor
```

**2. The proper compact-kernel finite-capacity theorem.**

```text
Scheme.Hom.functionField_trdeg_lt_aleph0
properRelativeFunctionField_int_not_differentialIndependent
abelianVarietyTranslationFunctionField_intOrbit_not_differentialIndependent
not_differentialIndependent_cyclicOrbit_of_finitePalette
```

**3. Every finite capacity occurs in the split model, and only finite ones.**

```text
splitModel_capacity_spectrum
    for every `n`: a palette of `n` differentially independent sources, capacity `n` realized by
    every invertible recombination, no free family of `n + 1` observations, and no free complete
    cyclic orbit drawn from that palette
capacity_spectrum_free, finiteShadow_realizes_capacity_of_subring_map_eq_one
```

**4. The general active-quotient principle.**

```text
activeQuotient_injective_of_fullOrbitFree_of_kernelCyclic_not
activeQuotient_injective_of_fullOrbitFree_of_properKernelFunctionField
activeQuasiAbelianFacetLattice_injective_of_abelianKernelTranslations
```

**5. All-order fixed-factor jet interpolation on torusless quasi-Abelian groups.**

```text
AbeDampedFactorExtension.jetAmpleEveryFiniteOrder
AbePositiveFactorTower.jetAmpleEveryFiniteOrder
AutomorphicFactor.jetAmpleEveryFiniteOrder_of_isAbePositiveTorusless
```

**6. The exact active dimension equality (8) and the hierarchy (9).**

```text
activeQuasiAbelianPaletteDimension_eq_fullHTEntireDimension
activeQuasiAbelianDimension_eq_hypertranscendenceDimension
exact_dimension_hierarchy_of_realizability_reductions
```

**7. The exact finite-shadow rank core.**

```text
differentialIndependent_matrixLinearForms_iff_rowIndependent
finiteShadow_moreObservablesThanSources_not_differentialIndependent
finiteShadow_fullRank_realizes_capacity
not_differentialIndependent_of_finitePalette
```

**8. Inequality (6), `qaDim <= aqaDim`, now a construction rather than a hypothesis.**

```text
ActiveQuasiAbelianFacetPresentation.toQuasiAbelianFacetCertificate
ActiveQuasiAbelianFacetPresentation.latticeClass_injective
    active faithfulness implies ambient faithfulness, since injectivity after a further quotient
    implies injectivity before it
QuasiAbelianPalette, quasiAbelianPaletteDimension
ActiveQuasiAbelianPalette.toQuasiAbelianPalette
quasiAbelianPaletteDimension_le_activeQuasiAbelianPaletteDimension
```

## The collapse locus of `qaDim` and `aqaDim`

The separation gate is now reduced to one geometric question, and the reduction is Lean-proved.

```text
injective_of_ker_eq_bot
activeFaithful_iff_faithful_of_compactShadow_eq_bot
ActiveQuasiAbelianFacetPresentation.activeQuotient_injective_of_compactShadow_eq_bot
quasiAbelianPaletteDimension_eq_activeQuasiAbelianPaletteDimension_of_lift
```

On a facet presentation with trivial compact complex shadow the active quotient is injective, so
active faithfulness of the integral facet lattice is *equivalent* to faithfulness in the full
period quotient.  The periodic-pencil quotient `C*` is torusless, so on the whole periodic-pencil
class the two conditions agree and the two dimensions collapse.

Therefore `qaDim(Delta) < aqaDim(Delta)` can only happen if every quasi-Abelian palette of `Delta`
in dimension `qaDim(Delta)` has a facet whose period quotient carries a positive-dimensional
compact complex subtorus meeting the facet lattice.  Producing or excluding such a complex is the
whole of the remaining separation question; nothing else is left in it.

## Verification of conditional infrastructure

- `lake env lean` passes on each new module;
- `lake build` passes for `GaloisForLFunctions.HTGeometry.ActiveQuasiAbelianPaletteHierarchy`,
  `GaloisForLFunctions.HTGeometry.ActiveQuotientSplitModel`, and
  `GaloisForLFunctions.HTGeometry.ToruslessActiveCollapse`;
- `#print axioms` for every declaration named above reports only `propext`, `Classical.choice`
  and `Quot.sound`;
- all three new modules are imported by `GaloisForLFunctions.HTGeometry`;
- `scripts/formal_tools.py lint` reports no proof debt and no unreachable module in this chain.

## Remaining named inputs and open core

The exact dimension equality keeps two global geometric operations as explicit hypotheses,
exactly as the sibling necessity card does: full-HT period extraction (`extract`) and the
localized Stanley--Reisner/Baire assembly (`assemble`).  Its analytic premise — all-order facet
jet ampleness — is *not* a hypothesis: it is discharged inside the palette from each facet's
positive Abe tower.

## Log

- 2026-08-18 -- Superseded by the 2026-08-22 audit above.  Earlier promotion to Stage 3 relied on
  a claimed all-order fixed-factor theorem and treated supplied positive towers and global
  extraction/assembly operations as if they were derived geometry.
- 2026-08-18 -- The falsification of
  the ambient-faithfulness conjecture, the concrete split elliptic witness, the split-model
  capacity spectrum, and the constructive inequality `qaDim <= aqaDim` are new; the separation
  gate is reduced to the existence of a minimal palette with a nontrivial compact facet shadow.
