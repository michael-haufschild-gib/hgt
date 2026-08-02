# Every full HT facet lattice is faithful on its active quasi-Abelian quotient

- **ID:** `active-quasi-abelian-facet-palette-necessity`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / NECESSARY ACTION-RELATIVE SOURCE GEOMETRY
- **Scientific status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Statement:** In every finite full Stanley--Reisner HT differential-matroid realization, the
  complete integral lattice of each facet embeds in the period quotient after its maximal compact
  complex subtorus is removed.
- **Formal module:**
  `formal/GaloisForLFunctions/HTGeometry/CompactKernelFunctionFieldCapacity.lean`.

## Setup

Let `F` be a scalar meromorphic realization of the exact full localized Stanley--Reisner
differential matroid of a finite essential complex `Delta`.  For a facet `A`, the established facet
separator produces

```text
G_A=q_A(T)F
```

such that:

1. the complete orbit `{T^n G_A:n in Z^A}` is differentially algebraically independent;
2. the full period quotient `X_A` is noncompact and quasi-Abelian;
3. the complement incidence is exact;
4. `Z^A -> X_A` is injective;
5. `X_A` satisfies the generalized Riemann relations.

Let `B_A` be the maximal compact connected complex subgroup of `X_A`.  It is an Abelian variety.
Define the active quotient

```text
Act(X_A)=X_A/B_A.
```

## Active facet theorem `[PROVED HERE]`

The composite

```text
Z^A -> X_A -> Act(X_A)                                   (1)
```

is injective.

### Proof

Assume that a nonzero `n in Z^A` lies in the kernel of (1).  Because `Z^A` is torsion-free, the
map

```text
Z -> Z^A,   k |-> k n                                    (2)
```

is injective.  Restricting the complete facet orbit along (2) preserves differential algebraic
independence.  Hence

```text
{T^(kn)G_A:k in Z}                                       (3)
```

has infinite differential transcendence degree.

But the translation class of `n` lies in the compact Abelian kernel `B_A`.  The proper
compact-kernel theorem applies to the quotient `X_A -> Act(X_A)`: every meromorphic observable uses
only finitely many coefficient functions in the relative Abelian function field, and compact
kernel translation introduces no new coefficients.  Therefore the complete cyclic orbit (3) has
finite differential transcendence degree.  Contradiction.  Thus (1) is injective. `QED`

## Dimension consequence `[PROVED HERE]`

Let `aqaDim(Delta)` be the least ambient dimension of a quasi-Abelian facet palette satisfying the
existing exact incidence, generalized Riemann, and lattice conditions together with active
faithfulness (1).  Every full HT realization supplies such a palette in its own dimension.  Hence

```text
aqaDim(Delta)<=htDim(Delta).                              (4)
```

Together with the previous hierarchy,

```text
peDim<=qaDim<=aqaDim<=htDim<=ppDim<=ffsDim.               (5)
```

The remaining equality `htDim=aqaDim` is a sufficiency problem: prove all-order fixed-factor jet
interpolation on torusless quasi-Abelian quotients.

## Scientific meaning

Ambient noncompactness and faithfulness in the full period quotient are not the correct necessary
conditions.  A structural action can be faithful while moving only in a compact complex shadow,
where every single observable has finite orbit capacity.  The theorem identifies the first
action-relative law constraining hypertranscendental functions:

> A completely free structural orbit must be faithful at infinity, after all compact complex
> directions have been quotiented out.

This converts the elliptic-shadow no-go into a universal positive restriction on every facet of a
finite full HT constraint geometry.

## Lean status

The relative function-field source and the complete facet theorem are now formalized directly.
`CompactKernelFunctionFieldCapacity.lean` proves:

```text
Scheme.Hom.functionFieldPullback_essFiniteType
Scheme.Hom.functionField_trdeg_lt_aleph0
properRelativeFunctionField_int_not_differentialIndependent
abelianVarietyTranslationFunctionField_intOrbit_not_differentialIndependent
activeQuotient_injective_of_fullOrbitFree_of_properKernelFunctionField
activeQuotient_injective_of_fullOrbitFree_of_abelianKernelTranslations
activeQuasiAbelianFacetLattice_injective_of_abelianKernelTranslations
activeQuasiAbelianDimension_le_hypertranscendenceDimension
```

The generic-stalk proof derives essential finite type from `LocallyOfFiniteType.stalkMap`, then
derives finite relative transcendence degree.  Differential independence would imply countable
algebraic independence of zero-jets, contradicting that finite bound.  The Abelian specialization
uses literal powers of a rational point and the actual scheme-translation pullback on the function
field.  The final facet theorem specializes the lattice to `Z^F` and proves its torsion-free cyclic
embedding internally; compact-kernel cyclic non-independence is no longer a hypothesis.

No compact-kernel statement is installed as an axiom, and the module contains no `sorry`, `admit`,
`axiom`, `opaque`, or `unsafe` declaration.

Verification on 2026-08-02:

- direct `lake env lean GaloisForLFunctions/HTGeometry/CompactKernelFunctionFieldCapacity.lean`
  passed;
- `lake build GaloisForLFunctions.HTGeometry.CompactKernelFunctionFieldCapacity` passed;
- `#print axioms` for every theorem listed above reports only `propext`, `Classical.choice`, and
  `Quot.sound` (the dimension inequality uses none);
- module is imported by `GaloisForLFunctions.HTGeometry`;
- repository lint finds no debt in this module; its sole current error is an unrelated unreachable
  RHTower module, `CriticalHalfDensityPrimeTailResolventLaw`.

## Parent and novelty boundary

Parent inputs are the generalized Riemann period theorem of Capocasa--Catanese, proper direct-image
and relative function-field finiteness for Abelian fibrations, finite transcendence degree of
Abelian function fields, and the established project facet-separation theorem.  Searches did not
locate the action-relative conclusion (1), inequality (4), or an equivalent differential-orbit
capacity theorem.  Novelty remains unverified pending specialist audit.

## Gates

- [x] exact facet orbit extracted
- [x] proper compact-kernel finite-capacity theorem proved
- [x] compact collision converted to a cyclic differential-rank contradiction
- [x] active quotient lattice injection proved
- [x] dimension inequality `aqaDim<=htDim` proved
- [x] algebraic implication formalized in Lean
- [ ] independent complex-geometric proof audit
- [ ] exact-formulation literature audit
- [x] relative function-field theorem directly formalized
- [x] literal Abelian translation orbit directly formalized
- [x] complete active facet lattice theorem directly formalized
- [x] promoted to Stage 3
