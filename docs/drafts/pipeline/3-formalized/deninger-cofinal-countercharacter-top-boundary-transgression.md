# Deninger cofinal countercharacter top-boundary transgression

- **ID:** `deninger-cofinal-countercharacter-top-boundary-transgression`
- **Route:** L — Deninger/Hodge/cohomological realization
- **Status:** `[FORMALIZED] [NOVELTY UNVERIFIED]`
- **Date:** 2026-08-03
- **Paper proof:**
  `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/deninger/deninger-cofinal-countercharacter-top-boundary-transgression.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.DeningerCofinalCountercharacterTopBoundaryTransgression`

## Formalized theorem set

Lean constructs the scaled finite Tate forward family and proves that its failure to commute with
cofinal zero-extension is exactly the scalar gain times the existing rank-one top boundary:

```text
deningerScaledTateForward
deningerScaledTateForwardNaturalityDefect
deningerScaledTateForwardNaturalityDefect_eq_topBoundary
```

It then instantiates the gain by the raw Deninger half-density character and by the covariantly
flat countertransported gain.  Their flat-minus-raw difference is the literal preclosure relative
class:

```text
deningerRawCofinalTateDefect
deningerCountertransportedCofinalTateDefect
deningerRelativeCofinalTateDefect
deningerRelativeCofinalTateDefect_eq
```

Critical reflection polarizes this class to the tensor-square mate curvature times the nonzero
Tate top boundary.  The new-top-coordinate reader normalizes the generator to one and detects the
critical line exactly:

```text
deningerRelativeCofinalTateDefect_reflection_sub_source
deningerCofinalTopBoundaryCoefficient
deningerCofinalTopBoundaryCoefficient_topBoundary_basis_last
deningerCofinalTopBoundaryCoefficient_reflectedRelativeDefect
deningerRelativeCofinalTateDefect_reflected_basis_eq_zero_iff
```

At clock six the reader is identified with the actual ordered `(2,3)` Gamma/Calderón--Witt
coefficient.  A finite-support completed Xi vector carries that coefficient into the existing
completed cross-prime incidence carrier, whose decoded source value is mate curvature times the
actual nonzero incidence witness:

```text
deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_cofinalTopBoundary
deningerCofinalRelativeBocksteinXiVector
deningerCofinalRelativeBocksteinIncidence
deningerCofinalRelativeBocksteinIncidence_sourceValue
deningerCofinalRelativeBocksteinIncidence_sourceValue_eq_zero_iff_gamma
```

All statements are unconditional.  The module neither assumes nor proves source Stokes
annihilation.

## Verification

Commands run from `formal/`:

```text
lake env lean GaloisForLFunctions/RHTower/DeningerCofinalCountercharacterTopBoundaryTransgression.lean
lake build GaloisForLFunctions.RHTower.DeningerCofinalCountercharacterTopBoundaryTransgression
lake env lean /tmp/hgt_route_l_cofinal_countercharacter_axioms.lean
```

Results:

- direct Lean check: pass;
- targeted module build: pass; no full build run;
- module wired into `GaloisForLFunctions.RHTower`;
- axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`;
- `scripts/formal_tools.py lint`: new module is reachable and has no forbidden declaration; global
  command exits nonzero only because unrelated concurrent cyclic/adelic/sieve modules are not yet
  reachable from the umbrella.

## Frontier consequence

The construction and coefficient-faithful finite-fibre landing clauses of
`RELATIVE_COUNTERCHARACTER_STOKES_ANNIHILATION` are closed.  The remaining Route-L theorem is now
exactly the ordinary-integer source statement:

```text
[ORDINARY_INTEGER_GREEN_STOKES_ANNIHILATION]

Compare completed/cofinal Xi Green provenance with the relative Tate top-boundary
class and prove source Stokes vanishing, compatibly with Gamma/co-Poisson Hodge
boundary and completed Calderón--Witt incidence, without assuming the equivalent
Gamma/mate-curvature vanishing.
```

The exact top-coordinate reader proves that generic finite exactness, cyclicity, mapping-cone
formalism, or countertransport cannot supply this annihilation.
