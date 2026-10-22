# Deninger--Burnol conormal radial top-boundary comparison — formalization certificate

- **ID:** `deninger-burnol-conormal-radial-top-boundary-comparison`
- **Route:** L — Deninger/Hodge/cohomological realization
- **Stage:** 3-formalized
- **Paper proof:**
  `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/deninger/deninger-burnol-conormal-radial-top-boundary-comparison.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.Deninger.DeningerBurnolConormalRadialTopBoundaryComparison`

## Unconditional formal content

- `deningerBurnolActualCenteredConormalCharacter`: centered ratio of the actual nested
  exact-multiplicity Burnol Mellin jets at logarithmic ordinary-integer aperture.
- `deningerBurnolActualCenteredConormalCharacter_eq`: identifies that ratio with the literal
  centered Burnol source character.
- `iteratedDeriv_burnolCoPoissonExpWindowZetaMellinGerm_log_nat_ne_zero`: proves the exact
  conormal jet is nonzero at every Xi divisor and every clock `n ≥ 2`.
- `norm_deningerBurnolActualCenteredConormalCharacter_sq`: identifies squared character norm with
  Deninger half-density mate gain.
- `deningerBurnolActualConormalRadialReflectionDefect_eq`: identifies the reflected radial
  discriminant with Deninger tensor-square mate curvature.
- `deningerCofinalTopBoundaryCoefficient_eq_burnolConormalRadialDefect`: compares actual Burnol
  conormal directly with the concrete cofinal Tate top-boundary reader.
- `deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_burnolConormal`: compares clock-six
  Burnol radial defect with actual Gamma/Calderón--Witt boundary coefficient.
- `deningerCofinalRelativeBocksteinIncidence_sourceValue_eq_burnolConormal`: identifies decoded
  completed incidence value with the same physical source coefficient times its nonzero witness.
- `deningerBurnolActualConormalRadialReflectionDefect_eq_zero_iff`: proves exact critical-line zero
  set without asserting universal vanishing.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerBurnolConormalRadialTopBoundaryComparison.lean
lake build GaloisForLFunctions/RHTower/Deninger/DeningerBurnolConormalRadialTopBoundaryComparison.lean:olean
lake env lean /tmp/hgt_route_l_burnol_deninger_axioms.lean
```

Direct target check and targeted module build pass.  Axiom audit reports only standard quotient,
choice, and propositional extensionality dependencies inherited from mathlib.  No `sorry`,
`admit`, project `axiom`, `opaque`, or `unsafe` declaration is introduced.

## Frontier effect

Physical Burnol co-Poisson conormal, Deninger relative top boundary, actual Gamma boundary, and
completed Calderón--Witt incidence now compare coefficient-faithfully.  The formal nonvanishing
theorem kills the Mellin-jet/Bockstein shortcut: differentiation retains horizontal location and
does not annihilate it.  Remaining open theorem is pre-specialization ordinary-integer Green--
Stokes annihilation of this exact coefficient.
