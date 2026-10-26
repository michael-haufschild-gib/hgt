# Kernel-checked first-atom quadrature

- **ID:** kernel-checked-first-atom-quadrature
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** User request to replace native decision proofs in PA order-24 quadrature and rank-four Milnor-to-Steinberg surjectivity.
- **Statement:** Preserve the original theorem statements using kernel-checked arithmetic, without additional assumptions, axioms, or increased proof limits.

## Proof

Three distinct indices cannot exhaust `Fin 4`: their finite set has cardinality three,
whereas the universe has cardinality four. This supplies the complement used by the
Milnor-to-Steinberg surjectivity proof.

For quadrature, each rational coefficient is enclosed by integer numerators over `10^30`.
Addition and negation preserve containment; products lie between their four corner products.
Integer floor and ceiling division round these bounds outward. Induction then proves
containment for polynomial multiplication, Horner composition, and integration. Monotonicity
of the original endpoint rounding maps preserves containment through the endpoint recurrence.

Equality certificates normalize all five required rows on each of the 64 cells. Summing their
integer numerators proves the five strict numerical comparisons. The enclosure inequalities
transfer these comparisons to the original rational masses, and the unchanged analytic proof
transfers them to the real moments. The original rational definitions retain their names and
values in `PrimeArchThetaFirstAtomQuadratureEnclosures`.

## Lean declarations

- `RHTower.ThetaRationalQuadrature.Enclosure.contains_massLo`
- `RHTower.ThetaRationalQuadrature.Enclosure.contains_massHi`
- `RHTower.ThetaRationalQuadrature.firstAtom_bounds`
- `RHTower.thetaRationalQuadrature_firstAtom_bounds`
- `RHTower.thetaCuspFirstAtom_highOrder_five_bounds`
- `GaloisForLFunctions.HTGeometry.exists_fin4_fourth`
- `GaloisForLFunctions.HTGeometry.fin4_steinbergSymbol_index_independent`
- `GaloisForLFunctions.HTGeometry.milnorKTwoToFin4SteinbergKTwoCenter_surjective`
- `GaloisForLFunctions.HTGeometry.milnorKTwoQuotientKerEquivFin4SteinbergKTwoCenter`

## Verification

Both final source checks passed, from `formal/`:

```sh
lake --old env lean GaloisForLFunctions/RHTower/PrimeArchThetaFirstAtomHighOrderMomentBounds.lean
lake --old env lean GaloisForLFunctions/HTGeometry/MilnorKTwoSteinbergSurjective.lean
```

The three final PA declarations and four HT declarations listed above were audited with
`#print axioms`; every audit returned only `propext`, `Classical.choice`, and `Quot.sound`.
All 64 cells and all five global inequalities passed with default proof limits. The final PA
check retained two existing sequence-focus linter warnings; it exited successfully.

The twenty helper modules are wired into `RHTower.lean`. Certificates are split into four-cell
modules to bound elaboration memory. No umbrella or full build was run. Temporary probes and
axiom-print commands are removed. Stale target olean/ilean artifacts and their hash/trace
metadata are removed; valid helper artifacts remain available to import.
