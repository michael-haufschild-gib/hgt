# Unary observer-operation Galois repair — Lean certification

- **ID:** ULF-LSM-2
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/law-saturation-mechanics/unary-observer-operation-galois-repair-and-descent-no-go-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveUnaryLawRepair`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified declarations

`UnaryLawClosure F E` is the intersection of all equivalence relations containing `E` and preserved
by every unary operation in `F`.

- `unaryLawClosure_equivalence` proves the closure is an equivalence.
- `unaryLawClosure_contains` proves it retains all declared observer identifications.
- `unaryLawClosure_preserves` proves every source law remains executable.
- `unaryLawClosure_least` proves universal minimality.
- `unaryLawClosure_fixed_iff` identifies executable observer doctrines with fixed points.
- `descended_iff_observerKernel_preserved` proves exact quotient descent.
- `no_descended_of_not_observerKernel_preserved` proves the no-descent law.
- `unaryLawClosure_subset_observerKernel_of_descents` proves every observer retaining all source laws
  contains the canonical repair.
- `unaryLawClosure_mono` proves adding laws or identifications only coarsens observation.

The capstone `unaryLawRepairMechanism_closed` packages the operation--observer mechanism without an
RH, analytic, topological, or route-specific premise.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveUnaryLawRepair.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveUnaryLawRepair
lake env lean /tmp/ConstitutiveUnaryLawRepairAxioms.lean
../scripts/formal_tools.py lint --check-generated
```

All checks passed. Axiom output contains only Lean/mathlib foundations `propext`,
`Classical.choice`, and `Quot.sound`. No project axiom, theorem premise, `sorry`, `admit`, `opaque`,
`unsafe`, or computation certificate is used.

## Exact field consequence

Observer loss is computed, not postulated: the least relation compatible with retained source laws
is canonical, and every observer on which those laws descend must erase at least those distinctions.
