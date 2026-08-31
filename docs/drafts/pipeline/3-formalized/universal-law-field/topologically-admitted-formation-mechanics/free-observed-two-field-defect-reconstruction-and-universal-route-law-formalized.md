# Free observed two-field, defect reconstruction, and universal route law — Lean formalization

- **ID:** ULF-TAFM-14
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper source:** `free-observed-two-field-defect-reconstruction-and-universal-route-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.FreeObservedTwoField`
- **Status:** `[FORMALIZED] [NO SORRY] [NO ADDED AXIOMS] [NOT RH]`

## Certified objects

`LinearObservedTwoField k C₂ C₁ O` stores an algebraic rewrite boundary, observer, and
observer-boundary zero law. `LinearObservedTwoField.Hom` stores the three route layers and both
naturality squares.

For a `LinearInterventionGrammar`, `freeObservedTwoField` retains the unquotiented free rewrite and
history modules. `GeneratorRouteData` stores target images of primitive rewrite generators,
primitive history generators, a fixed observer map, and both primitive square proofs.

## Certified laws

1. `GeneratorRouteData.boundary_natural`: primitive rewrite compatibility reconstructs the complete
   boundary square.
2. `GeneratorRouteData.observer_natural`: primitive observer compatibility reconstructs the
   complete observer square.
3. `GeneratorRouteData.existsUnique_hom`: compatible primitive data generate exactly one route.
4. `boundaryDefect_reconstruction`: every global boundary defect is exactly the finite linear
   combination of primitive boundary defects.
5. `observerDefect_reconstruction`: every global observer defect is exactly the finite linear
   combination of primitive observer defects.
6. `boundaryDefect_eq_zero_iff` and `observerDefect_eq_zero_iff`: complete defect vanishing is
   equivalent to primitive defect vanishing.
7. `existsUnique_routeRepresentation_iff_generatorSquares`: primitive squares are necessary and
   sufficient for one unique chain-level route representation.
8. `generatorSquares_iff_defects_zero`: primitive-square compatibility is exactly joint zero defect.
9. `freeObservedTwoField_routeRepresentation_capstone`: one unique route exists iff both complete
   defect fields vanish.

## Verification

- Direct foreground elaboration:
  `lake env lean GaloisForLFunctions/HTGeometry/FreeObservedTwoField.lean`
- Targeted leaf build only: `2998/2998` jobs passed; changed direct dependency rebuilt
- Umbrella wiring: imported by `HTGeometry.UniversalLawField`; umbrella not built
- Axiom audit: ten significant declarations report only `propext`, `Classical.choice`, and
  `Quot.sound`

## Exact remaining producer

Extract a literal divisor-independent intervention signature and relation table, including target
rewrite witnesses, for at least three structurally different route organs. After primitive-square
certification, ULF-TAFM-14 removes every further finite linear compatibility obligation. Remaining
work is kernel faithfulness, topological/normed completion, and the ULF-TAFM-12 sublinear
curvature--filling theorem. No arithmetic instantiation or RH claim is formalized here.
