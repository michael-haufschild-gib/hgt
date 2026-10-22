# Literal B2 lower-Weyl radial detector — Lean certificate

- **Paper card:** `rbh-pw-b-literal-b2-lower-weyl-radial-detector.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralCyclicPeierlsLowerWeylRadialDetector`,
  `ThetaCuspHawkingBMLiteralCyclicPeierlsSelfInverseSquarePhysical`,
  `ThetaCuspHawkingBMLiteralCyclicPeierlsAffineCuspIncidence`, `ThetaCuspHawkingBMMixedRadialOverlap`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake --old env lean` clean; `#print axioms` = `propext`, `Classical.choice`,
  `Quot.sound`; no `sorry`.

| Card item | Lean theorem |
|-|-|
| bulk overlap `= P(R)(overlapConstant + overlapInverseSquare/R²)` | `bulkOverlapCoefficient_eq` |
| `L(q) = ½Λ(2q-1)²Λ(q-1)(1-q/2)`; zero iff `Λ(2q-1) = 0` | `lowerWeylFaceCoefficient`, `lowerWeylFaceCoefficient_eq_zero_iff` |
| `overlapInverseSquare s w ≠ 0` (all branch/side cases) | `self_overlapInverseSquare_ne_zero` |
| normalized lower coefficient `A + L·I/R²` cannot vanish at both `R = 2, 3` (any radial-constant `A`) | `lowerWeylRadialDetector`, `lowerWeylRadialDetector_two_or_three_ne_zero` |
