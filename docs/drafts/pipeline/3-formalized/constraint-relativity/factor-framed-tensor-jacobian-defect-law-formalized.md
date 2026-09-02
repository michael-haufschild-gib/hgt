# Factor-framed tensor Jacobian defect law — formalized

- **ID:** `factor-framed-tensor-jacobian-defect-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `factor-framed-tensor-jacobian-defect-law.md`
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO PROJECT AXIOMS]`

## Lean modules

| Module under `HTGeometry/ConstraintRelativity/` | Role |
|---|---|
| `FactorFramedTensorJacobian` | heterogeneous pure-face Smith presentation, bar depths, lengths, homogeneous specializations |
| `FactorFramedTensorSoldering` | literal source/target map, factor compatibility, kernel/cokernel and length laws |
| `FactorFramedTensorFitting` | exact zeroth Fitting ideals |
| `FactorFramedTensorGradient` | factor potential derivation and universal Kähler soldering |
| `FactorFramedTensorKaehler` | actual Kähler presentation and literal Jacobian cokernel |
| `FactorFramedTensorTraceDual` | raw trace pairing and exact inverse-potential trace-dual lattice |
| `FactorFramedTensorClosedFibre` | coefficient reduction and literal closed-fibre quotient |
| `FactorFramedTensorNonmonogenic` | square-zero residue quotient and DVR nonmonogenic theorem |
| `TruncatedHardCoreFock` | compressed creators, face algebra, products, and phase transport |
| `FactorFramedTensorFockBridge` | literal polynomial quotient and `ℂ[[X]]` Jacobian closed fibre to creator algebra |
| `PowerSeriesResidue` | minimal shared equivalence `ℂ[[X]]/(X) ≃ ℂ` |

All are wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

1. `factorRawTraceDualCoordinateLattice_eq_inversePotentialLattice` proves `(4)` in the literal
   squarefree fraction-coordinate lattice using the unnormalized regular trace; the unit `2^d`
   is removed exactly under the card's `2 ∈ Rˣ` setup.
2. `factorKaehlerEquivPresentation` and `factorKaehlerEquivCotangentQuotient` prove `(5)` for the
   actual Kähler differential module of the polynomial quotient.
3. `factorFramedSoldering` and its coordinate/factor lemmas prove `(3)`--`(6)`, including the
   factorwise generator compatibility.
4. `factorKaehlerSolderingCokernelEquivJacobian` proves `(7)` and `(10c)` as an equivalence from
   the literal universal Kähler soldering cokernel to the literal critical/Jacobian algebra.
5. `factorGradientCokernelEquivFaceBars` proves heterogeneous `(20)` face by face;
   `factorGradientCokernel_length_eq_sum_weightedFaceDepth` and the closed formulas prove
   `(8)`--`(9)`, `(11)`--`(12)`, and `(21)`.
6. `factorCotangent_length`, `factorTraceQuotient_length`, and
   `factorFramedSolderingKernel_length_eq_cokernel` prove `(10)` and `(22)`.
7. `factorFramed_fittingIdealZero_source_eq_target` and
   `factorFramed_fittingIdealZero_eq_span_product` prove `(17)`.
8. `factorTensorOrder_not_monogenic_mod_uniformizer` proves `(10z)` for every DVR uniformizer and
   every positive depth vector with at least two factors.
9. `factorJacobianClosedFibreEquivSquarefreeFace` proves `(10f)` by exact coefficient reduction,
   not by defining a coordinate proxy. The face-bar decomposition gives `(10d)`--`(10e)`.
10. `complexFactorSquarefreeFaceAlgEquivCreatorAlgebra` proves the polynomial quotient form of
    `(27)` by a squarefree-face spanning theorem, creator relations, surjectivity, and exact finite
    rank comparison.
11. `complexPowerSeriesFactorJacobianClosedFibreEquivCreatorAlgebra` proves the literal card
    specialization: for every `n`, the actual depth-one factor-Jacobian algebra over `ℂ[[X]]`,
    reduced at `X = 0`, is ring-equivalent to the full compressed creator algebra on faces of size
    at most `n`.
12. `truncatedFockPhase_faceCreator` proves `(29)` for every real weight vector and every face.

## Verification

Direct checks used only `lake env lean <file>`. Final audits used only targeted builds, including:

```text
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.FactorFramedTensorSoldering
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.FactorFramedTensorFitting
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.FactorFramedTensorNonmonogenic
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.FactorFramedTensorKaehler
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.FactorFramedTensorTraceDual
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.PowerSeriesResidue
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.FactorFramedTensorFockBridge
```

No umbrella build was run. `#print axioms` for the principal declarations returns only `propext`,
`Classical.choice`, and `Quot.sound`.
