import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedActionCubicCoefficient

set_option autoImplicit false
set_option maxSynthPendingDepth 128

namespace RHTower.D4BMMixedActionSource
open GaloisForLFunctions.HTGeometry
open D4BMBackground D4BMMetricReconstruction D4BMActualMetricSource
open ComplexCoordinateMetricTwoJet MetricPathDensity D4BMActionSource
noncomputable section
local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-- Actual plus and minus fundamental fields, with independent scalar/vector amplitudes. -/
def literalModes (u aSp aVp aSm aVm : ℂ) : Fin 4 → MetricField :=
  ![literalField true u aSp aVp, literalField false u aSm aVm, fun _ => 0, fun _ => 0]

private theorem zero_space (p : ExteriorPoint) : fieldSpace p (fun _ => 0) = 0 := by
  have h := D4BMFullLinearEquation.fieldSpace_add p (fun _ => 0) (fun _ => 0)
    (fun _ _ => contDiffAt_const) (fun _ _ => contDiffAt_const)
  have he : fieldSpace p (fun _ => 0) = fieldSpace p (fun _ => 0) + fieldSpace p (fun _ => 0) := by
    convert! h using 1
    simp only [zero_add]
    rfl
  simpa using congrArg (fun q => q - fieldSpace p (fun _ => 0)) he.symm

private theorem zero_residual (p : ExteriorPoint) (i j : Fin 4) :
    D4BMLinearizedEinsteinSource.residual p (ofMetricField (fun _ => 0) p.val) i j = 0 := by
  rw [D4BMLinearizedEinsteinSource.residual, CoordinateMetricTwoJet.Linearization.cosmological,
    CoordinateMetricTwoJet.Linearization.einstein_eq_fderiv (actualJet p) _ (exterior_metric_det_ne_zero p)]
  change fderiv ℂ (einsteinComponent i j) (backgroundSpace p) (fieldSpace p (fun _ => 0)) + (-3) * 0 = 0
  simp only [zero_space, map_zero, mul_zero, add_zero]

private theorem literalModes_smooth (u aSp aVp aSm aVm : ℂ) (p : ExteriorPoint) (a i j : Fin 4) :
    ContDiffAt ℝ 2 (fun x => literalModes u aSp aVp aSm aVm a x i j) p.val := by
  fin_cases a
  · exact D4BMFullLinearEquation.literal_contDiffAt p _ u aSp aVp i j
  · exact D4BMFullLinearEquation.literal_contDiffAt p _ u aSm aVm i j
  · exact contDiffAt_const
  · exact contDiffAt_const

private theorem literalModes_first_zero (u aSp aVp aSm aVm : ℂ) (p : ExteriorPoint) (a i j : Fin 4) :
    deriv (source p (literalModes u aSp aVp aSm aVm a) i j) 0 = 0 := by
  have hz : deriv (source p (fun _ => 0) i j) 0 = 0 := by
    rw [(D4BMLinearizedEinsteinSource.source_hasDerivAt p (fun _ => 0)
      (fun _ _ => contDiffAt_const) i j).deriv, zero_residual]
  fin_cases a
  · exact D4BMFullLinearEquation.literal_plus_source_first_zero u aSp aVp p i j
  · exact D4BMFullLinearEquation.literal_minus_source_first_zero u aSm aVm p i j
  · exact hz
  · exact hz

/-- Both original BM branches discharge the full linearized equation in the mixed bulk pairing.
Every quadratic and cubic correction slot remains in the metric family. -/
theorem literal_mixedPairedCoefficient_eq (u aSp aVp aSm aVm : ℂ) (p : ExteriorPoint)
    (K L : Fin 4 → MetricField) (M : Mat)
    (hK : ∀ a i j, ContDiffAt ℝ 2 (fun x => K a x i j) p.val)
    (hL : ∀ a i j, ContDiffAt ℝ 2 (fun x => L a x i j) p.val) :
    let P := literalField true u aSp aVp
    let Q := literalField false u aSm aVm
    mixedPairedCoefficient p (literalModes u aSp aVp aSm aVm) K L M = ∑ i, ∑ j,
      (((actualJet p).metric⁻¹ * M * ((actualJet p).metric⁻¹).transpose) i j *
          (D4BMLinearizedEinsteinSource.residual p (ofMetricField (L 1) p.val) i j +
            secondVariation (backgroundSpace p) i j (fieldSpace p P) (fieldSpace p (K 1)) +
            secondVariation (backgroundSpace p) i j (fieldSpace p Q) (fieldSpace p (K 0)) +
            thirdVariation (backgroundSpace p) i j (fieldSpace p P) (fieldSpace p P) (fieldSpace p Q) / 2) +
        testWeightSlope (actualJet p).metric (Q p.val) M i j *
          (D4BMLinearizedEinsteinSource.residual p (ofMetricField (K 0) p.val) i j +
            secondVariation (backgroundSpace p) i j (fieldSpace p P) (fieldSpace p P) / 2) +
        testWeightSlope (actualJet p).metric (P p.val) M i j *
          (D4BMLinearizedEinsteinSource.residual p (ofMetricField (K 1) p.val) i j +
            secondVariation (backgroundSpace p) i j (fieldSpace p P) (fieldSpace p Q))) :=
  mixedPairedCoefficient_eq p (literalModes u aSp aVp aSm aVm) K L M
    (literalModes_smooth u aSp aVp aSm aVm p) hK hL (literalModes_first_zero u aSp aVp aSm aVm p)

/-- Premise-free mixed coefficient of the original affine BM metric. Besides the direct third
Einstein variation, both changing-weight contractions with the quadratic source remain. -/
theorem literal_affine_mixedPairedCoefficient (u aSp aVp aSm aVm : ℂ) (p : ExteriorPoint) (M : Mat) :
    let P := literalField true u aSp aVp
    let Q := literalField false u aSm aVm
    mixedPairedCoefficient p (literalModes u aSp aVp aSm aVm) (fun _ _ => 0) (fun _ _ => 0) M =
      ∑ i, ∑ j,
        (((actualJet p).metric⁻¹ * M * ((actualJet p).metric⁻¹).transpose) i j *
            (thirdVariation (backgroundSpace p) i j (fieldSpace p P) (fieldSpace p P) (fieldSpace p Q) / 2) +
          testWeightSlope (actualJet p).metric (Q p.val) M i j *
            (secondVariation (backgroundSpace p) i j (fieldSpace p P) (fieldSpace p P) / 2) +
          testWeightSlope (actualJet p).metric (P p.val) M i j *
            secondVariation (backgroundSpace p) i j (fieldSpace p P) (fieldSpace p Q)) := by
  have h := literal_mixedPairedCoefficient_eq u aSp aVp aSm aVm p
    (fun _ _ => 0) (fun _ _ => 0) M (fun _ _ _ => contDiffAt_const) (fun _ _ _ => contDiffAt_const)
  simpa only [zero_residual, zero_space, map_zero, zero_add, add_zero] using h

end
end RHTower.D4BMMixedActionSource
