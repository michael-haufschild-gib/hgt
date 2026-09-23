import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuadraticMixedSource
namespace RHTower.D4BMQuadraticMixedSource
open GaloisForLFunctions.HTGeometry D4BMScalarLinearEquation D4BMQuadraticAngularSource
open ComplexCoordinateMetricTwoJet
noncomputable section

private theorem jet_zero_mul (J : ScalarTwoJet (Fin 4) ℂ) :
    (ScalarTwoJet.constant 0).mul J = ScalarTwoJet.constant 0 := by
  ext <;> simp [ScalarTwoJet.mul, ScalarTwoJet.constant]
private theorem jet_mul_zero (J : ScalarTwoJet (Fin 4) ℂ) :
    J.mul (ScalarTwoJet.constant 0) = ScalarTwoJet.constant 0 := by
  ext <;> simp [ScalarTwoJet.mul, ScalarTwoJet.constant]
private theorem temporal_zero (s r : ℂ) : temporalRadial s r 0 = ScalarTwoJet.constant 0 := by
  ext k l
  · rfl
  · fin_cases k <;> simp [temporalRadial, ScalarTwoJet.constant]
  · fin_cases k <;> fin_cases l <;> simp [temporalRadial, ScalarTwoJet.constant]

private theorem scalar_zero (s r y S Sx Sy Sxx Sxy : ℂ) :
    toSpace (scalarJet s r y 0 S Sx Sy Sxx Sxy) = 0 := by
  simp [scalarJet, temporal_zero, jet_zero_mul, toSpace]
  simp only [ScalarTwoJet.constant]
  exact ⟨rfl, rfl, rfl⟩

private theorem coexact_zero (s r y S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) :
    toSpace (coexactJet s r y 0 S Sx Sy Sxx Sxy Sxxx Sxxy) = 0 := by
  simp [coexactJet, D4BMVectorLinearEquation.vectorJet, temporal_zero,
    jet_mul_zero, jet_zero_mul, toSpace]
  simp only [ScalarTwoJet.constant]
  refine ⟨?_, ?_, ?_⟩
  · funext i j
    fin_cases i <;> fin_cases j <;> rfl
  · funext k i j
    fin_cases i <;> fin_cases j <;> rfl
  · funext k l i j
    fin_cases i <;> fin_cases j <;> rfl

private theorem combined_add (s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) :
    toSpace (combinedJet s r y B aS aV S Sx Sy Sxx Sxy Sxxx Sxxy) =
    toSpace (scalarJet s r y (aS*B) S Sx Sy Sxx Sxy) +
    toSpace (coexactJet s r y (aV*B) S Sx Sy Sxx Sxy Sxxx Sxxy) := rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- The retained correction is exactly the mixed amplitude slot of the original ingoing jet. -/
theorem correction_amplitude_cut (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) :
    toSpace (D4BMQuadraticIngoingCorrection.correctionJet s r y B 1 1 S Sx Sy Sxx Sxy Sxxx Sxxy) -
    toSpace (D4BMQuadraticIngoingCorrection.correctionJet s r y B 1 0 S Sx Sy Sxx Sxy Sxxx Sxxy) -
    toSpace (D4BMQuadraticIngoingCorrection.correctionJet s r y B 0 1 S Sx Sy Sxx Sxy Sxxx Sxxy) =
    toSpace (correctionJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy) := by
  simp only [D4BMQuadraticIngoingCorrection.correctionJet, one_pow, one_mul, mul_one,
    zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_mul, zero_div,
    jet_zero_mul, jet_mul_zero, correctionJet]
  apply Prod.ext
  · funext i j
    fin_cases i <;> fin_cases j <;> simp [toSpace, ScalarTwoJet.constant]
  apply Prod.ext
  · funext k i j
    fin_cases i <;> fin_cases j <;> simp [toSpace, ScalarTwoJet.constant]
  · funext k l i j
    fin_cases i <;> fin_cases j <;> simp [toSpace, ScalarTwoJet.constant]

/-- Literal mixed amplitude coefficient of the original corrected nonlinear Einstein path. -/
def amplitudeCut (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ) (i j : Fin 4) : ℂ :=
  let E := fun a b => iteratedDeriv 2
    (D4BMQuadraticIngoingCorrection.correctedSource s r y B a b S Sx Sy Sxx Sxy Sxxx Sxxy i j) 0 / 2
  E 1 1-E 1 0-E 0 1

/-- All sixteen components of the literal amplitude cut equal the derived full tensor. -/
theorem amplitudeCut_eq (s r y B S Sx Sy Sxx Sxy Sxxx Sxxy : ℂ)
    (hr : r ≠ 0) (hy : y ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) (i j : Fin 4) :
    amplitudeCut s r y B S Sx Sy Sxx Sxy Sxxx Sxxy i j =
      tensor s r y B S Sx Sy Sxx Sxy i j := by
  have hJ : (D4BMBackground.jet r y).metric.det ≠ 0 := by
    change (D4BMBackground.metric r y).det ≠ 0
    rw [D4BMBackground.metric_det r y hf]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero 4 hr) (pow_ne_zero 4 (inv_ne_zero hy)))
  have hC := correction_amplitude_cut s r y B S Sx Sy Sxx Sxy Sxxx Sxxy
  have hCm := congrArg (fun q : ComplexMetricTwoJetSpace 4 => q.1 i j) hC
  have hCF := congrArg (fun q => fderiv ℂ (einsteinComponent i j) (toSpace (D4BMBackground.jet r y)) q) hC
  simp only [map_sub] at hCF
  have hE := einstein_component s r y B S Sx Sy Sxx Sxy Sxxx Sxxy hr hy hf i j
  rw [CoordinateMetricTwoJet.MixedQuadratic.einstein_eq_secondVariation _ _ _ hJ] at hE
  simp only [CoordinateMetricTwoJet.Linearization.cosmological,
    CoordinateMetricTwoJet.Linearization.einstein_eq_fderiv _ _ hJ] at hE
  unfold amplitudeCut D4BMQuadraticIngoingCorrection.correctedSource
  simp only [CubicSource.quadratic_coefficient _ _ _ _ hJ,
    CoordinateMetricTwoJet.Linearization.cosmological,
    CoordinateMetricTwoJet.Linearization.einstein_eq_fderiv _ _ hJ,
    combined_add, one_mul, zero_mul, scalar_zero, coexact_zero, add_zero, zero_add,
    map_add, add_apply,
    secondVariation_symm (toSpace (D4BMBackground.jet r y)) hJ i j
      (toSpace (scalarJet s r y B S Sx Sy Sxx Sxy))
      (toSpace (coexactJet s r y B S Sx Sy Sxx Sxy Sxxx Sxxy))]
  change _ = _ at hCm
  dsimp [toSpace] at hCm
  linear_combination hE + hCF - 3 * hCm

end
end RHTower.D4BMQuadraticMixedSource
