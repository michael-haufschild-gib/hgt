import GaloisForLFunctions.HTGeometry.CoordinateMetricTestModeVariation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedActionModeDerivatives
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMActionCubicCoefficient

set_option autoImplicit false
set_option maxSynthPendingDepth 128

namespace RHTower.D4BMMixedActionSource
open GaloisForLFunctions.HTGeometry
open D4BMBackground D4BMMetricReconstruction D4BMActualMetricSource
open D4BMMixedCorrectedSource D4BMMixedActionData ComplexCoordinateMetricTwoJet MetricPathDensity
noncomputable section
local notation "Mat" => Matrix (Fin 4) (Fin 4) ℂ

/-- The actual mixed amplitude derivative of the original volume-weighted source contraction. -/
def mixedPairedCoefficient (p : ExteriorPoint) (H K L : Fin 4 → MetricField) (M : Mat) : ℂ :=
  deriv (fun z => iteratedDeriv 3 (D4BMActionSource.pairedSource p
    (fieldPath H z) (fieldPath K z) (fieldPath L z) M) 0 / 6) 0

private theorem mixed_derivative (p : ExteriorPoint) (H K L : Fin 4 → MetricField) (M : Mat)
    (hH : ∀ a i j, ContDiffAt ℝ 2 (fun x => H a x i j) p.val)
    (hK : ∀ a i j, ContDiffAt ℝ 2 (fun x => K a x i j) p.val)
    (hL : ∀ a i j, ContDiffAt ℝ 2 (fun x => L a x i j) p.val)
    (hfirst : ∀ a i j, deriv (source p (H a) i j) 0 = 0) :
    mixedPairedCoefficient p H K L M = ∑ i, ∑ j,
      (((actualJet p).metric⁻¹ * M * ((actualJet p).metric⁻¹).transpose) i j *
          mixedCoefficient p H K L i j +
        testWeightSlope (actualJet p).metric (H 1 p.val) M i j *
          (iteratedDeriv 2 (D4BMCorrectedMetricSource.source p (H 0) (K 0) (L 0) i j) 0 / 2) +
        testWeightSlope (actualJet p).metric (H 0 p.val) M i j *
          (D4BMLinearizedEinsteinSource.residual p (ofMetricField (K 1) p.val) i j +
            secondVariation (backgroundSpace p) i j (fieldSpace p (H 0)) (fieldSpace p (H 1)))) := by
  let W : Fin 4 → Fin 4 → ℂ := fun i j =>
    ((actualJet p).metric⁻¹ * M * ((actualJet p).metric⁻¹).transpose) i j
  let E (n : ℕ) (i j : Fin 4) (z : ℂ) :=
    iteratedDeriv n (D4BMCorrectedMetricSource.source p
      (fieldPath H z) (fieldPath K z) (fieldPath L z) i j) 0 / (n.factorial : ℂ)
  have hE2 (i j : Fin 4) := quadratic_mode_hasDerivAt p H K L hH hK hL i j
  have hE3 (i j : Fin 4) := (cubic_mode_differentiableAt p H K L hH hK hL i j).hasDerivAt
  have hw (i j : Fin 4) : HasDerivAt
      (fun z => testWeightSlope (actualJet p).metric (fieldPath H z p.val) M i j)
      (testWeightSlope (actualJet p).metric (H 1 p.val) M i j) 0 :=
    testWeightSlope_path_hasDerivAt (actualJet p).metric
      (H 0 p.val) (H 1 p.val) (H 2 p.val) (H 3 p.val) M i j
  have hd (i j : Fin 4) := ((hE3 i j).const_mul (W i j)).add ((hw i j).mul (hE2 i j))
  have ht := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hd i j))
  have he : (fun z => iteratedDeriv 3 (D4BMActionSource.pairedSource p
      (fieldPath H z) (fieldPath K z) (fieldPath L z) M) 0 / 6) = fun z =>
      ∑ i, ∑ j, (W i j * E 3 i j z +
        testWeightSlope (actualJet p).metric (fieldPath H z p.val) M i j * E 2 i j z) := by
    funext z
    convert! D4BMActionSource.pairedSource_cubic p _ _ _ M (fieldPath_smooth p H hH z)
      (fieldPath_smooth p K hK z) (fieldPath_smooth p L hL z)
      (fieldPath_source_first_zero p H hH hfirst z) using 1
  unfold mixedPairedCoefficient
  rw [he]
  convert! ht.deriv using 1
  simp only [fieldPath_at_zero, mixedCoefficient, W, add_assoc]


/-- Complete weighted ++- bulk coefficient. All unused mode slots disappear by actual differentiation;
the two relevant quadratic residuals retain every tensor component and linear correction. -/
theorem mixedPairedCoefficient_eq (p : ExteriorPoint) (H K L : Fin 4 → MetricField) (M : Mat)
    (hH : ∀ a i j, ContDiffAt ℝ 2 (fun x => H a x i j) p.val)
    (hK : ∀ a i j, ContDiffAt ℝ 2 (fun x => K a x i j) p.val)
    (hL : ∀ a i j, ContDiffAt ℝ 2 (fun x => L a x i j) p.val)
    (hfirst : ∀ a i j, deriv (source p (H a) i j) 0 = 0) :
    mixedPairedCoefficient p H K L M = ∑ i, ∑ j,
      (((actualJet p).metric⁻¹ * M * ((actualJet p).metric⁻¹).transpose) i j *
          (D4BMLinearizedEinsteinSource.residual p (ofMetricField (L 1) p.val) i j +
            secondVariation (backgroundSpace p) i j (fieldSpace p (H 0)) (fieldSpace p (K 1)) +
            secondVariation (backgroundSpace p) i j (fieldSpace p (H 1)) (fieldSpace p (K 0)) +
            thirdVariation (backgroundSpace p) i j (fieldSpace p (H 0)) (fieldSpace p (H 0))
              (fieldSpace p (H 1)) / 2) +
        testWeightSlope (actualJet p).metric (H 1 p.val) M i j *
          (D4BMLinearizedEinsteinSource.residual p (ofMetricField (K 0) p.val) i j +
            secondVariation (backgroundSpace p) i j (fieldSpace p (H 0)) (fieldSpace p (H 0)) / 2) +
        testWeightSlope (actualJet p).metric (H 0 p.val) M i j *
          (D4BMLinearizedEinsteinSource.residual p (ofMetricField (K 1) p.val) i j +
            secondVariation (backgroundSpace p) i j (fieldSpace p (H 0)) (fieldSpace p (H 1)))) := by
  rw [mixed_derivative p H K L M hH hK hL hfirst]
  simp only [cubic_mixed_coefficient p H K L hH hK hL,
    D4BMCorrectedMetricSource.source_quadratic p (H 0) (K 0) (L 0) (hH 0) (hK 0) (hL 0)]

/-- Only the complete ++ and +- quadratic grades are needed to remove the varying-weight terms
from the ++- coefficient. The -- correction and other cubic slots are unrestricted. -/
theorem mixedPairedCoefficient_of_quadratic_zero (p : ExteriorPoint) (H K L : Fin 4 → MetricField) (M : Mat)
    (hH : ∀ a i j, ContDiffAt ℝ 2 (fun x => H a x i j) p.val)
    (hK : ∀ a i j, ContDiffAt ℝ 2 (fun x => K a x i j) p.val)
    (hL : ∀ a i j, ContDiffAt ℝ 2 (fun x => L a x i j) p.val)
    (hfirst : ∀ a i j, deriv (source p (H a) i j) 0 = 0)
    (hpp : ∀ i j, D4BMLinearizedEinsteinSource.residual p (ofMetricField (K 0) p.val) i j +
      secondVariation (backgroundSpace p) i j (fieldSpace p (H 0)) (fieldSpace p (H 0)) / 2 = 0)
    (hpm : ∀ i j, D4BMLinearizedEinsteinSource.residual p (ofMetricField (K 1) p.val) i j +
      secondVariation (backgroundSpace p) i j (fieldSpace p (H 0)) (fieldSpace p (H 1)) = 0) :
    mixedPairedCoefficient p H K L M = ∑ i, ∑ j,
      ((actualJet p).metric⁻¹ * M * ((actualJet p).metric⁻¹).transpose) i j * mixedCoefficient p H K L i j := by
  rw [mixed_derivative p H K L M hH hK hL hfirst]
  simp only [D4BMCorrectedMetricSource.source_quadratic p (H 0) (K 0) (L 0) (hH 0) (hK 0) (hL 0),
    hpp, hpm, mul_zero, add_zero]

end
end RHTower.D4BMMixedActionSource
