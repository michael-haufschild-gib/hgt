import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMiddleCriticalRate
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanStationaryPolynomial

/-!
# A fixed integration interval for the physical Gibbs barrier

The affine path runs from the large phase to the actual intermediate
stationary radius. Its rescaled coordinate remains in the phase interval
and tends to 1-u. All interval and positivity properties follow from the
constructed radii; no radius bounds are assumed.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAMiddleGapCoordinate (τ φ : ℝ) : ℝ :=
  (egbFixedChargeAMiddleMeanRatio τ φ - 1) / egbCoexistenceASymmetricRatio τ

def egbFixedChargeABarrierPathCoordinate (τ φ u : ℝ) : ℝ :=
  1 + (egbFixedChargeAMiddleGapCoordinate τ φ - 1) * u

def egbFixedChargeABarrierPathRadius (w φ τ u : ℝ) : ℝ :=
  egbFixedChargeALargeRadius w φ τ + (egbFixedChargeAMiddleRadius w φ τ - egbFixedChargeALargeRadius w φ τ) * u

theorem egbFixedChargeAMiddleGapCoordinate_bounds (τ φ : ℝ) :
    -1 < egbFixedChargeAMiddleGapCoordinate τ φ ∧ egbFixedChargeAMiddleGapCoordinate τ φ < 1 := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hv := egbFixedChargeAMiddleMeanRatio_bounds τ φ
  unfold egbFixedChargeAMiddleGapCoordinate
  constructor
  · apply (lt_div_iff₀ hd).2
    linarith [hv.1]
  · apply (div_lt_iff₀ hd).2
    linarith [hv.2]

theorem egbFixedChargeAMiddleGapCoordinate_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMiddleGapCoordinate τ φ) atBot (𝓝 (0 : ℝ)) :=
  egbFixedChargeAMiddleMeanRatio_linear_limit φ

theorem egbFixedChargeABarrierPathCoordinate_mapsTo (τ φ : ℝ) :
    MapsTo (egbFixedChargeABarrierPathCoordinate τ φ) (Icc 0 1) (Icc (-1) 1) := by
  intro u hu
  have hc := egbFixedChargeAMiddleGapCoordinate_bounds τ φ
  have hlo := mul_nonneg (show 0 ≤ 1 - egbFixedChargeAMiddleGapCoordinate τ φ by linarith [hc.2]) (show 0 ≤ 1 - u by linarith [hu.2])
  have hhi := mul_nonpos_of_nonpos_of_nonneg (show egbFixedChargeAMiddleGapCoordinate τ φ - 1 ≤ 0 by linarith [hc.2]) hu.1
  change -1 ≤ egbFixedChargeABarrierPathCoordinate τ φ u ∧ egbFixedChargeABarrierPathCoordinate τ φ u ≤ 1
  unfold egbFixedChargeABarrierPathCoordinate
  constructor <;> nlinarith [hc.1]

theorem egbFixedChargeABarrierPathCoordinate_critical_limit (φ u : ℝ) :
    Tendsto (fun τ => egbFixedChargeABarrierPathCoordinate τ φ u) atBot (𝓝 (1 - u)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add
    (((egbFixedChargeAMiddleGapCoordinate_critical_limit φ).sub (tendsto_const_nhds (x := (1 : ℝ)))).mul (tendsto_const_nhds (x := u)))
  change Tendsto (fun τ => 1 + (egbFixedChargeAMiddleGapCoordinate τ φ - 1) * u) _ _
  convert h using 1 <;> ring

theorem egbFixedChargeABarrierPathRadius_mean_formula (w φ τ u : ℝ) :
    egbFixedChargeABarrierPathRadius w φ τ u = egbFixedChargeAMeanRadius w φ τ *
      (1 + egbCoexistenceASymmetricRatio τ * egbFixedChargeABarrierPathCoordinate τ φ u) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeABarrierPathRadius egbFixedChargeABarrierPathCoordinate egbFixedChargeAMiddleGapCoordinate
  rw [egbFixedChargeAMiddleRadius_mean_formula, egbFixedChargeA_large_radius_mean]
  field_simp <;> ring

theorem egbFixedChargeABarrierPathRadius_start (w φ τ : ℝ) :
    egbFixedChargeABarrierPathRadius w φ τ 0 = egbFixedChargeALargeRadius w φ τ := by
  simp only [egbFixedChargeABarrierPathRadius, mul_zero, add_zero]

theorem egbFixedChargeABarrierPathRadius_end (w φ τ : ℝ) :
    egbFixedChargeABarrierPathRadius w φ τ 1 = egbFixedChargeAMiddleRadius w φ τ := by
  unfold egbFixedChargeABarrierPathRadius
  ring

theorem egbFixedChargeABarrierPathRadius_mapsTo (w φ τ : ℝ) :
    MapsTo (egbFixedChargeABarrierPathRadius w φ τ) (Icc 0 1)
      (Icc (egbFixedChargeAMiddleRadius w φ τ) (egbFixedChargeALargeRadius w φ τ)) := by
  intro u hu
  have hr := (egbFixedChargeAMiddleRadius_bounds w φ τ).2
  have hlo := mul_nonneg (show 0 ≤ egbFixedChargeALargeRadius w φ τ - egbFixedChargeAMiddleRadius w φ τ by linarith)
    (show 0 ≤ 1 - u by linarith [hu.2])
  have hhi := mul_nonpos_of_nonpos_of_nonneg (show egbFixedChargeAMiddleRadius w φ τ - egbFixedChargeALargeRadius w φ τ ≤ 0 by linarith) hu.1
  change egbFixedChargeAMiddleRadius w φ τ ≤ _ ∧ _
  unfold egbFixedChargeABarrierPathRadius
  constructor <;> nlinarith

theorem egbFixedChargeABarrierPathScale_mapsTo (τ φ : ℝ) :
    MapsTo (fun u => 1 + egbCoexistenceASymmetricRatio τ * egbFixedChargeABarrierPathCoordinate τ φ u) (Icc 0 1)
      (Icc (1 - egbCoexistenceASymmetricRatio τ) (1 + egbCoexistenceASymmetricRatio τ)) := by
  intro u hu
  have hc := egbFixedChargeABarrierPathCoordinate_mapsTo τ φ hu
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hlo := mul_le_mul_of_nonneg_left hc.1 hd.le
  have hhi := mul_le_mul_of_nonneg_left hc.2 hd.le
  constructor <;> linarith

theorem egbFixedChargeAMeanDenominator_gt_four (τ φ : ℝ) : 4 < egbFixedChargeAMeanDenominator τ φ := by
  have hd := egbCoexistenceASymmetricRatio_bounds τ
  have hx : egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) < 1 := by nlinarith [hd.1, hd.2]
  have hprod : 0 ≤ 4 * egbFixedChargeAMeanCoupling τ φ * egbCoexistenceALogKernel τ :=
    mul_nonneg (mul_nonneg (by norm_num) (egbFixedChargeAMeanCoupling_nonneg τ φ)) (egbCoexistenceALogKernel_pos τ).le
  unfold egbFixedChargeAMeanDenominator
  linarith

theorem egbFixedChargeAMiddleMeanResidual_linear_limit (φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ + egbFixedChargeAMiddleMeanConstant τ φ) /
      egbCoexistenceASymmetricRatio τ) atBot (𝓝 (0 : ℝ)) := by
  have h := (egbFixedChargeAMiddleMeanResidual_critical_limit φ).mul egbCoexistenceASymmetricRatio_critical_limit
  simp only [mul_zero] at h
  convert h using 1
  funext τ
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  field_simp

theorem egbFixedChargeAMiddleMeanLinearCombination_limit (φ : ℝ) :
    Tendsto (fun τ => 2 * egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ)
      atBot (𝓝 (4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ))) := by
  have h := ((tendsto_const_nhds (x := (2 : ℝ))).mul (egbFixedChargeAMeanPressureNumerator_critical_limit φ)).add
    (egbFixedChargeAMiddleMeanLinear_critical_limit φ)
  convert h using 1 <;> ring

end GaloisForLFunctions.HTGeometry
