import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMiddleMeanQuadratic

/-!
# Critical coefficients and a positive secant denominator for the middle root
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAMeanPressureNumerator_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanPressureNumerator τ φ) atBot (𝓝 (3 - 2 * egbFixedChargeACriticalCouplingWeight φ)) := by
  have hd : Tendsto (fun τ => egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) atBot (𝓝 (0 : ℝ)) := by
    simpa using egbCoexistenceASymmetricRatio_critical_limit.pow 2
  have h := ((tendsto_const_nhds (x := (3 : ℝ))).mul ((tendsto_const_nhds (x := (1 : ℝ))).add hd)).add
    (((tendsto_const_nhds (x := (2 : ℝ))).mul (egbFixedChargeAMeanCoupling_critical_limit φ)).mul
      ((tendsto_const_nhds (x := (2 : ℝ))).sub egbCoexistenceALogKernel_tendsto_critical))
  change Tendsto (fun τ => 3 * (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) + 2 * egbFixedChargeAMeanCoupling τ φ * (2 - egbCoexistenceALogKernel τ)) _ _
  convert h using 1 <;> ring

theorem egbFixedChargeAMiddleMeanLinear_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMiddleMeanLinear τ φ) atBot (𝓝 (-2 - 4 * egbFixedChargeACriticalCouplingWeight φ)) := by
  have hd : Tendsto (fun τ => egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) atBot (𝓝 (0 : ℝ)) := by
    simpa using egbCoexistenceASymmetricRatio_critical_limit.pow 2
  have h := ((tendsto_const_nhds (x := (2 : ℝ))).mul (egbFixedChargeAMeanPressureNumerator_critical_limit φ)).sub
    ((tendsto_const_nhds (x := (8 : ℝ))).mul ((tendsto_const_nhds (x := (1 : ℝ))).add hd))
  change Tendsto (fun τ => 2 * egbFixedChargeAMeanPressureNumerator τ φ - 8 * (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))) _ _
  convert h using 1 <;> ring

theorem egbFixedChargeAMiddleMeanConstant_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMiddleMeanConstant τ φ) atBot (𝓝 (-1 + 6 * egbFixedChargeACriticalCouplingWeight φ)) := by
  have hd : Tendsto (fun τ => egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) atBot (𝓝 (0 : ℝ)) := by
    simpa using egbCoexistenceASymmetricRatio_critical_limit.pow 2
  have hd4 : Tendsto (fun τ => egbCoexistenceASymmetricRatio τ ^ (4 : ℕ)) atBot (𝓝 (0 : ℝ)) := by
    simpa using egbCoexistenceASymmetricRatio_critical_limit.pow 4
  have hi : Tendsto (fun τ => 6 - egbCoexistenceALogKernel τ + (egbCoexistenceALogKernel τ + 2) * egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))
      atBot (𝓝 (3 : ℝ)) := by
    convert ((tendsto_const_nhds (x := (6 : ℝ))).sub egbCoexistenceALogKernel_tendsto_critical).add
      ((egbCoexistenceALogKernel_tendsto_critical.add (tendsto_const_nhds (x := (2 : ℝ)))).mul hd) using 1 <;> norm_num
  simp only [egbFixedChargeAMiddleMeanConstant_formula]
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hd4).neg.add
    (((tendsto_const_nhds (x := (2 : ℝ))).mul (egbFixedChargeAMeanCoupling_critical_limit φ)).mul hi)
  convert h using 1 <;> ring

theorem egbFixedChargeAMiddleMeanResidual_critical_limit (φ : ℝ) :
    Tendsto (fun τ => (egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ + egbFixedChargeAMiddleMeanConstant τ φ) /
      egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) atBot (𝓝 (1 - 14 * egbFixedChargeACriticalCouplingWeight φ / 5)) := by
  have hd : Tendsto (fun τ => egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) atBot (𝓝 (0 : ℝ)) := by
    simpa using egbCoexistenceASymmetricRatio_critical_limit.pow 2
  have hk : Tendsto (fun τ => -8 * ((egbCoexistenceALogKernel τ - 3) / egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) + 2 * (egbCoexistenceALogKernel τ + 2))
      atBot (𝓝 (-14 / 5 : ℝ)) := by
    convert ((tendsto_const_nhds (x := (-8 : ℝ))).mul egbCoexistenceALogKernel_asymmetry_quadratic_limit).add
      ((tendsto_const_nhds (x := (2 : ℝ))).mul (egbCoexistenceALogKernel_tendsto_critical.add (tendsto_const_nhds (x := (2 : ℝ))))) using 1 <;> norm_num
  simp only [egbFixedChargeAMiddleMeanResidual_formula]
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).add hd).add ((egbFixedChargeAMeanCoupling_critical_limit φ).mul hk)
  convert h using 1 <;> ring

theorem egbFixedChargeAMiddleMeanSecant_pos (τ φ : ℝ) :
    0 < egbFixedChargeAMeanPressureNumerator τ φ * (egbFixedChargeAMiddleMeanRatio τ φ + 1) + egbFixedChargeAMiddleMeanLinear τ φ := by
  have hN := egbFixedChargeAMeanPressureNumerator_pos τ φ
  have hv := egbFixedChargeAMiddleMeanRatio_pos τ φ
  have hC := egbFixedChargeAMiddleMeanConstant_neg τ φ
  have he : (egbFixedChargeAMeanPressureNumerator τ φ * (egbFixedChargeAMiddleMeanRatio τ φ + 1) + egbFixedChargeAMiddleMeanLinear τ φ) *
      egbFixedChargeAMiddleMeanRatio τ φ =
      egbFixedChargeAMeanPressureNumerator τ φ * egbFixedChargeAMiddleMeanRatio τ φ - egbFixedChargeAMiddleMeanConstant τ φ := by
    linear_combination egbFixedChargeAMiddleMeanRatio_quadratic τ φ
  have hp : 0 < egbFixedChargeAMeanPressureNumerator τ φ * egbFixedChargeAMiddleMeanRatio τ φ - egbFixedChargeAMiddleMeanConstant τ φ :=
    sub_pos.mpr (lt_trans hC (mul_pos hN hv))
  by_contra hn
  have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hv.le
  rw [he] at hm
  linarith

theorem egbFixedChargeAMiddleMeanSecant_critical_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAMeanPressureNumerator τ φ * (egbFixedChargeAMiddleMeanRatio τ φ + 1) + egbFixedChargeAMiddleMeanLinear τ φ)
      atBot (𝓝 (4 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ))) := by
  have h := ((egbFixedChargeAMeanPressureNumerator_critical_limit φ).mul
    ((egbFixedChargeAMiddleMeanRatio_critical_limit φ).add (tendsto_const_nhds (x := (1 : ℝ))))).add
      (egbFixedChargeAMiddleMeanLinear_critical_limit φ)
  convert h using 1 <;> ring

theorem egbFixedChargeAMiddleMeanRatio_difference_cross (τ φ : ℝ) :
    (egbFixedChargeAMiddleMeanRatio τ φ - 1) *
      (egbFixedChargeAMeanPressureNumerator τ φ * (egbFixedChargeAMiddleMeanRatio τ φ + 1) + egbFixedChargeAMiddleMeanLinear τ φ) =
    -(egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ + egbFixedChargeAMiddleMeanConstant τ φ) := by
  linear_combination egbFixedChargeAMiddleMeanRatio_quadratic τ φ

end GaloisForLFunctions.HTGeometry
