import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAKernelLimits
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeATransfer

/-!
# Cold scaling of the fixed-charge model-A coexistence weights

Normalize the effective-charge weight by the squared radius ratio. Its
limit is one, while the coupling times the logarithmic kernel vanishes.
The apparent divergent kernel factors in pressure and the discriminant
therefore cancel in exact combinations before taking any limit.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbFixedChargeANormalizedWeight (τ φ : ℝ) : ℝ := egbFixedChargeAWeight τ φ / thermalRatio τ ^ 2

theorem egbFixedChargeANormalizedWeight_pos (τ φ : ℝ) : 0 < egbFixedChargeANormalizedWeight τ φ := by
  have hs := egbFixedChargeAWeight_pos τ φ
  have hz := thermalRatio_pos τ
  unfold egbFixedChargeANormalizedWeight
  positivity

theorem egbFixedChargeANormalizedWeight_formula (τ φ : ℝ) :
    egbFixedChargeANormalizedWeight τ φ =
      2 * (thermalRatio τ ^ 2 + 1) / (egbFixedChargeAQuadraticB τ φ + sqrt (egbFixedChargeADiscriminant τ φ)) := by
  have hz := thermalRatio_pos τ
  have hB := egbFixedChargeAQuadraticB_pos τ φ
  unfold egbFixedChargeANormalizedWeight egbFixedChargeAWeight egbCoexistenceAQuadraticC
  field_simp <;> ring

theorem egbFixedChargeAWeight_normalized (τ φ : ℝ) :
    egbFixedChargeAWeight τ φ = egbFixedChargeANormalizedWeight τ φ * thermalRatio τ ^ 2 := by
  have hz := thermalRatio_pos τ
  unfold egbFixedChargeANormalizedWeight
  field_simp

theorem egbFixedChargeAQuadraticB_cold_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAQuadraticB τ φ) atTop (𝓝 1) := by
  have h : Tendsto (fun τ => egbFixedChargeAQuadraticB τ φ) atTop
      (𝓝 (1 - egbFixedChargeAFraction φ * 0)) :=
    egbFixedChargeABase_cold_limit.sub (tendsto_const_nhds.mul egbFixedChargeALinearCorrection_cold_limit)
  simpa only [mul_zero, sub_zero] using h

theorem egbFixedChargeADiscriminant_product (τ φ : ℝ) :
    egbFixedChargeADiscriminant τ φ = egbFixedChargeAQuadraticB τ φ ^ 2 +
      4 * egbFixedChargeAFraction φ * (egbCoexistenceAQuadraticA τ * egbCoexistenceAQuadraticC τ) := by
  unfold egbFixedChargeADiscriminant
  ring

theorem egbFixedChargeADiscriminant_cold_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeADiscriminant τ φ) atTop (𝓝 1) := by
  simp only [egbFixedChargeADiscriminant_product]
  have h : Tendsto (fun τ => egbFixedChargeAQuadraticB τ φ ^ 2 +
      4 * egbFixedChargeAFraction φ * (egbCoexistenceAQuadraticA τ * egbCoexistenceAQuadraticC τ)) atTop
      (𝓝 ((1 : ℝ) ^ 2 + 4 * egbFixedChargeAFraction φ * 0)) :=
    ((egbFixedChargeAQuadraticB_cold_limit φ).pow 2).add
      (tendsto_const_nhds.mul egbCoexistenceA_quadratic_product_cold_limit)
  norm_num at h
  exact h

theorem egbFixedChargeANormalizedWeight_cold_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeANormalizedWeight τ φ) atTop (𝓝 1) := by
  simp only [egbFixedChargeANormalizedWeight_formula]
  have hz := thermalRatio_tendsto_atTop_zero
  have h : Tendsto (fun τ => 2 * (thermalRatio τ ^ 2 + 1) /
      (egbFixedChargeAQuadraticB τ φ + sqrt (egbFixedChargeADiscriminant τ φ))) atTop
      (𝓝 ((2 * ((0 : ℝ) ^ 2 + 1)) / (1 + sqrt 1))) :=
    (tendsto_const_nhds.mul ((hz.pow 2).add tendsto_const_nhds)).div
      ((egbFixedChargeAQuadraticB_cold_limit φ).add (egbFixedChargeADiscriminant_cold_limit φ).sqrt) (by positivity)
  norm_num at h
  exact h

theorem egbFixedChargeAWeight_cold_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAWeight τ φ) atTop (𝓝 0) := by
  simp only [egbFixedChargeAWeight_normalized]
  have h := (egbFixedChargeANormalizedWeight_cold_limit φ).mul (thermalRatio_tendsto_atTop_zero.pow 2)
  norm_num at h
  exact h

theorem egbFixedChargeACouplingWeight_cold_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeACouplingWeight τ φ) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := egbFixedChargeAFraction φ)).mul (egbFixedChargeAWeight_cold_limit φ)
  simpa only [egbFixedChargeACouplingWeight, mul_zero] using h

/-- The potentially singular logarithmic correction is controlled by the normalized root. -/
theorem egbFixedChargeA_kernel_product_normalized (τ φ : ℝ) :
    egbFixedChargeACouplingWeight τ φ * egbCoexistenceALogKernel τ =
      egbFixedChargeAFraction φ * egbFixedChargeANormalizedWeight τ φ *
        (egbCoexistenceALogKernel τ * thermalRatio τ ^ 2) := by
  unfold egbFixedChargeACouplingWeight
  rw [egbFixedChargeAWeight_normalized]
  ring

theorem egbFixedChargeA_kernel_product_cold_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeACouplingWeight τ φ * egbCoexistenceALogKernel τ) atTop (𝓝 0) := by
  simp only [egbFixedChargeA_kernel_product_normalized]
  have h := ((tendsto_const_nhds (x := egbFixedChargeAFraction φ)).mul (egbFixedChargeANormalizedWeight_cold_limit φ)).mul
    egbCoexistenceALogKernel_weighted_cold_limit
  simpa only [mul_zero] using h

theorem egbFixedChargeADenominator_cold_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeADenominator τ φ) atTop (𝓝 1) := by
  have he : (fun τ => egbFixedChargeADenominator τ φ) =
      (fun τ => egbCoexistenceShape τ + 4 * (egbFixedChargeACouplingWeight τ φ * egbCoexistenceALogKernel τ)) := by
    funext τ
    unfold egbFixedChargeADenominator
    ring
  rw [he]
  have h : Tendsto (fun τ => egbCoexistenceShape τ + 4 * (egbFixedChargeACouplingWeight τ φ * egbCoexistenceALogKernel τ))
      atTop (𝓝 ((1 : ℝ) + 4 * 0)) := egbCoexistenceShape_tendsto_cold.add
        (tendsto_const_nhds.mul (egbFixedChargeA_kernel_product_cold_limit φ))
  norm_num at h
  exact h

theorem egbFixedChargeATemperatureWeight_cold_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeATemperatureWeight τ φ) atTop (𝓝 4) := by
  have h : Tendsto (fun τ => egbFixedChargeATemperatureWeight τ φ) atTop (𝓝 (((4 : ℝ) * (0 + 1)) / 1)) :=
    (tendsto_const_nhds.mul (thermalRatio_tendsto_atTop_zero.add tendsto_const_nhds)).div
      (egbFixedChargeADenominator_cold_limit φ) one_ne_zero
  norm_num at h
  exact h

theorem egbFixedChargeAPressureWeight_cold_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAPressureWeight τ φ) atTop (𝓝 3) := by
  have he : (fun τ => egbFixedChargeAPressureWeight τ φ) = (fun τ =>
      (3 * (thermalRatio τ ^ 2 + 1) + 8 * egbFixedChargeACouplingWeight τ φ -
        4 * (egbFixedChargeACouplingWeight τ φ * egbCoexistenceALogKernel τ)) /
          (egbFixedChargeADenominator τ φ * (thermalRatio τ ^ 2 + 1))) := by
    funext τ
    unfold egbFixedChargeAPressureWeight
    ring
  rw [he]
  have hz := thermalRatio_tendsto_atTop_zero
  have h : Tendsto (fun τ => (3 * (thermalRatio τ ^ 2 + 1) + 8 * egbFixedChargeACouplingWeight τ φ -
      4 * (egbFixedChargeACouplingWeight τ φ * egbCoexistenceALogKernel τ)) /
        (egbFixedChargeADenominator τ φ * (thermalRatio τ ^ 2 + 1))) atTop
      (𝓝 ((3 * ((0 : ℝ) ^ 2 + 1) + 8 * 0 - 4 * 0) / (1 * (0 ^ 2 + 1)))) :=
    (((tendsto_const_nhds.mul ((hz.pow 2).add tendsto_const_nhds)).add
      (tendsto_const_nhds.mul (egbFixedChargeACouplingWeight_cold_limit φ))).sub
        (tendsto_const_nhds.mul (egbFixedChargeA_kernel_product_cold_limit φ))).div
          ((egbFixedChargeADenominator_cold_limit φ).mul ((hz.pow 2).add tendsto_const_nhds)) (by norm_num)
  norm_num at h
  exact h

end GaloisForLFunctions.HTGeometry
