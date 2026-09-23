import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAColdLimits
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAJumps

/-!
# Cold entropy and volume scaling on the fixed-charge model-A curve

The exact logarithmic kernel identity controls coupling times log of the
radius ratio. This removes the apparent logarithmic singularity before
taking limits. The actual entropy jump has area scaling, and the actual
volume jump has the corresponding cubic-radius scaling.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbFixedChargeAEntropyWeight (τ φ : ℝ) : ℝ :=
  1 - thermalRatio τ ^ (2 : ℕ) - 4 * egbFixedChargeACouplingWeight τ φ * log (thermalRatio τ)

theorem egbFixedChargeA_log_product_formula (τ φ : ℝ) :
    egbFixedChargeACouplingWeight τ φ * log (thermalRatio τ) =
      ((thermalRatio τ - 1) ^ (3 : ℕ) * (egbFixedChargeACouplingWeight τ φ * egbCoexistenceALogKernel τ) +
        4 * egbFixedChargeACouplingWeight τ φ * (thermalRatio τ ^ (2 : ℕ) + thermalRatio τ + 1) * (thermalRatio τ - 1)) /
          (3 * (thermalRatio τ + 1) * (thermalRatio τ ^ (2 : ℕ) + 1)) := by
  have hz := thermalRatio_pos τ
  apply (eq_div_iff (by positivity)).2
  linear_combination -(egbFixedChargeACouplingWeight τ φ) * egbCoexistenceALogKernel_cubic_identity τ

theorem egbFixedChargeA_log_product_cold_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeACouplingWeight τ φ * log (thermalRatio τ)) atTop (𝓝 0) := by
  simp only [egbFixedChargeA_log_product_formula]
  have hz := thermalRatio_tendsto_atTop_zero
  have hb := egbFixedChargeACouplingWeight_cold_limit φ
  have h : Tendsto (fun τ =>
      ((thermalRatio τ - 1) ^ (3 : ℕ) * (egbFixedChargeACouplingWeight τ φ * egbCoexistenceALogKernel τ) +
        4 * egbFixedChargeACouplingWeight τ φ * (thermalRatio τ ^ (2 : ℕ) + thermalRatio τ + 1) * (thermalRatio τ - 1)) /
          (3 * (thermalRatio τ + 1) * (thermalRatio τ ^ (2 : ℕ) + 1))) atTop
      (𝓝 ((((0 : ℝ) - 1) ^ (3 : ℕ) * 0 + 4 * 0 * (0 ^ (2 : ℕ) + 0 + 1) * (0 - 1)) /
        (3 * (0 + 1) * (0 ^ (2 : ℕ) + 1)))) :=
    ((((hz.sub tendsto_const_nhds).pow 3).mul (egbFixedChargeA_kernel_product_cold_limit φ)).add
      (((tendsto_const_nhds.mul hb).mul (((hz.pow 2).add hz).add tendsto_const_nhds)).mul
        (hz.sub tendsto_const_nhds))).div
          ((tendsto_const_nhds.mul (hz.add tendsto_const_nhds)).mul ((hz.pow 2).add tendsto_const_nhds)) (by norm_num)
  norm_num at h
  exact h

theorem egbFixedChargeAEntropyJump_weight (w φ τ : ℝ) :
    egbFixedChargeAEntropyJump w φ τ = Real.pi * egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ) * egbFixedChargeAEntropyWeight τ φ :=
  egbFixedChargeAEntropyJump_formula w φ τ

theorem egbFixedChargeAEntropyWeight_pos (τ φ : ℝ) : 0 < egbFixedChargeAEntropyWeight τ φ := by
  have h := egbFixedChargeAEntropyJump_pos 0 φ τ
  rw [egbFixedChargeAEntropyJump_weight] at h
  have hA : 0 < Real.pi * egbFixedChargeALargeRadius 0 φ τ ^ (2 : ℕ) := by
    have hR := egbFixedChargeALargeRadius_pos 0 φ τ
    positivity
  by_contra hn
  have hc := mul_nonpos_of_nonneg_of_nonpos hA.le (le_of_not_gt hn)
  linarith

theorem egbFixedChargeAEntropyWeight_cold_limit (φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAEntropyWeight τ φ) atTop (𝓝 1) := by
  have he : (fun τ => egbFixedChargeAEntropyWeight τ φ) =
      (fun τ => 1 - thermalRatio τ ^ (2 : ℕ) - 4 * (egbFixedChargeACouplingWeight τ φ * log (thermalRatio τ))) := by
    funext τ
    unfold egbFixedChargeAEntropyWeight
    ring
  rw [he]
  have h : Tendsto (fun τ => 1 - thermalRatio τ ^ (2 : ℕ) - 4 * (egbFixedChargeACouplingWeight τ φ * log (thermalRatio τ)))
      atTop (𝓝 (1 - (0 : ℝ) ^ (2 : ℕ) - 4 * 0)) :=
    (tendsto_const_nhds.sub (thermalRatio_tendsto_atTop_zero.pow 2)).sub
      (tendsto_const_nhds.mul (egbFixedChargeA_log_product_cold_limit φ))
  norm_num at h
  exact h

theorem egbFixedChargeAEntropyJump_area_formula (w φ τ : ℝ) :
    egbFixedChargeAEntropyJump w φ τ / (Real.pi * egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ)) = egbFixedChargeAEntropyWeight τ φ := by
  have hR := egbFixedChargeALargeRadius_pos w φ τ
  rw [egbFixedChargeAEntropyJump_weight]
  field_simp

theorem egbFixedChargeAEntropyJump_area_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAEntropyJump w φ τ / (Real.pi * egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ))) atTop (𝓝 1) := by
  simp only [egbFixedChargeAEntropyJump_area_formula]
  exact egbFixedChargeAEntropyWeight_cold_limit φ

theorem egbFixedChargeAEntropyJump_radius_square_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAEntropyJump w φ τ / egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ)) atTop (𝓝 Real.pi) := by
  have he : (fun τ => egbFixedChargeAEntropyJump w φ τ / egbFixedChargeALargeRadius w φ τ ^ (2 : ℕ)) =
      (fun τ => Real.pi * egbFixedChargeAEntropyWeight τ φ) := by
    funext τ
    have hR := egbFixedChargeALargeRadius_pos w φ τ
    rw [egbFixedChargeAEntropyJump_weight]
    field_simp
  rw [he]
  simpa only [mul_one] using (tendsto_const_nhds (x := Real.pi)).mul (egbFixedChargeAEntropyWeight_cold_limit φ)

theorem egbFixedChargeAVolumeJump_radius_cube_cold_limit (w φ : ℝ) :
    Tendsto (fun τ => egbFixedChargeAVolumeJump w φ τ / egbFixedChargeALargeRadius w φ τ ^ (3 : ℕ)) atTop (𝓝 (4 * Real.pi / 3)) := by
  have he : (fun τ => egbFixedChargeAVolumeJump w φ τ / egbFixedChargeALargeRadius w φ τ ^ (3 : ℕ)) =
      (fun τ => (4 * Real.pi / 3) * (1 - thermalRatio τ ^ (3 : ℕ))) := by
    funext τ
    have hR := egbFixedChargeALargeRadius_pos w φ τ
    rw [egbFixedChargeAVolumeJump_formula]
    field_simp <;> ring
  rw [he]
  have h : Tendsto (fun τ => (4 * Real.pi / 3) * (1 - thermalRatio τ ^ (3 : ℕ))) atTop
      (𝓝 ((4 * Real.pi / 3) * (1 - (0 : ℝ) ^ (3 : ℕ)))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub (thermalRatio_tendsto_atTop_zero.pow 3))
  norm_num at h
  exact h

end GaloisForLFunctions.HTGeometry
