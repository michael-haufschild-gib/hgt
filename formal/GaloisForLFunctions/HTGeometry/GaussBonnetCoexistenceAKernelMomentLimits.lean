import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAKernelMoments

/-!
# Exact critical coefficients from the positive moment remainder

Every weighted moment tends to its elementary polynomial coefficient.
The recurrence then gives the second-order endpoint coefficient of the
actual logarithmic kernel, in either radius asymmetry or radius ratio.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open CPV

theorem egbCoexistenceASymmetricRatio_critical_limit :
    Tendsto egbCoexistenceASymmetricRatio atBot (𝓝 0) := by
  change Tendsto (fun τ => (1 - thermalRatio τ) / (1 + thermalRatio τ)) atBot (𝓝 0)
  have hz := thermalRatio_tendsto_atBot_one
  have h : Tendsto (fun τ => (1 - thermalRatio τ) / (1 + thermalRatio τ)) atBot (𝓝 (((1 : ℝ) - 1) / (1 + 1))) :=
    (tendsto_const_nhds.sub hz).div (tendsto_const_nhds.add hz) (by norm_num)
  norm_num at h
  exact h

theorem egbCoexistenceAKernelMoment_critical_limit (n : ℕ) :
    Tendsto (fun τ => egbCoexistenceAKernelMoment τ n) atBot (𝓝 (egbCoexistenceAKernelMomentCoefficient n)) := by
  have hd : Tendsto (fun τ => 1 - egbCoexistenceASymmetricRatio τ ^ 2) atBot (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (egbCoexistenceASymmetricRatio_critical_limit.pow 2)
    norm_num at h
    exact h
  have hu : Tendsto (fun τ => egbCoexistenceAKernelMomentCoefficient n / (1 - egbCoexistenceASymmetricRatio τ ^ 2))
      atBot (𝓝 (egbCoexistenceAKernelMomentCoefficient n)) := by
    simpa only [Pi.div_def, div_one] using (tendsto_const_nhds (x := egbCoexistenceAKernelMomentCoefficient n)).div hd one_ne_zero
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun τ => (egbCoexistenceAKernelMoment_bounds τ n).1) (fun τ => (egbCoexistenceAKernelMoment_bounds τ n).2)

theorem egbCoexistenceAKernelMoment_normalized_remainder (τ : ℝ) (n : ℕ) :
    (egbCoexistenceAKernelMoment τ n - egbCoexistenceAKernelMomentCoefficient n) / egbCoexistenceASymmetricRatio τ ^ 2 =
      egbCoexistenceAKernelMoment τ (n + 1) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [egbCoexistenceAKernelMoment_recurrence]
  field_simp

theorem egbCoexistenceAKernelMoment_remainder_critical_limit (n : ℕ) :
    Tendsto (fun τ => (egbCoexistenceAKernelMoment τ n - egbCoexistenceAKernelMomentCoefficient n) /
      egbCoexistenceASymmetricRatio τ ^ 2) atBot (𝓝 (egbCoexistenceAKernelMomentCoefficient (n + 1))) := by
  simp only [egbCoexistenceAKernelMoment_normalized_remainder]
  exact egbCoexistenceAKernelMoment_critical_limit (n + 1)

theorem egbCoexistenceALogKernel_exact_quadratic_remainder (τ : ℝ) :
    egbCoexistenceALogKernel τ - 3 =
      3 * egbCoexistenceASymmetricRatio τ ^ 2 * egbCoexistenceAKernelMoment τ 1 := by
  have h := egbCoexistenceAKernelMoment_recurrence τ 0
  norm_num [egbCoexistenceAKernelMomentCoefficient] at h
  rw [egbCoexistenceAKernelMoment_zero]
  linear_combination 3 * h

theorem egbCoexistenceALogKernel_normalized_quadratic_remainder (τ : ℝ) :
    (egbCoexistenceALogKernel τ - 3) / egbCoexistenceASymmetricRatio τ ^ 2 = 3 * egbCoexistenceAKernelMoment τ 1 := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [egbCoexistenceALogKernel_exact_quadratic_remainder]
  field_simp

theorem egbCoexistenceALogKernel_asymmetry_quadratic_limit :
    Tendsto (fun τ => (egbCoexistenceALogKernel τ - 3) / egbCoexistenceASymmetricRatio τ ^ 2) atBot (𝓝 ((8 : ℝ) / 5)) := by
  simp only [egbCoexistenceALogKernel_normalized_quadratic_remainder]
  have h := (tendsto_const_nhds (x := (3 : ℝ))).mul (egbCoexistenceAKernelMoment_critical_limit 1)
  norm_num [egbCoexistenceAKernelMomentCoefficient] at h
  exact h

theorem egbCoexistenceALogKernel_ratio_quadratic_formula (τ : ℝ) :
    (egbCoexistenceALogKernel τ - 3) / (1 - thermalRatio τ) ^ 2 =
      3 * egbCoexistenceAKernelMoment τ 1 / (1 + thermalRatio τ) ^ 2 := by
  have hz := thermalRatio_pos τ
  have hg := sub_pos.mpr (thermalRatio_lt_one τ)
  rw [egbCoexistenceALogKernel_exact_quadratic_remainder]
  unfold egbCoexistenceASymmetricRatio
  field_simp

theorem egbCoexistenceALogKernel_ratio_quadratic_limit :
    Tendsto (fun τ => (egbCoexistenceALogKernel τ - 3) / (1 - thermalRatio τ) ^ 2) atBot (𝓝 ((2 : ℝ) / 5)) := by
  simp only [egbCoexistenceALogKernel_ratio_quadratic_formula]
  have h : Tendsto (fun τ => 3 * egbCoexistenceAKernelMoment τ 1 / (1 + thermalRatio τ) ^ 2) atBot
      (𝓝 ((3 * egbCoexistenceAKernelMomentCoefficient 1) / (1 + (1 : ℝ)) ^ 2)) :=
    ((tendsto_const_nhds (x := (3 : ℝ))).mul (egbCoexistenceAKernelMoment_critical_limit 1)).div
      ((tendsto_const_nhds.add thermalRatio_tendsto_atBot_one).pow 2) (by norm_num)
  norm_num [egbCoexistenceAKernelMomentCoefficient] at h
  exact h

theorem egbCoexistenceALogKernel_ratio_linear_limit :
    Tendsto (fun τ => (egbCoexistenceALogKernel τ - 3) / (1 - thermalRatio τ)) atBot (𝓝 0) := by
  have h := egbCoexistenceALogKernel_ratio_quadratic_limit.mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub thermalRatio_tendsto_atBot_one)
  have he : (fun τ => ((egbCoexistenceALogKernel τ - 3) / (1 - thermalRatio τ) ^ 2) * (1 - thermalRatio τ)) =
      (fun τ => (egbCoexistenceALogKernel τ - 3) / (1 - thermalRatio τ)) := by
    funext τ
    have hg := sub_pos.mpr (thermalRatio_lt_one τ)
    field_simp
  rw [he] at h
  norm_num at h
  exact h

end GaloisForLFunctions.HTGeometry
