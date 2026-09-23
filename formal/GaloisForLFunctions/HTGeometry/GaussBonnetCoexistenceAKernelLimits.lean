import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAWeights
import GaloisForLFunctions.HTGeometry.GaussBonnetCriticalEndpoint

/-!
# Critical and cold limits of the logarithmic coexistence kernel

Squeeze the exact kernel between its proven bounds. The kernel tends to
three at the critical endpoint; its product with the squared radius ratio
vanishes in the cold limit. This controls the quadratic discriminant even
though the unweighted kernel need not remain bounded.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open CPV

theorem egbCoexistenceALogKernel_tendsto_critical : Tendsto egbCoexistenceALogKernel atBot (𝓝 3) := by
  have hz := thermalRatio_tendsto_atBot_one
  have hu : Tendsto (fun τ => (thermalRatio τ ^ (2 : ℕ) + thermalRatio τ + 1) / thermalRatio τ) atBot
      (𝓝 (((1 : ℝ) ^ (2 : ℕ) + 1 + 1) / 1)) :=
    (((hz.pow 2).add hz).add tendsto_const_nhds).div hz one_ne_zero
  norm_num at hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    egbCoexistenceALogKernel_lower_bound egbCoexistenceALogKernel_upper_bound

/-- Uniform control of the kernel combination that enters the cold discriminant. -/
theorem egbCoexistenceALogKernel_weighted_bounds (τ : ℝ) :
    0 ≤ egbCoexistenceALogKernel τ * thermalRatio τ ^ (2 : ℕ) ∧
      egbCoexistenceALogKernel τ * thermalRatio τ ^ (2 : ℕ) ≤
        thermalRatio τ * (thermalRatio τ ^ (2 : ℕ) + thermalRatio τ + 1) := by
  have hz := thermalRatio_pos τ
  have hH := egbCoexistenceALogKernel_pos τ
  have h := (le_div_iff₀ hz).1 (egbCoexistenceALogKernel_upper_bound τ)
  have hm := mul_le_mul_of_nonneg_right h hz.le
  exact ⟨by positivity, by nlinarith⟩

theorem egbCoexistenceALogKernel_weighted_cold_limit :
    Tendsto (fun τ => egbCoexistenceALogKernel τ * thermalRatio τ ^ (2 : ℕ)) atTop (𝓝 0) := by
  have hz := thermalRatio_tendsto_atTop_zero
  have hu : Tendsto (fun τ => thermalRatio τ * (thermalRatio τ ^ (2 : ℕ) + thermalRatio τ + 1)) atTop
      (𝓝 ((0 : ℝ) * (0 ^ (2 : ℕ) + 0 + 1))) := hz.mul (((hz.pow 2).add hz).add tendsto_const_nhds)
  norm_num at hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun τ => (egbCoexistenceALogKernel_weighted_bounds τ).1)
    (fun τ => (egbCoexistenceALogKernel_weighted_bounds τ).2)

theorem egbCoexistenceAQuadraticA_critical_limit : Tendsto egbCoexistenceAQuadraticA atBot (𝓝 24) := by
  have hz := thermalRatio_tendsto_atBot_one
  have h : Tendsto egbCoexistenceAQuadraticA atBot (𝓝 (4 * 3 * ((1 : ℝ) ^ (2 : ℕ) + 1))) :=
    (tendsto_const_nhds.mul egbCoexistenceALogKernel_tendsto_critical).mul ((hz.pow 2).add tendsto_const_nhds)
  norm_num at h
  exact h

theorem egbCoexistenceAQuadraticC_critical_limit : Tendsto egbCoexistenceAQuadraticC atBot (𝓝 2) := by
  have hz := thermalRatio_tendsto_atBot_one
  have h : Tendsto egbCoexistenceAQuadraticC atBot (𝓝 ((1 : ℝ) ^ (2 : ℕ) * (1 ^ (2 : ℕ) + 1))) :=
    (hz.pow 2).mul ((hz.pow 2).add tendsto_const_nhds)
  norm_num at h
  exact h

theorem egbFixedChargeABase_critical_limit : Tendsto egbFixedChargeABase atBot (𝓝 12) := by
  have hz := thermalRatio_tendsto_atBot_one
  have h : Tendsto egbFixedChargeABase atBot (𝓝 (6 * ((1 : ℝ) ^ (2 : ℕ) + 1))) :=
    egbCoexistenceShape_tendsto_critical.mul ((hz.pow 2).add tendsto_const_nhds)
  norm_num at h
  exact h

theorem egbFixedChargeALinearCorrection_critical_limit : Tendsto egbFixedChargeALinearCorrection atBot (𝓝 (-12)) := by
  have hz := thermalRatio_tendsto_atBot_one
  have h : Tendsto egbFixedChargeALinearCorrection atBot
      (𝓝 (4 * (1 : ℝ) ^ (2 : ℕ) * 3 - 8 * 1 * (1 ^ (2 : ℕ) + 1 + 1))) :=
    ((tendsto_const_nhds.mul (hz.pow 2)).mul egbCoexistenceALogKernel_tendsto_critical).sub
      ((tendsto_const_nhds.mul hz).mul (((hz.pow 2).add hz).add tendsto_const_nhds))
  norm_num at h
  exact h

theorem egbCoexistenceAQuadraticC_cold_limit : Tendsto egbCoexistenceAQuadraticC atTop (𝓝 0) := by
  have hz := thermalRatio_tendsto_atTop_zero
  have h : Tendsto egbCoexistenceAQuadraticC atTop (𝓝 ((0 : ℝ) ^ (2 : ℕ) * (0 ^ (2 : ℕ) + 1))) :=
    (hz.pow 2).mul ((hz.pow 2).add tendsto_const_nhds)
  norm_num at h
  exact h

theorem egbFixedChargeABase_cold_limit : Tendsto egbFixedChargeABase atTop (𝓝 1) := by
  have hz := thermalRatio_tendsto_atTop_zero
  have h : Tendsto egbFixedChargeABase atTop (𝓝 (1 * ((0 : ℝ) ^ (2 : ℕ) + 1))) :=
    egbCoexistenceShape_tendsto_cold.mul ((hz.pow 2).add tendsto_const_nhds)
  norm_num at h
  exact h

theorem egbFixedChargeALinearCorrection_cold_limit : Tendsto egbFixedChargeALinearCorrection atTop (𝓝 0) := by
  have hz := thermalRatio_tendsto_atTop_zero
  have he : egbFixedChargeALinearCorrection = fun τ =>
      4 * (egbCoexistenceALogKernel τ * thermalRatio τ ^ (2 : ℕ)) -
        8 * thermalRatio τ * (thermalRatio τ ^ (2 : ℕ) + thermalRatio τ + 1) := by
    funext τ
    unfold egbFixedChargeALinearCorrection
    ring
  rw [he]
  have h : Tendsto (fun τ => 4 * (egbCoexistenceALogKernel τ * thermalRatio τ ^ (2 : ℕ)) -
      8 * thermalRatio τ * (thermalRatio τ ^ (2 : ℕ) + thermalRatio τ + 1)) atTop
      (𝓝 ((4 : ℝ) * 0 - 8 * 0 * (0 ^ (2 : ℕ) + 0 + 1))) :=
    (tendsto_const_nhds.mul egbCoexistenceALogKernel_weighted_cold_limit).sub
      ((tendsto_const_nhds.mul hz).mul (((hz.pow 2).add hz).add tendsto_const_nhds))
  norm_num at h
  exact h

/-- Exact cancellation isolates the only kernel combination needed in the cold discriminant. -/
theorem egbCoexistenceA_quadratic_product (τ : ℝ) :
    egbCoexistenceAQuadraticA τ * egbCoexistenceAQuadraticC τ =
      4 * (egbCoexistenceALogKernel τ * thermalRatio τ ^ (2 : ℕ)) * (thermalRatio τ ^ (2 : ℕ) + 1) ^ (2 : ℕ) := by
  unfold egbCoexistenceAQuadraticA egbCoexistenceAQuadraticC
  ring

theorem egbCoexistenceA_quadratic_product_cold_limit :
    Tendsto (fun τ => egbCoexistenceAQuadraticA τ * egbCoexistenceAQuadraticC τ) atTop (𝓝 0) := by
  simp only [egbCoexistenceA_quadratic_product]
  have hz := thermalRatio_tendsto_atTop_zero
  have h : Tendsto (fun τ => 4 * (egbCoexistenceALogKernel τ * thermalRatio τ ^ (2 : ℕ)) * (thermalRatio τ ^ (2 : ℕ) + 1) ^ (2 : ℕ)) atTop
      (𝓝 ((4 : ℝ) * 0 * (0 ^ (2 : ℕ) + 1) ^ (2 : ℕ))) :=
    (tendsto_const_nhds.mul egbCoexistenceALogKernel_weighted_cold_limit).mul
      (((hz.pow 2).add tendsto_const_nhds).pow 2)
  norm_num at h
  exact h

end GaloisForLFunctions.HTGeometry
