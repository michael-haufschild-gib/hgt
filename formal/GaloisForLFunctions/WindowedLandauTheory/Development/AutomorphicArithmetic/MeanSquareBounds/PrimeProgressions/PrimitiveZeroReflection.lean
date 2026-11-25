import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! The functional equation preserves analytic multiplicities of primitive zeros in the critical strip. -/

open Complex DirichletCharacter Filter Topology

noncomputable section

namespace QH.PrimeProgressions

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

private theorem completed_analytic {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1) :
    AnalyticAt ℂ χ.completedLFunction s := by
  have e₀ : s ≠ 0 := fun e => by norm_num [e] at h₀
  have e₁ : s ≠ 1 := fun e => by norm_num [e] at h₁
  refine analyticAt_iff_eventually_differentiableAt.mpr ?_
  filter_upwards [eventually_ne_nhds e₀, eventually_ne_nhds e₁] with z hz₀ hz₁
  exact differentiableAt_completedLFunction χ z (.inl hz₀) (.inl hz₁)

private theorem gammaInv_analytic (χ : DirichletCharacter ℂ N) (s : ℂ) :
    AnalyticAt ℂ (fun z => (χ.gammaFactor z)⁻¹) s := by
  rcases χ.even_or_odd with h | h
  · have hA : AnalyticAt ℂ (fun z => (Gammaℝ z)⁻¹) s :=
      differentiable_Gammaℝ_inv.analyticAt s
    simpa only [h.gammaFactor_def] using hA
  · have hA : AnalyticAt ℂ (fun z => (Gammaℝ z)⁻¹) (s + 1) :=
      differentiable_Gammaℝ_inv.analyticAt (s + 1)
    have hadd : AnalyticAt ℂ (fun z : ℂ => z + 1) s := analyticAt_id.add analyticAt_const
    simpa only [Function.comp_def, h.gammaFactor_def] using
      (AnalyticAt.comp (f := fun z : ℂ => z + 1) (x := s) hA hadd)

omit [NeZero N] in
private theorem gamma_ne_zero (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos (by simpa only [add_re, one_re] using add_pos hs zero_lt_one)

private theorem analyticOrderAt_LFunction_eq_completed (χ : DirichletCharacter ℂ N)
    {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1) :
    analyticOrderAt χ.LFunction s = analyticOrderAt χ.completedLFunction s := by
  have hs : s ≠ 0 := fun e => by norm_num [e] at h₀
  have e : χ.LFunction =ᶠ[𝓝 s] χ.completedLFunction * (fun z => (χ.gammaFactor z)⁻¹) := by
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hs] with z hz
    exact (LFunction_eq_completed_div_gammaFactor χ z (.inl hz)).trans (div_eq_mul_inv _ _)
  rw [analyticOrderAt_congr e, analyticOrderAt_mul (completed_analytic h₀ h₁) (gammaInv_analytic χ s),
    (gammaInv_analytic χ s).analyticOrderAt_eq_zero.mpr (inv_ne_zero (gamma_ne_zero χ h₀)), add_zero]

theorem rootNumber_ne_zero_of_primitive (hχ : χ.IsPrimitive) : χ.rootNumber ≠ 0 := by
  intro h
  have h₂ := hχ.completedLFunction_one_sub (-1)
  rw [h, mul_zero, zero_mul] at h₂
  norm_num at h₂
  have e := LFunction_eq_completed_div_gammaFactor χ 2 (.inl (by norm_num))
  rw [h₂, zero_div] at e
  exact (χ.LFunction_ne_zero_of_one_le_re (.inr (by norm_num)) (by norm_num)) e

theorem LFunction_one_sub_eq_zero_iff (hχ : χ.IsPrimitive) {s : ℂ}
    (h₀ : 0 < s.re) (h₁ : s.re < 1) :
    χ.LFunction (1 - s) = 0 ↔ (χ⁻¹).LFunction s = 0 := by
  have r₀ : 0 < (1 - s).re := by simpa only [sub_re, one_re, sub_pos] using h₁
  have e₀ : s ≠ 0 := fun e => by norm_num [e] at h₀
  have e₁ : 1 - s ≠ 0 := fun e => by norm_num [e] at r₀
  have hN : (N : ℂ) ^ (s - 1 / 2) ≠ 0 := by
    rw [cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne N))]
    exact exp_ne_zero _
  rw [LFunction_eq_completed_div_gammaFactor χ _ (.inl e₁),
    LFunction_eq_completed_div_gammaFactor χ⁻¹ _ (.inl e₀), hχ.completedLFunction_one_sub]
  simp only [div_eq_mul_inv, one_mul] at hN
  simp only [div_eq_mul_inv, one_mul, mul_eq_zero, inv_eq_zero,
    gamma_ne_zero χ r₀, gamma_ne_zero χ⁻¹ h₀,
    hN, rootNumber_ne_zero_of_primitive hχ, false_or, or_false]

/-- Reflection preserves the order of a primitive Dirichlet L-function at every point in the strip. -/
theorem analyticOrderNatAt_LFunction_one_sub (hχ : χ.IsPrimitive) {s : ℂ}
    (h₀ : 0 < s.re) (h₁ : s.re < 1) :
    analyticOrderNatAt χ.LFunction (1 - s) = analyticOrderNatAt (χ⁻¹).LFunction s := by
  have r₀ : 0 < (1 - s).re := by simpa only [sub_re, one_re, sub_pos] using h₁
  have r₁ : (1 - s).re < 1 := by rw [sub_re, one_re]; linarith only [h₀]
  let R : ℂ → ℂ := fun z => 1 - z
  have hRa : AnalyticAt ℂ R s := analyticAt_const.sub analyticAt_id
  have hRd : deriv R s ≠ 0 := by simp [R]
  let E : ℂ → ℂ := fun z => (N : ℂ) ^ (z - 1 / 2) * χ.rootNumber
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hEa : AnalyticAt ℂ E s := by
    simp only [E, cpow_def_of_ne_zero hN]
    exact (analyticAt_cexp.comp (analyticAt_const.mul (analyticAt_id.sub analyticAt_const))).mul
      analyticAt_const
  have hE : E s ≠ 0 := by
    change (N : ℂ) ^ (s - 1 / 2) * χ.rootNumber ≠ 0
    rw [cpow_def_of_ne_zero hN]
    exact mul_ne_zero (exp_ne_zero _) (rootNumber_ne_zero_of_primitive hχ)
  have he : χ.completedLFunction ∘ R = E * (χ⁻¹).completedLFunction :=
    funext hχ.completedLFunction_one_sub
  unfold analyticOrderNatAt
  rw [analyticOrderAt_LFunction_eq_completed χ r₀ r₁,
    analyticOrderAt_LFunction_eq_completed χ⁻¹ h₀ h₁]
  change (analyticOrderAt χ.completedLFunction (R s)).toNat =
    (analyticOrderAt (χ⁻¹).completedLFunction s).toNat
  rw [← analyticOrderAt_comp_of_deriv_ne_zero (f := χ.completedLFunction) hRa hRd, he,
    analyticOrderAt_mul hEa (completed_analytic h₀ h₁), hEa.analyticOrderAt_eq_zero.mpr hE, zero_add]

end QH.PrimeProgressions
