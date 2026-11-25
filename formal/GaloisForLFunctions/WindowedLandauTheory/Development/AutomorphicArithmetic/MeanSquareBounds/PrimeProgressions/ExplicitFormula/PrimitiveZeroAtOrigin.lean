import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.PrimitiveZeroReflection

/-! The only possible zero immediately to the left of the critical strip is the simple zero at the origin. -/

open Complex DirichletCharacter Filter Topology

noncomputable section

namespace QH.PrimeProgressions

private theorem completedLFunction_ne_zero_left {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {s : ℂ}
    (hs : s.re ≤ 0) (h₀ : s ≠ 0 ∨ χ ≠ 1) : χ.completedLFunction s ≠ 0 := by
  have hFE := hχ.completedLFunction_one_sub (1 - s)
  rw [sub_sub_cancel] at hFE
  rw [hFE]
  have hw : 1 ≤ (1 - s).re := by rw [sub_re, one_re]; linarith only [hs]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hpow : (N : ℂ) ^ (1 - s - 1 / 2) ≠ 0 := by
    rw [cpow_def_of_ne_zero hN]
    exact exp_ne_zero _
  refine mul_ne_zero (mul_ne_zero hpow (rootNumber_ne_zero_of_primitive hχ)) ?_
  intro hC
  have hne : χ⁻¹ ≠ 1 ∨ 1 - s ≠ 1 := by
    rcases h₀ with h | h
    · exact Or.inr (fun e => h (by linear_combination -e))
    · exact Or.inl (inv_ne_one.mpr h)
  have h1s : 1 - s ≠ 0 := fun h => by norm_num [h] at hw
  apply LFunction_ne_zero_of_one_le_re χ⁻¹ hne hw
  rw [LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (.inl h1s), hC, zero_div]

private theorem inv_Gammaℝ_factor (s : ℂ) :
    (Gammaℝ s)⁻¹ = s / (2 * Real.pi) * (Gammaℝ (s + 2))⁻¹ := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [Gammaℝ_def]
  · have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [Gammaℝ_add_two hs]
    simp only [div_eq_mul_inv, mul_inv, inv_inv]
    generalize (Gammaℝ s)⁻¹ = g
    field_simp

private theorem inv_Gammaℝ_deriv_zero_ne_zero :
    deriv (fun s : ℂ => (Gammaℝ s)⁻¹) 0 ≠ 0 := by
  have he : (fun s => (Gammaℝ s)⁻¹) = fun s => s / (2 * Real.pi) * (Gammaℝ (s + 2))⁻¹ :=
    funext inv_Gammaℝ_factor
  have h₁ : HasDerivAt (fun s : ℂ => s / (2 * (Real.pi : ℂ))) (1 / (2 * Real.pi)) 0 :=
    (hasDerivAt_id' 0).div_const _
  have h₂ : HasDerivAt (fun s : ℂ => (Gammaℝ (s + 2))⁻¹)
      (deriv (fun s : ℂ => (Gammaℝ s)⁻¹) 2) 0 := by
    simpa only [zero_add] using HasDerivAt.comp_add_const (0 : ℂ) 2
      (differentiable_Gammaℝ_inv ((0 : ℂ) + 2)).hasDerivAt
  have hΓ : Gammaℝ 2 ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by norm_num)
  rw [he, (h₁.fun_mul h₂).deriv]
  simp [hΓ, Real.pi_ne_zero]

theorem eq_zero_and_order_of_primitive_zero_left {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {s : ℂ}
    (hs₁ : -1 < s.re) (hs₂ : s.re ≤ 0) (hzero : χ.LFunction s = 0) :
    s = 0 ∧ analyticOrderNatAt χ.LFunction s = 1 := by
  have h₀ : s ≠ 0 ∨ χ ≠ 1 := by
    by_contra! h
    obtain ⟨rfl, rfl⟩ := h
    have e : N = 1 := by
      have h := hχ
      rwa [DirichletCharacter.isPrimitive_def, conductor_one, eq_comm] at h
    subst N
    rw [LFunction_modOne_eq, riemannZeta_zero] at hzero
    norm_num at hzero
  have hC := completedLFunction_ne_zero_left hχ hs₂ h₀
  have hN₀ : s ≠ 0 ∨ N ≠ 1 := h₀.imp id (fun h e => h (level_one' χ e))
  have hf := LFunction_eq_completed_div_gammaFactor χ s hN₀
  have hG : χ.gammaFactor s = 0 := by
    by_contra h
    exact (div_ne_zero hC h) (hf.symm.trans hzero)
  have hs₀ : s = 0 := by
    rcases χ.even_or_odd with h | h
    · rw [h.gammaFactor_def] at hG
      obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hG
      have hre := congrArg Complex.re hn
      have hn' : (n : ℝ) < 1 := by
        simp at hre
        linarith only [hre, hs₁]
      have hz : n = 0 := by
        have : n < 1 := by exact_mod_cast hn'
        omega
      simpa [hz] using hn
    · rw [h.gammaFactor_def] at hG
      exact (Gammaℝ_ne_zero_of_re_pos (by rw [add_re, one_re]; linarith only [hs₁]) hG).elim
  subst s
  have hχ₁ : χ ≠ 1 := h₀.resolve_left (by simp)
  have hN₁ : N ≠ 1 := fun h => hχ₁ (level_one' χ h)
  have hEven : χ.Even := by
    rcases χ.even_or_odd with he | ho
    · exact he
    · rw [ho.gammaFactor_def, zero_add] at hG
      exact (Gammaℝ_ne_zero_of_re_pos (by norm_num) hG).elim
  have hexp : χ.LFunction = fun z => χ.completedLFunction z * (Gammaℝ z)⁻¹ := by
    funext z
    rw [LFunction_eq_completed_div_gammaFactor _ z (.inr hN₁), div_eq_mul_inv, hEven.gammaFactor_def]
  have hCd := (differentiable_completedLFunction hχ₁ 0).hasDerivAt
  have hGd := (differentiable_Gammaℝ_inv 0).hasDerivAt
  have hΓ₀ : Gammaℝ 0 = 0 := Gammaℝ_eq_zero_iff.mpr ⟨0, by simp⟩
  have hd : deriv χ.LFunction 0 ≠ 0 := by
    rw [hexp, (hCd.fun_mul hGd).deriv, hΓ₀, inv_zero, mul_zero, zero_add]
    exact mul_ne_zero hC inv_Gammaℝ_deriv_zero_ne_zero
  have ha := (differentiable_LFunction hχ₁).analyticAt 0
  exact ⟨rfl, by simp [analyticOrderNatAt, ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hd]⟩

end QH.PrimeProgressions
