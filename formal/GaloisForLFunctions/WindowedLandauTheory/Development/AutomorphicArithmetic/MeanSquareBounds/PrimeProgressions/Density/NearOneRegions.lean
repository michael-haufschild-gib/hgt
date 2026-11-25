import GaloisForLFunctions.WindowedLandauTheory.LandauZeroFreeBounds.NoZeroComplex

/-! The exceptional-zero alternative in the conductor-height normalization. -/

open Complex DirichletCharacter WindowedLandauTheory.ZeroFreeDirichlet

namespace QH.PrimeProgressions

private theorem inRegion_of_max_height {q : ℕ} [NeZero q] (hq : 3 ≤ q) {c : ℝ} (hc : 0 < c)
    {z : ℂ} (hz : 1 - (c / 2) / Real.log (max (q : ℝ) (q * |z.im|)) ≤ z.re) :
    InRegion c q z := by
  let M := max (q : ℝ) (q * |z.im|)
  have hM : (3 : ℝ) ≤ M := (by exact_mod_cast hq : (3 : ℝ) ≤ q).trans (le_max_left _ _)
  have hA : (q : ℝ) * (|z.im| + 2) ≤ M ^ 2 := by
    have h₁ : (q : ℝ) ≤ M := le_max_left _ _
    have h₂ : (q : ℝ) * |z.im| ≤ M := le_max_right _ _
    have h₃ := mul_le_mul_of_nonneg_right hM (show 0 ≤ M by linarith only [hM])
    nlinarith only [h₁, h₂, h₃]
  have hlog := Real.log_le_log (by positivity) hA
  rw [Real.log_pow] at hlog
  have hD := div_le_div_of_nonneg_left hc.le (log_mul_abs_add_two_pos q z.im)
    (show Real.log ((q : ℝ) * (|z.im| + 2)) ≤ 2 * Real.log M by
      simpa only [Nat.cast_ofNat] using hlog)
  have hreg : 1 - c / 2 / Real.log M ≤ z.re := hz
  rw [div_div] at hreg
  exact (sub_le_sub_left hD 1).trans hreg

private theorem character_value_real_of_sq {q : ℕ} (χ : DirichletCharacter ℂ q)
    (h : χ ^ 2 = 1) (a : ZMod q) : (χ a).im = 0 := by
  by_cases ha : IsUnit a
  · have h₂ : χ a * χ a = 1 := by
      rw [← pow_two, ← MulChar.pow_apply' χ two_ne_zero, h, MulChar.one_apply ha]
    rcases mul_self_eq_one_iff.mp h₂ with e | e <;> simp [e]
  · simp [MulChar.map_nonunit χ ha]

/-- The narrow Dirichlet region admits only a simple real zero of a real character.
The corresponding zeta strip is zero-free. -/
theorem primitive_near_one_regions :
    ∃ c : ℝ, 0 < c ∧
      (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → 3 ≤ q →
        ∀ z : ℂ, χ.LFunction z = 0 →
          1 - c / Real.log (max (q : ℝ) (q * |z.im|)) ≤ z.re →
          (∀ a : ZMod q, (χ a).im = 0) ∧ z.im = 0 ∧ analyticOrderNatAt χ.LFunction z = 1 ∧
          ∀ w : ℂ, χ.LFunction w = 0 →
            1 - c / Real.log (max (q : ℝ) (q * |w.im|)) ≤ w.re → w = z) ∧
      (∀ z : ℂ, riemannZeta z = 0 → 0 < z.re → z.re < 1 →
        z.re ≤ 1 - c / Real.log (|z.im| + 3)) := by
  obtain ⟨c, hc, hreg⟩ := zFRDirichlet
  refine ⟨c / 2, by positivity, ?_, ?_⟩
  · intro q _ χ hprim hq z hz hzz
    have hχ : χ ≠ 1 := by
      intro h
      rw [DirichletCharacter.isPrimitive_def, h, DirichletCharacter.conductor_one] at hprim
      omega
    obtain ⟨hsq, _, him, hder, huniq⟩ :=
      hreg q χ z (inRegion_of_max_height hq hc hzz) ⟨Or.inl hχ, hz⟩
    have ha := (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
    refine ⟨character_value_real_of_sq χ hsq, him, ?_, ?_⟩
    · simp [analyticOrderNatAt, ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz hder]
    · intro w hw hww
      exact (huniq χ w (inRegion_of_max_height hq hc hww) ⟨Or.inl hχ, hw⟩).2
  · intro z hz _ hlt
    by_contra h
    have hne : z ≠ 1 := by rintro rfl; simp at hlt
    have hlog : Real.log (|z.im| + 2) ≤ 2 * Real.log (|z.im| + 3) := by
      have h₁ := Real.log_le_log (show 0 < |z.im| + 2 by positivity)
        (show |z.im| + 2 ≤ |z.im| + 3 by linarith)
      have h₂ := Real.log_nonneg (show 1 ≤ |z.im| + 3 by linarith only [abs_nonneg z.im])
      linarith only [h₁, h₂]
    have hdiv := div_le_div_of_nonneg_left hc.le
      (Real.log_pos (show 1 < |z.im| + 2 by linarith only [abs_nonneg z.im])) hlog
    have hs : InRegion c 1 z := by
      have hgt := lt_of_not_ge h
      rw [div_div] at hgt
      unfold InRegion
      rw [Nat.cast_one, one_mul]
      exact (sub_le_sub_left hdiv 1).trans hgt.le
    have hzero : IsLZero (1 : DirichletCharacter ℂ 1) z :=
      ⟨Or.inr hne, by rwa [DirichletCharacter.LFunction_modOne_eq]⟩
    exact (hreg 1 1 z hs hzero).2.1 rfl

end QH.PrimeProgressions
