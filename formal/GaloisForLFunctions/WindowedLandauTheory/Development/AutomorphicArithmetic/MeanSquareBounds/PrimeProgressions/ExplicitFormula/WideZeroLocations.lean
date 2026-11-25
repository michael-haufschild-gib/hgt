import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExplicitFormula.EntireCharacterPartialFraction
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExplicitFormula.PrimitiveZeroAtOrigin
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.PrincipalRightHalfZeroWindow

/-! Zeros and logarithmic derivatives transfer through principal pole removal. -/

open Complex DirichletCharacter Filter Metric Topology

open scoped Classical

noncomputable section

namespace QH.PrimeProgressions

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {s : ℂ}

theorem entireCharacterL_eq_zero_iff (hs : s ≠ 1) :
    entireCharacterL χ s = 0 ↔ χ.LFunction s = 0 := by
  unfold entireCharacterL
  split_ifs with hχ
  · subst χ
    rw [LFunctionTrivChar₁, Function.update_of_ne hs, mul_eq_zero]
    simp [sub_ne_zero.mpr hs]
  · rfl

theorem analyticOrderNatAt_entireCharacterL (hs : s ≠ 1) :
    analyticOrderNatAt (entireCharacterL χ) s = analyticOrderNatAt χ.LFunction s := by
  unfold entireCharacterL
  split_ifs with hχ
  · subst χ
    exact principal_analyticOrderNatAt hs
  · rfl

theorem logDeriv_entireCharacterL (hs : s ≠ 1) (hL : χ.LFunction s ≠ 0) :
    logDeriv (entireCharacterL χ) s =
      logDeriv χ.LFunction s + if χ = 1 then 1 / (s - 1) else 0 := by
  unfold entireCharacterL
  split_ifs with hc
  · subst χ
    have h₁ := sub_ne_zero.mpr hs
    rw [logDeriv_apply, logDeriv_apply, deriv_LFunctionTrivChar₁_apply_of_ne_one N hs,
      LFunctionTrivChar₁, Function.update_of_ne hs]
    field_simp
  · exact (add_zero _).symm

theorem entireCharacterL_ne_zero_of_one_le_re (hs : 1 ≤ s.re) : entireCharacterL χ s ≠ 0 := by
  by_cases h : s = 1
  · subst s
    unfold entireCharacterL
    split_ifs with hχ
    · exact LFunctionTrivChar₁_apply_one_ne_zero N
    · exact LFunction_apply_one_ne_zero hχ
  · exact fun hz => LFunction_ne_zero_of_one_le_re χ (.inr h) hs ((entireCharacterL_eq_zero_iff h).mp hz)

theorem entireCharacterL_order_ne_top : analyticOrderAt (entireCharacterL χ) s ≠ ⊤ := by
  intro h
  have e := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s
    (differentiable_entireCharacterL χ).analyticAt).1 h
  exact (entireCharacterL_ne_zero_of_one_le_re (χ := χ) (s := 2) (by norm_num))
    (by simp [e])

theorem entireCharacterL_zero_mem_strip_or_zero (hχ : χ.IsPrimitive) {t : ℝ}
    (hs : s ∈ closedBall (2 + t * I) (341 / 125)) (h : entireCharacterL χ s = 0) :
    (0 < s.re ∧ s.re < 1) ∨ s = 0 := by
  have h₁ : s.re < 1 := lt_of_not_ge fun e => entireCharacterL_ne_zero_of_one_le_re e h
  have hs₁ : s ≠ 1 := fun e => by norm_num [e] at h₁
  by_cases hs₀ : 0 < s.re
  · exact Or.inl ⟨hs₀, h₁⟩
  · refine Or.inr (eq_zero_and_order_of_primitive_zero_left hχ ?_ (le_of_not_gt hs₀)
      ((entireCharacterL_eq_zero_iff hs₁).mp h)).1
    rw [mem_closedBall, Complex.dist_eq] at hs
    have hc : (2 + t * I).re = 2 := by simp
    have hre := (abs_le.mp ((abs_re_le_norm (s - (2 + t * I))).trans hs)).1
    rw [sub_re, hc] at hre
    linarith only [hre]

end QH.PrimeProgressions
