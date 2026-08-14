import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The high-frequency tail of a monotone symbol

For a nonnegative symbol `r` the weighted derivative integral telescopes:

`∫_ε^R r'(η) / (c + r(η)/2)² dη = 2/(c + r(ε)/2) - 2/(c + r(R)/2) ≤ 2/c`,

because `-2/(c + r/2)` is an exact primitive.  With `c = L - ‖T‖/2` this is the `O(1/L)` bound of the
high-frequency Gamma estimate: the whole oscillatory phase is retained, and only the monotonicity of
the symbol is used.
-/

open intervalIntegral MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The exact primitive of the weighted symbol derivative. -/
def symbolTailPrimitive (c : ℝ) (r : ℝ → ℝ) (η : ℝ) : ℝ := -2 / (c + r η / 2)

theorem hasDerivAt_symbolTailPrimitive {r r' : ℝ → ℝ} {c η : ℝ} (hc : 0 < c)
    (hrnn : 0 ≤ r η) (hr : HasDerivAt r (r' η) η) :
    HasDerivAt (symbolTailPrimitive c r) (r' η / (c + r η / 2) ^ 2) η := by
  have hden : 0 < c + r η / 2 := by linarith
  have hbase : HasDerivAt (fun x : ℝ => c + r x / 2) (r' η / 2) η := by
    have h := (hr.div_const 2).const_add c
    exact h
  have hinv := hbase.inv (ne_of_gt hden)
  have hscaled := hinv.const_mul (-2 : ℝ)
  have hval : (-2 : ℝ) * (-(r' η / 2) / (c + r η / 2) ^ 2) = r' η / (c + r η / 2) ^ 2 := by
    field_simp
  have hfun : symbolTailPrimitive c r = fun x : ℝ => (-2 : ℝ) * (c + r x / 2)⁻¹ := by
    funext x
    rw [symbolTailPrimitive]
    field_simp
  rw [hfun, ← hval]
  exact hscaled

/-- **The high-frequency tail estimate.** -/
theorem integral_deriv_div_sq_le {r r' : ℝ → ℝ} {c ε R : ℝ} (hc : 0 < c)
    (hrnn : ∀ η ∈ Set.uIcc ε R, 0 ≤ r η)
    (hr : ∀ η ∈ Set.uIcc ε R, HasDerivAt r (r' η) η)
    (hint : IntervalIntegrable (fun η => r' η / (c + r η / 2) ^ 2) volume ε R) :
    (∫ η in ε..R, r' η / (c + r η / 2) ^ 2) ≤ 2 / c := by
  have hderiv : ∀ η ∈ Set.uIcc ε R,
      HasDerivAt (symbolTailPrimitive c r) (r' η / (c + r η / 2) ^ 2) η :=
    fun η hη => hasDerivAt_symbolTailPrimitive hc (hrnn η hη) (hr η hη)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hftc, symbolTailPrimitive, symbolTailPrimitive]
  have hmemε : ε ∈ Set.uIcc ε R := Set.left_mem_uIcc
  have hmemR : R ∈ Set.uIcc ε R := Set.right_mem_uIcc
  have hdenε : 0 < c + r ε / 2 := by
    have := hrnn ε hmemε
    linarith
  have hdenR : 0 < c + r R / 2 := by
    have := hrnn R hmemR
    linarith
  have hstep : -2 / (c + r R / 2) - -2 / (c + r ε / 2) ≤ 2 / (c + r ε / 2) := by
    have h1 : -2 / (c + r R / 2) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg (by norm_num) hdenR.le
    have h2 : -2 / (c + r ε / 2) = -(2 / (c + r ε / 2)) := by ring
    linarith [h1, h2]
  have hlast : 2 / (c + r ε / 2) ≤ 2 / c := by
    apply div_le_div_of_nonneg_left (by norm_num) hc
    have := hrnn ε hmemε
    linarith
  linarith [hstep, hlast]

/-- **The high-frequency tail estimate for a monotone symbol of either sign.**  Only the
nonnegativity of the symbol and its monotonicity on the interval are used. -/
theorem integral_abs_deriv_div_sq_le {r r' : ℝ → ℝ} {c ε R : ℝ} (hc : 0 < c)
    (hrnn : ∀ η ∈ Set.uIcc ε R, 0 ≤ r η)
    (hr : ∀ η ∈ Set.uIcc ε R, HasDerivAt r (r' η) η)
    (hint : IntervalIntegrable (fun η => r' η / (c + r η / 2) ^ 2) volume ε R)
    (hmono : (∀ η ∈ Set.uIcc ε R, 0 ≤ r' η) ∨ (∀ η ∈ Set.uIcc ε R, r' η ≤ 0)) :
    (∫ η in ε..R, |r' η| / (c + r η / 2) ^ 2) ≤ 2 / c := by
  have hmemε : ε ∈ Set.uIcc ε R := Set.left_mem_uIcc
  have hmemR : R ∈ Set.uIcc ε R := Set.right_mem_uIcc
  have hdenε : 0 < c + r ε / 2 := by
    have := hrnn ε hmemε
    linarith
  have hdenR : 0 < c + r R / 2 := by
    have := hrnn R hmemR
    linarith
  rcases hmono with hpos | hneg
  · have hcongr : (∫ η in ε..R, |r' η| / (c + r η / 2) ^ 2)
        = ∫ η in ε..R, r' η / (c + r η / 2) ^ 2 := by
      refine intervalIntegral.integral_congr fun η hη => ?_
      rw [abs_of_nonneg (hpos η hη)]
    rw [hcongr]
    exact integral_deriv_div_sq_le hc hrnn hr hint
  · have hcongr : (∫ η in ε..R, |r' η| / (c + r η / 2) ^ 2)
        = -∫ η in ε..R, r' η / (c + r η / 2) ^ 2 := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun η hη => ?_
      show |r' η| / (c + r η / 2) ^ 2 = -(r' η / (c + r η / 2) ^ 2)
      rw [abs_of_nonpos (hneg η hη)]
      ring
    have hderiv : ∀ η ∈ Set.uIcc ε R,
        HasDerivAt (symbolTailPrimitive c r) (r' η / (c + r η / 2) ^ 2) η :=
      fun η hη => hasDerivAt_symbolTailPrimitive hc (hrnn η hη) (hr η hη)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rw [hcongr, hftc, symbolTailPrimitive, symbolTailPrimitive]
    have h1 : -2 / (c + r ε / 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by norm_num) hdenε.le
    have h2 : 2 / (c + r R / 2) ≤ 2 / c := by
      apply div_le_div_of_nonneg_left (by norm_num) hc
      have := hrnn R hmemR
      linarith
    have h3 : -(-2 / (c + r R / 2) - -2 / (c + r ε / 2))
        = 2 / (c + r R / 2) + -2 / (c + r ε / 2) := by ring
    rw [h3]
    linarith [h1, h2]

/-- **The half-power tail estimate.**  `∫_ε^R η^{-3/2} dη ≤ 2 ε^{-1/2}`. -/
theorem integral_rpow_neg_three_halves_le {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) :
    (∫ η in ε..R, η ^ (-(3:ℝ)/2)) ≤ 2 * ε ^ (-(1:ℝ)/2) := by
  have hzero : (0:ℝ) ∉ Set.uIcc ε R := by
    rw [Set.uIcc_of_le hεR]
    intro hcon
    exact absurd hcon.1 (not_le.mpr hε)
  rw [integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
  have hexp : -(3:ℝ)/2 + 1 = -(1:ℝ)/2 := by ring
  rw [hexp]
  have hR : 0 < R := lt_of_lt_of_le hε hεR
  have hRpos : (0:ℝ) < R ^ (-(1:ℝ)/2) := Real.rpow_pos_of_pos hR _
  have hεpos : (0:ℝ) < ε ^ (-(1:ℝ)/2) := Real.rpow_pos_of_pos hε _
  have hval : (R ^ (-(1:ℝ)/2) - ε ^ (-(1:ℝ)/2)) / (-(1:ℝ)/2)
      = 2 * (ε ^ (-(1:ℝ)/2) - R ^ (-(1:ℝ)/2)) := by
    field_simp
    ring
  rw [hval]
  nlinarith [hRpos, hεpos]

end

end GaloisForLFunctions.HTGeometry
