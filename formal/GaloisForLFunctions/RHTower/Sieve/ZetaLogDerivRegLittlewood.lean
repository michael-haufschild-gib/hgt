import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegUniform
import GaloisForLFunctions.RHTower.Sieve.ZetaLittlewoodArbitraryConstant

/-!
# The regular part on a strip of arbitrary width

`exists_bound_zetaLogDerivReg_uniform` bounds `zetaLogDerivReg` by `C log²K` on the strip
`1 - 1/40000/log K ≤ Re s ≤ 9/8`, `|Im s| ≤ K`.  Both the width constant and the exponent come from
the exponent-one region.

With the Littlewood region the width constant is arbitrary and the bound carries the extra
`log log K`:

```text
‖zetaLogDerivReg s‖  ≤  C · log²K / log log K      on   1 - A/log K ≤ Re s ≤ 9/8 ,  |Im s| ≤ K
```

for every `A`.  The transfer from the height `|Im s|` of the point to the contour parameter `K` uses
that `x ↦ x²/log x` is increasing past `e`, which is where the argument differs from the
exponent-one one.
-/

namespace RHTower.Sieve

open Complex

/-- `x ↦ x²/log x` is increasing past `e`. -/
theorem sq_div_log_mono {x y : ℝ} (hx : 1 ≤ Real.log x) (hx0 : 0 < x) (hxy : x ≤ y) :
    x ^ (2 : ℕ) / Real.log x ≤ y ^ (2 : ℕ) / Real.log y := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hlogy : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hly1 : (1 : ℝ) ≤ Real.log y := by linarith
  have hx1 : (1 : ℝ) ≤ x := by
    by_contra hcon
    have : Real.log x ≤ 0 := Real.log_nonpos (by linarith) (le_of_lt (not_le.mp hcon))
    linarith
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  -- `log y ≤ log x + (y² - x²)/x²`
  have hratio : Real.log (y / x) ≤ (y ^ (2 : ℕ) - x ^ (2 : ℕ)) / x ^ (2 : ℕ) := by
    have h1 : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : y / x - 1 ≤ (y ^ (2 : ℕ) - x ^ (2 : ℕ)) / x ^ (2 : ℕ) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < x ^ (2 : ℕ))]
      have hxne : x ≠ 0 := ne_of_gt hx0
      field_simp
      nlinarith [hx0, hxy]
    linarith
  have hsplit : Real.log (y / x) = Real.log y - Real.log x :=
    Real.log_div (ne_of_gt hy0) (ne_of_gt hx0)
  rw [hsplit] at hratio
  have hkey : Real.log y ≤ Real.log x + (y ^ (2 : ℕ) - x ^ (2 : ℕ)) / x ^ (2 : ℕ) := by linarith
  have hmul : x ^ (2 : ℕ) * Real.log y ≤ x ^ (2 : ℕ) * Real.log x + (y ^ (2 : ℕ) - x ^ (2 : ℕ)) := by
    have hstep := mul_le_mul_of_nonneg_left hkey (by positivity : (0 : ℝ) ≤ x ^ (2 : ℕ))
    have hcancel : x ^ (2 : ℕ) * ((y ^ (2 : ℕ) - x ^ (2 : ℕ)) / x ^ (2 : ℕ)) = y ^ (2 : ℕ) - x ^ (2 : ℕ) := by
      field_simp
    nlinarith [hstep, hcancel]
  have hsq : (0 : ℝ) ≤ y ^ (2 : ℕ) - x ^ (2 : ℕ) := by nlinarith [hx1, hxy]
  have hlx : (0 : ℝ) ≤ Real.log x - 1 := by linarith
  nlinarith [hmul, mul_nonneg hsq hlx]

/-- **The strip of arbitrary exponent-one width is zero-free, uniformly up to height `K`.** -/
theorem exists_zeta_uniform_arbitrary_zero_free (A : ℝ) (hA : 0 < A) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ (s : ℂ) (K : ℝ), L₀ ≤ Real.log K → |s.im| ≤ K →
      1 - A / Real.log K ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  obtain ⟨T, hT3, hregion⟩ := exists_zero_free_region_arbitrary_constant (2 * A)
  obtain ⟨δ, hδ0, hbox⟩ := exists_zero_free_box T
  refine ⟨max 1 (A / δ), le_max_left _ _, ?_⟩
  intro s K hL hKim hre hne
  have hL1 : (1 : ℝ) ≤ Real.log K := le_trans (le_max_left _ _) hL
  have hLδ : A / δ ≤ Real.log K := le_trans (le_max_right _ _) hL
  rcases le_or_gt 1 s.re with hx1 | hx1
  · exact riemannZeta_ne_zero_of_one_le_re hx1
  rcases le_or_gt T |s.im| with hbig | hsmall
  · have habs3 : (3 : ℝ) ≤ |s.im| := le_trans hT3 hbig
    have hlog1 : (1 : ℝ) ≤ Real.log |s.im| :=
      le_trans one_le_log_three (Real.log_le_log (by norm_num) habs3)
    have hpos : (0 : ℝ) < Real.log |s.im| := by linarith
    have hlt : Real.log |s.im| ≤ Real.log K := Real.log_le_log (by linarith) hKim
    have h1 : A / Real.log K ≤ A / Real.log |s.im| :=
      div_le_div_of_nonneg_left hA.le hpos hlt
    have h2 : A / Real.log |s.im| < 2 * A / Real.log |s.im| := by
      rw [div_lt_div_iff₀ hpos hpos]
      nlinarith [hA, hpos]
    have hsplit : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I :=
      (Complex.re_add_im s).symm
    rw [hsplit]
    exact hregion s.re s.im hbig hx1.le (by linarith)
  · have hδcmp : A / Real.log K ≤ δ := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < Real.log K)]
      rw [div_le_iff₀ hδ0] at hLδ
      nlinarith [hLδ]
    exact hbox s (by linarith) hx1.le (le_of_lt hsmall) hne

set_option maxHeartbeats 1000000 in
/-- **The regular part on the strip of arbitrary width, at Littlewood strength.** -/
theorem exists_bound_zetaLogDerivReg_uniform_littlewood (A : ℝ) (hA : 0 < A) :
    ∃ C L₀ : ℝ, 0 < C ∧ 1 ≤ L₀ ∧ ∀ (s : ℂ) (K : ℝ), L₀ ≤ Real.log K → |s.im| ≤ K →
      1 - A / Real.log K ≤ s.re → s.re ≤ 9 / 8 →
      ‖zetaLogDerivReg s‖ ≤ C * Real.log K ^ (2 : ℕ) / Real.log (Real.log K) := by
  obtain ⟨C₁, T₁, hC₁0, hT₁0, hbound⟩ := exists_logDeriv_zeta_bound_arbitrary_constant A
  obtain ⟨δ, hδ0, M₀, hM₀0, hbox⟩ :=
    exists_bound_zetaLogDerivReg_box 2 (max T₁ 16) (by norm_num) (by positivity)
  obtain ⟨L₁, hL₁1, hzf⟩ := exists_zeta_uniform_arbitrary_zero_free A hA
  refine ⟨C₁ + M₀ + 1, max (max (Real.exp 1) (A / δ)) L₁, by linarith,
    le_trans hL₁1 (le_max_right _ _), ?_⟩
  intro s K hL hKim hre hhi
  have hLe : Real.exp 1 ≤ Real.log K :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hL)
  have hL1 : (1 : ℝ) ≤ Real.log K := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hLδ : A / δ ≤ Real.log K :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hL)
  have hL₁K : L₁ ≤ Real.log K := le_trans (le_max_right _ _) hL
  have hLL1 : (1 : ℝ) ≤ Real.log (Real.log K) := by
    have h := Real.log_le_log (Real.exp_pos 1) hLe
    rwa [Real.log_exp] at h
  have hLL0 : (0 : ℝ) < Real.log (Real.log K) := by linarith
  have hLsq : (1 : ℝ) ≤ Real.log K ^ (2 : ℕ) / Real.log (Real.log K) := by
    rw [le_div_iff₀ hLL0]
    nlinarith [hL1, hLL1, Real.log_le_sub_one_of_pos (show (0:ℝ) < Real.log K by linarith)]
  rcases le_or_gt (max T₁ 16) |s.im| with hbig | hsmall
  · have hT₁im : T₁ ≤ |s.im| := le_trans (le_max_left _ _) hbig
    have habs16 : (16 : ℝ) ≤ |s.im| := le_trans (le_max_right _ _) hbig
    have habs4 : (4 : ℝ) ≤ |s.im| := by linarith
    have hlog1 : (1 : ℝ) ≤ Real.log |s.im| := one_le_log_abs habs4
    have hlogE : Real.exp 1 ≤ Real.log |s.im| := by
      have h16 : Real.log ((16 : ℝ)) ≤ Real.log |s.im| :=
        Real.log_le_log (by norm_num) habs16
      have h16eq : Real.log ((16 : ℝ)) = 4 * Real.log 2 := by
        rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]; norm_num
      have hlog2 := Real.log_two_gt_d9
      have hexp1 := Real.exp_one_lt_d9
      rw [h16eq] at h16
      linarith
    have hloglog1 : (1 : ℝ) ≤ Real.log (Real.log |s.im|) := by
      have h := Real.log_le_log (Real.exp_pos 1) hlogE
      rwa [Real.log_exp] at h
    have hlt : Real.log |s.im| ≤ Real.log K := Real.log_le_log (by linarith) hKim
    have hwide : 1 - A / Real.log |s.im| ≤ s.re := by
      have h1 : A / Real.log K ≤ A / Real.log |s.im| :=
        div_le_div_of_nonneg_left hA.le (by linarith) hlt
      linarith
    have hsplit : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I :=
      (Complex.re_add_im s).symm
    have hres : ‖logDeriv riemannZeta s‖
        ≤ C₁ * Real.log |s.im| ^ (2 : ℕ) / Real.log (Real.log |s.im|) := by
      have h := hbound s.re s.im hT₁im hwide hhi
      rwa [← hsplit] at h
    have hs1 : s ≠ 1 := by
      intro h
      rw [h] at habs4
      simp only [Complex.one_im, abs_zero] at habs4
      linarith
    have hzu : zetaResidueUnit s ≠ 0 :=
      (zetaResidueUnit_ne_zero_iff hs1).2 (hzf s K hL₁K hKim hre hs1)
    have hdecomp : -(logDeriv riemannZeta s) = (s - 1)⁻¹ + zetaLogDerivReg s :=
      neg_logDeriv_riemannZeta_eq hs1 hzu
    have hpole : ‖(s - 1)⁻¹‖ ≤ 1 / 4 := by
      rw [norm_inv]
      have hge : (4 : ℝ) ≤ ‖s - 1‖ := by
        have h := Complex.abs_im_le_norm (s - 1)
        simp only [Complex.sub_im, Complex.one_im, sub_zero] at h
        linarith [habs4, h]
      rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have hreg : ‖zetaLogDerivReg s‖ ≤ ‖logDeriv riemannZeta s‖ + ‖(s - 1)⁻¹‖ := by
      have heq : zetaLogDerivReg s = -(logDeriv riemannZeta s) - (s - 1)⁻¹ := by
        rw [hdecomp]; ring
      rw [heq]
      calc ‖-(logDeriv riemannZeta s) - (s - 1)⁻¹‖
          ≤ ‖-(logDeriv riemannZeta s)‖ + ‖(s - 1)⁻¹‖ := norm_sub_le _ _
        _ = ‖logDeriv riemannZeta s‖ + ‖(s - 1)⁻¹‖ := by rw [norm_neg]
    have hmono : Real.log |s.im| ^ (2 : ℕ) / Real.log (Real.log |s.im|)
        ≤ Real.log K ^ (2 : ℕ) / Real.log (Real.log K) :=
      sq_div_log_mono hloglog1 (by linarith) hlt
    have hCmono : C₁ * Real.log |s.im| ^ (2 : ℕ) / Real.log (Real.log |s.im|)
        ≤ C₁ * (Real.log K ^ (2 : ℕ) / Real.log (Real.log K)) := by
      have hstep := mul_le_mul_of_nonneg_left hmono hC₁0.le
      have heq : C₁ * Real.log |s.im| ^ (2 : ℕ) / Real.log (Real.log |s.im|)
          = C₁ * (Real.log |s.im| ^ (2 : ℕ) / Real.log (Real.log |s.im|)) := by ring
      linarith [hstep, heq.le, heq.ge]
    have hfinal : ‖zetaLogDerivReg s‖
        ≤ C₁ * (Real.log K ^ (2 : ℕ) / Real.log (Real.log K)) + 1 / 4 := by
      linarith [hreg, hres, hpole, hCmono]
    have hexp : (C₁ + M₀ + 1) * Real.log K ^ (2 : ℕ) / Real.log (Real.log K)
        = C₁ * (Real.log K ^ (2 : ℕ) / Real.log (Real.log K))
          + (M₀ + 1) * (Real.log K ^ (2 : ℕ) / Real.log (Real.log K)) := by
      field_simp
      ring
    nlinarith [hfinal, hexp.le, hexp.ge, hLsq, hM₀0]
  · have hδcmp : A / Real.log K ≤ δ := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < Real.log K)]
      rw [div_le_iff₀ hδ0] at hLδ
      nlinarith [hLδ]
    have hres := hbox s (by linarith) (by linarith) (le_of_lt hsmall)
    have hexp : (C₁ + M₀ + 1) * Real.log K ^ (2 : ℕ) / Real.log (Real.log K)
        = (C₁ + M₀ + 1) * (Real.log K ^ (2 : ℕ) / Real.log (Real.log K)) := by ring
    nlinarith [hres, hLsq, hC₁0, hM₀0, hexp.le, hexp.ge]

end RHTower.Sieve
