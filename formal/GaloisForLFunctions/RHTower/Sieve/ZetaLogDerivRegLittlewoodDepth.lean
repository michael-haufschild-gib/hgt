import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegLittlewood
import GaloisForLFunctions.RHTower.Sieve.ZetaLittlewoodRegionNine

/-!
# The regular part on a strip whose width grows with the height

`exists_bound_zetaLogDerivReg_uniform_littlewood` bounds `zetaLogDerivReg` on the strip
`1 - A/log K ≤ Re s ≤ 9/8`, `|Im s| ≤ K`, for each fixed depth `A`; the constant depends on `A`.
A depth that grows with `K` is a different statement, and it is the one Littlewood's region
supplies:

```text
‖zetaLogDerivReg s‖ ≤ C·log²K/log log K    on   1 - c·log log K/log K ≤ Re s ≤ 9/8 ,  |Im s| ≤ K
```

with `c` and `C` absolute.  The transfer from the height `|Im s|` of the point to the parameter `K`
uses that `u ↦ log u/u` is antitone past `e`, so the strip at `K` is contained in the strip at every
smaller height.
-/

namespace RHTower.Sieve

open Complex

/-- The Littlewood width is antitone in the height: the strip prescribed at `K` sits inside the
strip prescribed at any smaller height. -/
theorem logLog_div_log_antitone {u v : ℝ} (hu : Real.exp 1 ≤ u) (huv : u ≤ v) :
    Real.log v / v ≤ Real.log u / u :=
  Real.log_div_self_antitoneOn hu (le_trans hu huv) huv

/-- `e ≤ log 16`. -/
theorem exp_one_le_log_sixteen : Real.exp 1 ≤ Real.log 16 := by
  have h16eq : Real.log ((16 : ℝ)) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]; norm_num
  have hlog2 := Real.log_two_gt_d9
  have hexp1 := Real.exp_one_lt_d9
  rw [h16eq]
  linarith

/-- Widening the constant weakens the strip condition. -/
theorem littlewood_depth_mono {c c' K x : ℝ} (hcc : c ≤ c')
    (hR : 0 ≤ Real.log (Real.log K) / Real.log K)
    (h : 1 - c * Real.log (Real.log K) / Real.log K ≤ x) :
    1 - c' * Real.log (Real.log K) / Real.log K ≤ x := by
  have hstep : c * (Real.log (Real.log K) / Real.log K)
      ≤ c' * (Real.log (Real.log K) / Real.log K) :=
    mul_le_mul_of_nonneg_right hcc hR
  rw [mul_div_assoc] at h ⊢
  linarith

/-- The Littlewood width never exceeds the constant itself. -/
theorem logLog_div_log_le_one {K : ℝ} (hK : 0 < Real.log K) :
    Real.log (Real.log K) / Real.log K ≤ 1 := by
  rw [div_le_one hK]
  linarith [Real.log_le_sub_one_of_pos hK]

/-- **The strip whose width grows with the height is zero-free.** -/
theorem exists_zeta_uniform_littlewood_depth_zero_free :
    ∃ c L₀ : ℝ, 0 < c ∧ Real.exp 1 ≤ L₀ ∧ ∀ (s : ℂ) (K : ℝ), L₀ ≤ Real.log K → |s.im| ≤ K →
      1 - c * Real.log (Real.log K) / Real.log K ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
  obtain ⟨c₁, hc₁0, hregion⟩ := exists_littlewood_zero_free_region_from_nine
  obtain ⟨δ, hδ0, hbox⟩ := exists_zero_free_box 16
  refine ⟨min c₁ δ / 2, Real.exp 1, by positivity, le_rfl, ?_⟩
  intro s K hL hKim hre hne
  have hLe : Real.exp 1 ≤ Real.log K := hL
  have hL1 : (1 : ℝ) ≤ Real.log K := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hL0 : (0 : ℝ) < Real.log K := by linarith
  have hLL1 : (1 : ℝ) ≤ Real.log (Real.log K) := by
    have h := Real.log_le_log (Real.exp_pos 1) hLe
    rwa [Real.log_exp] at h
  have hR0 : (0 : ℝ) ≤ Real.log (Real.log K) / Real.log K := by positivity
  rcases le_or_gt 1 s.re with hx1 | hx1
  · exact riemannZeta_ne_zero_of_one_le_re hx1
  rcases le_or_gt (16 : ℝ) |s.im| with hbig | hsmall
  · -- the Littlewood region, transferred from `K` down to the height of `s`
    have h9 : (9 : ℝ) ≤ |s.im| := by linarith
    have him0 : (0 : ℝ) < |s.im| := by linarith
    have hloge : Real.exp 1 ≤ Real.log |s.im| :=
      le_trans exp_one_le_log_sixteen (Real.log_le_log (by norm_num) hbig)
    have hlt : Real.log |s.im| ≤ Real.log K := Real.log_le_log him0 hKim
    have hanti : Real.log (Real.log K) / Real.log K
        ≤ Real.log (Real.log |s.im|) / Real.log |s.im| := logLog_div_log_antitone hloge hlt
    have hlogim0 : (0 : ℝ) < Real.log |s.im| := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have hLLim0 : (0 : ℝ) < Real.log (Real.log |s.im|) := by
      have h := Real.log_le_log (Real.exp_pos 1) hloge
      rw [Real.log_exp] at h
      linarith
    have hRim0 : (0 : ℝ) < Real.log (Real.log |s.im|) / Real.log |s.im| := by positivity
    have hcmin : min c₁ δ / 2 < c₁ := by
      have : min c₁ δ ≤ c₁ := min_le_left _ _
      linarith
    have hstrict : min c₁ δ / 2 * (Real.log (Real.log K) / Real.log K)
        < c₁ * (Real.log (Real.log |s.im|) / Real.log |s.im|) := by
      have h1 : min c₁ δ / 2 * (Real.log (Real.log K) / Real.log K)
          ≤ min c₁ δ / 2 * (Real.log (Real.log |s.im|) / Real.log |s.im|) :=
        mul_le_mul_of_nonneg_left hanti (by positivity)
      nlinarith [hcmin, hRim0]
    have hsplit : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I :=
      (Complex.re_add_im s).symm
    rw [hsplit]
    refine hregion s.re s.im h9 hx1.le ?_
    rw [mul_div_assoc] at hre ⊢
    linarith
  · -- the compact box
    have hδcmp : min c₁ δ / 2 * Real.log (Real.log K) / Real.log K ≤ δ := by
      have hle : min c₁ δ / 2 * (Real.log (Real.log K) / Real.log K) ≤ min c₁ δ / 2 * 1 :=
        mul_le_mul_of_nonneg_left (logLog_div_log_le_one hL0) (by positivity)
      have hmd : min c₁ δ ≤ δ := min_le_right _ _
      rw [mul_div_assoc]
      linarith
    exact hbox s (by linarith) hx1.le (le_of_lt hsmall) hne

set_option maxHeartbeats 1000000 in
/-- **The regular part on the strip whose width grows with the height.** -/
theorem exists_bound_zetaLogDerivReg_littlewood_depth :
    ∃ c C L₀ : ℝ, 0 < c ∧ 0 < C ∧ Real.exp 1 ≤ L₀ ∧
      ∀ (s : ℂ) (K : ℝ), L₀ ≤ Real.log K → |s.im| ≤ K →
        1 - c * Real.log (Real.log K) / Real.log K ≤ s.re → s.re ≤ 9 / 8 →
        ‖zetaLogDerivReg s‖ ≤ C * Real.log K ^ 2 / Real.log (Real.log K) := by
  obtain ⟨c₁, C₁, T₁, hc₁0, hC₁0, hT₁0, hbound⟩ := exists_logDeriv_zeta_bound_littlewood
  obtain ⟨δ, hδ0, M₀, hM₀0, hbox⟩ :=
    exists_bound_zetaLogDerivReg_box 2 (max T₁ 16) (by norm_num)
      (le_trans (by norm_num) (le_max_right T₁ 16))
  obtain ⟨c₂, L₁, hc₂0, hL₁, hzf⟩ := exists_zeta_uniform_littlewood_depth_zero_free
  refine ⟨min (min c₁ c₂) δ, C₁ + M₀ + 1, max (Real.exp 1) L₁,
    lt_min (lt_min hc₁0 hc₂0) hδ0, by linarith, le_max_left _ _, ?_⟩
  intro s K hL hKim hre hhi
  have hLe : Real.exp 1 ≤ Real.log K := le_trans (le_max_left _ _) hL
  have hL₁K : L₁ ≤ Real.log K := le_trans (le_max_right _ _) hL
  have hL1 : (1 : ℝ) ≤ Real.log K := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hL0 : (0 : ℝ) < Real.log K := by linarith
  have hLL1 : (1 : ℝ) ≤ Real.log (Real.log K) := by
    have h := Real.log_le_log (Real.exp_pos 1) hLe
    rwa [Real.log_exp] at h
  have hLL0 : (0 : ℝ) < Real.log (Real.log K) := by linarith
  have hR0 : (0 : ℝ) ≤ Real.log (Real.log K) / Real.log K := by positivity
  have hLsq : (1 : ℝ) ≤ Real.log K ^ 2 / Real.log (Real.log K) := by
    rw [le_div_iff₀ hLL0]
    nlinarith [hL1, hLL1, Real.log_le_sub_one_of_pos hL0]
  rcases le_or_gt (max T₁ 16) |s.im| with hbig | hsmall
  · have hT₁im : T₁ ≤ |s.im| := le_trans (le_max_left _ _) hbig
    have habs16 : (16 : ℝ) ≤ |s.im| := le_trans (le_max_right _ _) hbig
    have habs4 : (4 : ℝ) ≤ |s.im| := by linarith
    have him0 : (0 : ℝ) < |s.im| := by linarith
    have hloge : Real.exp 1 ≤ Real.log |s.im| :=
      le_trans exp_one_le_log_sixteen (Real.log_le_log (by norm_num) habs16)
    have hlogim1 : (1 : ℝ) ≤ Real.log |s.im| := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have hloglog1 : (1 : ℝ) ≤ Real.log (Real.log |s.im|) := by
      have h := Real.log_le_log (Real.exp_pos 1) hloge
      rwa [Real.log_exp] at h
    have hlt : Real.log |s.im| ≤ Real.log K := Real.log_le_log him0 hKim
    have hanti : Real.log (Real.log K) / Real.log K
        ≤ Real.log (Real.log |s.im|) / Real.log |s.im| := logLog_div_log_antitone hloge hlt
    -- the strip condition at the height of `s`
    have hwide : 1 - c₁ * Real.log (Real.log |s.im|) / Real.log |s.im| ≤ s.re := by
      have hcle : min (min c₁ c₂) δ ≤ c₁ := le_trans (min_le_left _ _) (min_le_left _ _)
      have h1 : min (min c₁ c₂) δ * (Real.log (Real.log K) / Real.log K)
          ≤ c₁ * (Real.log (Real.log |s.im|) / Real.log |s.im|) := by
        have ha : min (min c₁ c₂) δ * (Real.log (Real.log K) / Real.log K)
            ≤ min (min c₁ c₂) δ * (Real.log (Real.log |s.im|) / Real.log |s.im|) :=
          mul_le_mul_of_nonneg_left hanti
            (le_of_lt (lt_min (lt_min hc₁0 hc₂0) hδ0))
        have hb : min (min c₁ c₂) δ * (Real.log (Real.log |s.im|) / Real.log |s.im|)
            ≤ c₁ * (Real.log (Real.log |s.im|) / Real.log |s.im|) :=
          mul_le_mul_of_nonneg_right hcle (by positivity)
        linarith
      rw [mul_div_assoc] at hre ⊢
      linarith
    have hsplit : s = ((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * Complex.I :=
      (Complex.re_add_im s).symm
    have hres : ‖logDeriv riemannZeta s‖
        ≤ C₁ * Real.log |s.im| ^ 2 / Real.log (Real.log |s.im|) := by
      have h := hbound s.re s.im hT₁im hwide hhi
      rwa [← hsplit] at h
    have hs1 : s ≠ 1 := by
      intro h
      rw [h] at habs4
      simp only [Complex.one_im, abs_zero] at habs4
      linarith
    have hzfs : riemannZeta s ≠ 0 := by
      refine hzf s K hL₁K hKim ?_ hs1
      have hcle : min (min c₁ c₂) δ ≤ c₂ := le_trans (min_le_left _ _) (min_le_right _ _)
      exact littlewood_depth_mono hcle hR0 hre
    have hzu : zetaResidueUnit s ≠ 0 := (zetaResidueUnit_ne_zero_iff hs1).2 hzfs
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
    have hmono : Real.log |s.im| ^ 2 / Real.log (Real.log |s.im|)
        ≤ Real.log K ^ 2 / Real.log (Real.log K) :=
      sq_div_log_mono hloglog1 (by linarith) hlt
    have hCmono : C₁ * Real.log |s.im| ^ 2 / Real.log (Real.log |s.im|)
        ≤ C₁ * (Real.log K ^ 2 / Real.log (Real.log K)) := by
      have hstep := mul_le_mul_of_nonneg_left hmono hC₁0.le
      have heq : C₁ * Real.log |s.im| ^ 2 / Real.log (Real.log |s.im|)
          = C₁ * (Real.log |s.im| ^ 2 / Real.log (Real.log |s.im|)) := by ring
      linarith [hstep, heq.le, heq.ge]
    have hfinal : ‖zetaLogDerivReg s‖
        ≤ C₁ * (Real.log K ^ 2 / Real.log (Real.log K)) + 1 / 4 := by
      linarith [hreg, hres, hpole, hCmono]
    have hexp : (C₁ + M₀ + 1) * Real.log K ^ 2 / Real.log (Real.log K)
        = C₁ * (Real.log K ^ 2 / Real.log (Real.log K))
          + (M₀ + 1) * (Real.log K ^ 2 / Real.log (Real.log K)) := by
      field_simp
      ring
    nlinarith [hfinal, hexp.le, hexp.ge, hLsq, hM₀0]
  · have hδcmp : min (min c₁ c₂) δ * Real.log (Real.log K) / Real.log K ≤ δ := by
      have hle : min (min c₁ c₂) δ * (Real.log (Real.log K) / Real.log K)
          ≤ min (min c₁ c₂) δ * 1 :=
        mul_le_mul_of_nonneg_left (logLog_div_log_le_one hL0)
          (le_of_lt (lt_min (lt_min hc₁0 hc₂0) hδ0))
      have hmd : min (min c₁ c₂) δ ≤ δ := min_le_right _ _
      rw [mul_div_assoc]
      linarith
    have hres := hbox s (by linarith) (by linarith) (le_of_lt hsmall)
    have hexp : (C₁ + M₀ + 1) * Real.log K ^ 2 / Real.log (Real.log K)
        = (C₁ + M₀ + 1) * (Real.log K ^ 2 / Real.log (Real.log K)) := by ring
    nlinarith [hres, hLsq, hC₁0, hM₀0, hexp.le, hexp.ge]

end RHTower.Sieve
