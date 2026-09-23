import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegionBound
import GaloisForLFunctions.RHTower.Sieve.ZetaLittlewoodRegionAbs
import GaloisForLFunctions.RHTower.Sieve.DirichletWideOrder

/-!
# `ζ'/ζ` inside the Littlewood region

`exists_logDeriv_zeta_bound_of_region` bounds `ζ'/ζ` by `C log²|γ|` on a strip of width
`≍ 1/log|γ|`.  The square is a product of two logarithms: one is the number of zeros near the
centre, `≪ log|γ|`, the other is the reciprocal distance to each of them, `≪ log|γ|` precisely
because the region is `1/log|γ|` wide.

Only the second factor sees the region.  A region of width `c·log log|γ|/log|γ|` therefore improves
the bound by exactly `log log|γ|`:

```text
‖ζ'/ζ(σ + iγ)‖  ≤  C · log²|γ| / log log|γ|      on   1 − c·log log|γ|/(8 log|γ|) ≤ σ ≤ 9/8 .
```

The zero count and the Landau remainder are unchanged.
-/

namespace RHTower.Sieve

open Complex

/-- The Littlewood width. -/
noncomputable def littlewoodWidth (c γ : ℝ) : ℝ :=
  c * Real.log (Real.log |γ|) / Real.log |γ|

/-- `exp 2 ≤ 16`. -/
theorem exp_two_le_sixteen : Real.exp 2 ≤ 16 := by
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have h := Real.exp_one_lt_d9
  nlinarith [Real.exp_pos 1, he2]

/-- At height `exp 16` the iterated logarithm is already at least `2`. -/
theorem two_le_logLog_abs {γ : ℝ} (hγ : Real.exp 16 ≤ |γ|) :
    (2 : ℝ) ≤ Real.log (Real.log |γ|) := by
  have hexp16 : (16 : ℝ) ≤ Real.log |γ| := by
    have h := Real.log_le_log (Real.exp_pos 16) hγ
    rwa [Real.log_exp] at h
  have h1 : Real.log (Real.exp 2) ≤ Real.log (Real.log |γ|) := by
    refine Real.log_le_log (Real.exp_pos 2) ?_
    linarith [exp_two_le_sixteen]
  rwa [Real.log_exp] at h1

/-- **Every zero near the centre lies left of the Littlewood region.** -/
theorem wide_zero_re_le_littlewood {c T γ : ℝ} (hc0 : 0 < c)
    (hregion : ∀ β γ' : ℝ, T ≤ |γ'| → β ≤ 1 →
      1 - c * Real.log (Real.log |γ'|) / Real.log |γ'| < β →
      riemannZeta ((β : ℂ) + (γ' : ℂ) * Complex.I) ≠ 0)
    (hγ : Real.exp 16 ≤ |γ|) (hγT : T + 1 ≤ |γ|) {ρ : ℂ}
    (hd : ‖ρ - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 21 / 40)
    (hz : riemannZeta ρ = 0) :
    ρ.re ≤ 1 - littlewoodWidth c γ / 4 := by
  have hexp16 : (16 : ℝ) ≤ Real.log |γ| := by
    have h := Real.log_le_log (Real.exp_pos 16) hγ
    rwa [Real.log_exp] at h
  have hγ4 : (4 : ℝ) ≤ |γ| := by
    have h1 : (17 : ℝ) ≤ Real.exp 16 := by
      have := Real.add_one_le_exp (16 : ℝ); linarith
    linarith
  have hγ0 : (0 : ℝ) < |γ| := by linarith
  have hL0 : (0 : ℝ) < Real.log |γ| := by linarith
  have hLL := two_le_logLog_abs hγ
  have hLL0 : (0 : ℝ) < Real.log (Real.log |γ|) := by linarith
  have hrere : ρ.re ≤ 1 := by
    by_contra hcon
    exact riemannZeta_ne_zero_of_one_le_re (le_of_lt (not_le.mp hcon)) hz
  have him : |ρ.im - γ| ≤ 21 / 40 := by
    have h1 : |(ρ - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).im|
        ≤ ‖ρ - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ := Complex.abs_im_le_norm _
    have h2 : (ρ - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).im = ρ.im - γ := by
      rw [Complex.sub_im, wide_centre_im]
    rw [h2] at h1
    linarith
  have habs := abs_le.mp him
  have hlow : T ≤ |ρ.im| := by
    rcases abs_cases γ with ⟨hg, _⟩ | ⟨hg, _⟩ <;>
      rcases abs_cases ρ.im with ⟨hi, _⟩ | ⟨hi, _⟩ <;> rw [hi] <;>
        linarith [habs.1, habs.2, hγT]
  have hhalf : |γ| / 2 ≤ |ρ.im| := by
    rcases abs_cases γ with ⟨hg, _⟩ | ⟨hg, _⟩ <;>
      rcases abs_cases ρ.im with ⟨hi, _⟩ | ⟨hi, _⟩ <;> rw [hi] <;>
        linarith [habs.1, habs.2, hγ4]
  have hup : |ρ.im| ≤ 2 * |γ| := by
    rcases abs_cases γ with ⟨hg, _⟩ | ⟨hg, _⟩ <;>
      rcases abs_cases ρ.im with ⟨hi, _⟩ | ⟨hi, _⟩ <;> rw [hi] <;>
        linarith [habs.1, habs.2, hγ4]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hlogρup : Real.log |ρ.im| ≤ 2 * Real.log |γ| := by
    have h1 : Real.log |ρ.im| ≤ Real.log (2 * |γ|) := Real.log_le_log (by linarith) hup
    rw [Real.log_mul (by norm_num) (ne_of_gt hγ0)] at h1
    linarith
  have hlogρlo : Real.log |γ| / 2 ≤ Real.log |ρ.im| := by
    have h1 : Real.log (|γ| / 2) ≤ Real.log |ρ.im| := Real.log_le_log (by positivity) hhalf
    have h2 : Real.log (|γ| / 2) = Real.log |γ| - Real.log 2 :=
      Real.log_div (ne_of_gt hγ0) (by norm_num)
    rw [h2] at h1
    linarith
  have hlogρ0 : (0 : ℝ) < Real.log |ρ.im| := by linarith
  have hLLρ : Real.log (Real.log |γ|) / 2 ≤ Real.log (Real.log |ρ.im|) := by
    have h1 : Real.log (Real.log |γ| / 2) ≤ Real.log (Real.log |ρ.im|) :=
      Real.log_le_log (by positivity) hlogρlo
    have h2 : Real.log (Real.log |γ| / 2) = Real.log (Real.log |γ|) - Real.log 2 :=
      Real.log_div (ne_of_gt hL0) (by norm_num)
    rw [h2] at h1
    linarith
  have hwid : littlewoodWidth c γ / 4
      ≤ c * Real.log (Real.log |ρ.im|) / Real.log |ρ.im| := by
    rw [littlewoodWidth, div_div, div_le_div_iff₀ (by positivity) hlogρ0]
    have hA : c * Real.log (Real.log |γ|) * Real.log |ρ.im|
        ≤ c * Real.log (Real.log |γ|) * (2 * Real.log |γ|) :=
      mul_le_mul_of_nonneg_left hlogρup (by positivity)
    have hB : 4 * c * Real.log |γ| * (Real.log (Real.log |γ|) / 2)
        ≤ 4 * c * Real.log |γ| * Real.log (Real.log |ρ.im|) :=
      mul_le_mul_of_nonneg_left hLLρ (by positivity)
    nlinarith [hA, hB]
  by_contra hcon
  refine hregion ρ.re ρ.im hlow hrere ?_ (by rw [Complex.re_add_im]; exact hz)
  linarith [not_le.mp hcon, hwid]

set_option maxHeartbeats 1000000 in
/-- **`ζ'/ζ` is `O(log²|γ| / log log|γ|)` inside a Littlewood region.** -/
theorem exists_logDeriv_zeta_bound_of_littlewood {c T₀ : ℝ} (hc0 : 0 < c) (hcle : c ≤ 1 / 10)
    (hregion : ∀ β γ' : ℝ, T₀ ≤ |γ'| → β ≤ 1 →
      1 - c * Real.log (Real.log |γ'|) / Real.log |γ'| < β →
      riemannZeta ((β : ℂ) + (γ' : ℂ) * Complex.I) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ σ γ : ℝ, max (Real.exp 16) (T₀ + 1) ≤ |γ| →
        1 - littlewoodWidth c γ / 8 ≤ σ → σ ≤ 9 / 8 →
        ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
          ≤ C * Real.log |γ| ^ (2 : ℕ) / Real.log (Real.log |γ|) := by
  obtain ⟨E, hE0, hcount⟩ := exists_wide_zero_count
  refine ⟨320 / 21 * wideD + 8 * E / c, ?_, ?_⟩
  · have h1 : (0 : ℝ) < 320 / 21 * wideD := by nlinarith [wideD_pos]
    have h2 : (0 : ℝ) < 8 * E / c := div_pos (by linarith) hc0
    linarith
  intro σ γ hγT hσlow hσ98
  have hγexp : Real.exp 16 ≤ |γ| := le_trans (le_max_left _ _) hγT
  have hγT₀ : T₀ + 1 ≤ |γ| := le_trans (le_max_right _ _) hγT
  have hexp16 : (16 : ℝ) ≤ Real.log |γ| := by
    have h := Real.log_le_log (Real.exp_pos 16) hγexp
    rwa [Real.log_exp] at h
  have hγ4 : (4 : ℝ) ≤ |γ| := by
    have h1 : (17 : ℝ) ≤ Real.exp 16 := by
      have := Real.add_one_le_exp (16 : ℝ); linarith
    linarith
  have hL0 : (0 : ℝ) < Real.log |γ| := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log |γ| := by linarith
  have hLL := two_le_logLog_abs hγexp
  have hLL0 : (0 : ℝ) < Real.log (Real.log |γ|) := by linarith
  -- the width, and its smallness
  set W : ℝ := littlewoodWidth c γ with hWdef
  have hWval : W * Real.log |γ| = c * Real.log (Real.log |γ|) := by
    rw [hWdef, littlewoodWidth]
    field_simp
  have hW0 : (0 : ℝ) < W := by
    rw [hWdef, littlewoodWidth]; positivity
  have hratio : Real.log (Real.log |γ|) ≤ Real.log |γ| / 2 := by
    have hsqrt := wide_log_le_two_sqrt (x := Real.log |γ|) hL0
    have hs : Real.sqrt (Real.log |γ|) * Real.sqrt (Real.log |γ|) = Real.log |γ| :=
      Real.mul_self_sqrt hL0.le
    have hs4 : (4 : ℝ) ≤ Real.sqrt (Real.log |γ|) := by
      nlinarith [hs, Real.sqrt_nonneg (Real.log |γ|), hexp16]
    nlinarith [hsqrt, hs, hs4, Real.sqrt_nonneg (Real.log |γ|)]
  have hWsmall : W ≤ 1 / 20 := by
    rw [hWdef, littlewoodWidth, div_le_div_iff₀ hL0 (by norm_num)]
    nlinarith [hratio, hc0, hL0, hcle]
  have hσ159 : (159 : ℝ) / 160 ≤ σ := by linarith [hσlow, hWsmall]
  -- the point is not a zero
  have hzne : riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
    rcases le_or_gt σ 1 with hle | hgt
    · refine hregion σ γ (by linarith) hle ?_
      have hWeq : c * Real.log (Real.log |γ|) / Real.log |γ| = W := by
        rw [hWdef, littlewoodWidth]
      rw [hWeq]
      linarith [hσlow, hW0]
    · exact riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  -- Landau's data on the wide disc
  obtain ⟨Z, m, hZdist, hZzero, hZmem, hZmult, hZkey⟩ := zeta_landau_wide hγ4
  have hzc : ‖((σ : ℂ) + (γ : ℂ) * Complex.I)
      - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 21 / 160 := by
    have hdiff : ((σ : ℂ) + (γ : ℂ) * Complex.I) - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)
        = (((σ - 9 / 8 : ℝ)) : ℂ) := by push_cast; ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hkeyz := hZkey ((σ : ℂ) + (γ : ℂ) * Complex.I) hzc hzne
  have hkeyc := hZkey (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)
    (by rw [sub_self, norm_zero]; norm_num) (zeta_wide_centre_ne_zero γ)
  have hcnt := hcount γ hγ4 Z m hZdist hZzero hkeyc
  -- distance to each retained zero
  have hdistz : ∀ ρ ∈ Z, W / 8 ≤ ‖((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ‖ := by
    intro ρ hρ
    have hleft := wide_zero_re_le_littlewood hc0 hregion hγexp hγT₀ (hZdist ρ hρ) (hZzero ρ hρ)
    rw [← hWdef] at hleft
    have h1 : |(((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ).re|
        ≤ ‖((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ‖ := Complex.abs_re_le_norm _
    have h2 : (((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ).re = σ - ρ.re := by
      rw [Complex.sub_re]; simp
    rw [h2] at h1
    have h3 : W / 8 ≤ σ - ρ.re := by linarith [hleft, hσlow]
    linarith [le_abs_self (σ - ρ.re)]
  -- the retained sum
  have hsumz : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ)‖
      ≤ (∑ ρ ∈ Z, (m ρ : ℝ)) * (8 / W) := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    rw [norm_div, Complex.norm_natCast]
    have hd := hdistz ρ hρ
    have hcpos : (0 : ℝ) < W / 8 := by positivity
    have hdpos : (0 : ℝ) < ‖((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ‖ := by linarith
    rw [div_le_iff₀ hdpos]
    have hm0 : (0 : ℝ) ≤ (m ρ : ℝ) := Nat.cast_nonneg _
    have hinv : (1 : ℝ) ≤ 8 / W * ‖((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ‖ := by
      have hfac : (0 : ℝ) < 8 / W := by positivity
      have hmul := mul_le_mul_of_nonneg_left hd hfac.le
      have hone : 8 / W * (W / 8) = 1 := by field_simp
      rw [hone] at hmul
      exact hmul
    nlinarith [hm0, hinv]
  -- assembling
  have hsplit : ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
      ≤ ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ∑ ρ ∈ Z, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ)‖
        + ‖∑ ρ ∈ Z, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ)‖ := by
    have h := norm_add_le
      (logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)
        - ∑ ρ ∈ Z, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ))
      (∑ ρ ∈ Z, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ))
    simpa using h
  have hprod : (∑ ρ ∈ Z, (m ρ : ℝ)) * (8 / W)
      ≤ 8 * E / c * (Real.log |γ| ^ (2 : ℕ) / Real.log (Real.log |γ|)) := by
    have hfac : (0 : ℝ) ≤ 8 / W := by positivity
    have hstep := mul_le_mul_of_nonneg_right hcnt hfac
    have heq : (E * Real.log |γ|) * (8 / W)
        = 8 * E / c * (Real.log |γ| ^ (2 : ℕ) / Real.log (Real.log |γ|)) := by
      rw [hWdef, littlewoodWidth]
      field_simp
    linarith [hstep, heq.le, heq.ge]
  have hlin : 320 / 21 * wideD * Real.log |γ|
      ≤ 320 / 21 * wideD * (Real.log |γ| ^ (2 : ℕ) / Real.log (Real.log |γ|)) := by
    have hge : Real.log |γ| ≤ Real.log |γ| ^ (2 : ℕ) / Real.log (Real.log |γ|) := by
      rw [le_div_iff₀ hLL0]
      nlinarith [hratio, hL0]
    nlinarith [hge, wideD_pos]
  have hfinal : ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
      ≤ 320 / 21 * wideD * (Real.log |γ| ^ (2 : ℕ) / Real.log (Real.log |γ|))
        + 8 * E / c * (Real.log |γ| ^ (2 : ℕ) / Real.log (Real.log |γ|)) := by
    linarith [hsplit, hkeyz, hsumz, hlin, hprod]
  have hcollect : 320 / 21 * wideD * (Real.log |γ| ^ (2 : ℕ) / Real.log (Real.log |γ|))
      + 8 * E / c * (Real.log |γ| ^ (2 : ℕ) / Real.log (Real.log |γ|))
      = (320 / 21 * wideD + 8 * E / c) * Real.log |γ| ^ (2 : ℕ) / Real.log (Real.log |γ|) := by
    field_simp
  linarith [hfinal, hcollect.le, hcollect.ge]

/-- **`ζ'/ζ` is `O(log²|γ| / log log|γ|)`.**  The Littlewood region instantiated. -/
theorem exists_logDeriv_zeta_bound_littlewood :
    ∃ c C T : ℝ, 0 < c ∧ 0 < C ∧ 0 < T ∧
      ∀ σ γ : ℝ, T ≤ |γ| →
        1 - c * Real.log (Real.log |γ|) / Real.log |γ| ≤ σ → σ ≤ 9 / 8 →
        ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
          ≤ C * Real.log |γ| ^ (2 : ℕ) / Real.log (Real.log |γ|) := by
  obtain ⟨c₀, T₀, hc₀0, hT₀, hregion⟩ := exists_littlewood_zero_free_region_abs
  set c : ℝ := min c₀ (1 / 10) with hcdef
  have hc0 : 0 < c := lt_min hc₀0 (by norm_num)
  have hcle : c ≤ 1 / 10 := min_le_right _ _
  have hcc₀ : c ≤ c₀ := min_le_left _ _
  have hregion' : ∀ β γ' : ℝ, T₀ ≤ |γ'| → β ≤ 1 →
      1 - c * Real.log (Real.log |γ'|) / Real.log |γ'| < β →
      riemannZeta ((β : ℂ) + (γ' : ℂ) * Complex.I) ≠ 0 := by
    intro β γ' hγ' hβ1 hβ
    refine hregion β γ' hγ' hβ1 ?_
    have hL0 : (0 : ℝ) < Real.log |γ'| := by
      have h3 : (3 : ℝ) ≤ |γ'| := le_trans hT₀ hγ'
      have h1 : Real.log 3 ≤ Real.log |γ'| := Real.log_le_log (by norm_num) h3
      have h2 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
      linarith
    have hLL : (0 : ℝ) ≤ Real.log (Real.log |γ'|) := by
      refine Real.log_nonneg ?_
      have h3 : (3 : ℝ) ≤ |γ'| := le_trans hT₀ hγ'
      have hexp : Real.exp 1 ≤ |γ'| := by
        have := Real.exp_one_lt_d9; linarith
      have h := Real.log_le_log (Real.exp_pos 1) hexp
      rwa [Real.log_exp] at h
    have hmono : c * Real.log (Real.log |γ'|) / Real.log |γ'|
        ≤ c₀ * Real.log (Real.log |γ'|) / Real.log |γ'| := by
      refine div_le_div_of_nonneg_right ?_ hL0.le
      exact mul_le_mul_of_nonneg_right hcc₀ hLL
    linarith
  obtain ⟨C, hC0, hb⟩ := exists_logDeriv_zeta_bound_of_littlewood hc0 hcle hregion'
  refine ⟨c / 8, C, max (Real.exp 16) (T₀ + 1), by positivity, hC0, ?_, ?_⟩
  · have : (0 : ℝ) < Real.exp 16 := Real.exp_pos 16
    exact lt_of_lt_of_le this (le_max_left _ _)
  intro σ γ hγ hσlow hσ98
  refine hb σ γ hγ ?_ hσ98
  rw [littlewoodWidth]
  have heq : c * Real.log (Real.log |γ|) / Real.log |γ| / 8
      = c / 8 * Real.log (Real.log |γ|) / Real.log |γ| := by ring
  rw [heq]
  exact hσlow

end RHTower.Sieve
