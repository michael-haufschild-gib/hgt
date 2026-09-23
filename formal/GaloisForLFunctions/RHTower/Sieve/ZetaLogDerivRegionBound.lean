import GaloisForLFunctions.RHTower.Sieve.ZetaZeroCountWide
import GaloisForLFunctions.RHTower.Sieve.ZeroFreeRegionKappaOne
import GaloisForLFunctions.RHTower.Sieve.ZeroFreeRegionFromNine

/-!
# `ζ'/ζ` inside the zero-free region

At a point `z = σ + iγ` of the zero-free region, Landau's inequality on the wide disc gives

```text
‖ζ'/ζ(z)‖ ≤ (320/21)·wideD·log|γ| + ∑_ρ m_ρ / |z - ρ|.
```

Every retained zero lies left of the region, so `|z - ρ| ≥ c/(4 log|γ|)`, and the retained zeros
number `O(log|γ|)`.  The sum is therefore `O(log²|γ|)`, which is the classical
`ζ'/ζ = O(log² t)` — now with the exponent-one width, whereas the corpus's mean-value route
reached only width `log^{-9}`.
-/

namespace RHTower.Sieve

open Complex

/-- **Every zero near the centre lies left of the region.** -/
theorem wide_zero_re_le {c T γ : ℝ} (hc0 : 0 < c)
    (hregion : ∀ β γ' : ℝ, T ≤ |γ'| → β ≤ 1 → 1 - c / Real.log |γ'| < β →
      riemannZeta ((β : ℂ) + (γ' : ℂ) * Complex.I) ≠ 0)
    (hγ : 4 ≤ |γ|) (hγT : T + 1 ≤ |γ|) {ρ : ℂ}
    (hd : ‖ρ - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 21 / 40)
    (hz : riemannZeta ρ = 0) :
    ρ.re ≤ 1 - c / (2 * Real.log |γ|) := by
  have hL1 := one_le_log_abs hγ
  have hγ0 : (0 : ℝ) < |γ| := by linarith
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
  have hbig : (3 : ℝ) ≤ |ρ.im| := by
    rcases abs_cases γ with ⟨hg, _⟩ | ⟨hg, _⟩ <;>
      rcases abs_cases ρ.im with ⟨hi, _⟩ | ⟨hi, _⟩ <;> rw [hi] <;>
        linarith [habs.1, habs.2, hγ]
  have hup : |ρ.im| ≤ 2 * |γ| := by
    rcases abs_cases γ with ⟨hg, _⟩ | ⟨hg, _⟩ <;>
      rcases abs_cases ρ.im with ⟨hi, _⟩ | ⟨hi, _⟩ <;> rw [hi] <;>
        linarith [habs.1, habs.2, hγ]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlogρ : Real.log |ρ.im| ≤ 2 * Real.log |γ| := by
    have h1 : Real.log |ρ.im| ≤ Real.log (2 * |γ|) :=
      Real.log_le_log (by linarith) hup
    rw [Real.log_mul (by norm_num) (ne_of_gt hγ0)] at h1
    linarith
  have hlogρpos : (0 : ℝ) < Real.log |ρ.im| := Real.log_pos (by linarith)
  by_contra hcon
  have hstep : c / (2 * Real.log |γ|) ≤ c / Real.log |ρ.im| :=
    div_le_div_of_nonneg_left hc0.le hlogρpos hlogρ
  have hgt : 1 - c / Real.log |ρ.im| < ρ.re := by linarith [not_le.mp hcon]
  refine hregion ρ.re ρ.im hlow hrere hgt ?_
  rw [Complex.re_add_im]
  exact hz

/-- **`ζ'/ζ` is `O(log²|γ|)` inside a zero-free region**, for any region of exponent one. -/
theorem exists_logDeriv_zeta_bound_of_region {c T₀ : ℝ} (hc0 : 0 < c)
    (hregion : ∀ β γ' : ℝ, T₀ ≤ |γ'| → β ≤ 1 → 1 - c / Real.log |γ'| < β →
      riemannZeta ((β : ℂ) + (γ' : ℂ) * Complex.I) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ σ γ : ℝ, max 4 (T₀ + 1) ≤ |γ| →
        1 - min (c / 4) (1 / 160) / Real.log |γ| ≤ σ → σ ≤ 9 / 8 →
        ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
          ≤ C * Real.log |γ| ^ (2 : ℕ) := by
  obtain ⟨E, hE0, hcount⟩ := exists_wide_zero_count
  have hCpos : (0 : ℝ) < 320 / 21 * wideD + 4 * E / c := by
    have h1 : (0 : ℝ) < 320 / 21 * wideD := by nlinarith [wideD_pos]
    have h2 : (0 : ℝ) < 4 * E / c := div_pos (by linarith) hc0
    linarith
  refine ⟨320 / 21 * wideD + 4 * E / c, hCpos, ?_⟩
  intro σ γ hγT hσlow hσ98
  have hγ4 : (4 : ℝ) ≤ |γ| := le_trans (le_max_left _ _) hγT
  have hγT₀ : T₀ + 1 ≤ |γ| := le_trans (le_max_right _ _) hγT
  have hL1 := one_le_log_abs hγ4
  have hL0 : (0 : ℝ) < Real.log |γ| := by linarith
  have hmin1 : min (c / 4) (1 / 160) ≤ c / 4 := min_le_left _ _
  have hmin2 : min (c / 4) (1 / 160) ≤ 1 / 160 := min_le_right _ _
  have hminpos : (0 : ℝ) < min (c / 4) (1 / 160) := lt_min (by linarith) (by norm_num)
  have hquot : min (c / 4) (1 / 160) / Real.log |γ| ≤ min (c / 4) (1 / 160) := by
    rw [div_le_iff₀ hL0]
    nlinarith [hminpos, hL1]
  have hσ159 : (159 : ℝ) / 160 ≤ σ := by linarith [hσlow, hquot, hmin2]
  have hσquarter : 1 - c / 4 / Real.log |γ| ≤ σ := by
    have hstep : min (c / 4) (1 / 160) / Real.log |γ| ≤ c / 4 / Real.log |γ| := by
      rw [div_le_div_iff₀ hL0 hL0]
      nlinarith [hmin1, hL0]
    linarith [hσlow]
  -- the point is in the region, hence not a zero
  have hzne : riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
    rcases le_or_gt σ 1 with hle | hgt
    · refine hregion σ γ (by linarith) hle ?_
      have hlt : c / 4 / Real.log |γ| < c / Real.log |γ| := by
        rw [div_lt_div_iff₀ hL0 hL0]
        nlinarith [hc0, hL0]
      linarith [hσquarter]
    · refine riemannZeta_ne_zero_of_one_le_re ?_
      simp
      linarith
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
  -- distance from `z` to each retained zero
  have hdistz : ∀ ρ ∈ Z, c / (4 * Real.log |γ|)
      ≤ ‖((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ‖ := by
    intro ρ hρ
    have hleft := wide_zero_re_le hc0 hregion hγ4 hγT₀ (hZdist ρ hρ) (hZzero ρ hρ)
    have h1 : |(((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ).re|
        ≤ ‖((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ‖ := Complex.abs_re_le_norm _
    have h2 : (((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ).re = σ - ρ.re := by
      rw [Complex.sub_re]
      simp
    rw [h2] at h1
    have hhalf : c / (4 * Real.log |γ|) + c / (4 * Real.log |γ|)
        = c / (2 * Real.log |γ|) := by
      field_simp
      ring
    have hcq : c / 4 / Real.log |γ| = c / (4 * Real.log |γ|) := by ring
    have h3 : c / (4 * Real.log |γ|) ≤ σ - ρ.re := by
      linarith [hleft, hσquarter, hhalf, hcq]
    linarith [le_abs_self (σ - ρ.re)]
  -- the retained sum
  have hsumz : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ)‖
      ≤ (∑ ρ ∈ Z, (m ρ : ℝ)) * (4 * Real.log |γ| / c) := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    rw [norm_div, Complex.norm_natCast]
    have hd := hdistz ρ hρ
    have hcpos : (0 : ℝ) < c / (4 * Real.log |γ|) := by positivity
    have hdpos : (0 : ℝ) < ‖((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ‖ := by linarith
    rw [div_le_iff₀ hdpos]
    have hm0 : (0 : ℝ) ≤ (m ρ : ℝ) := Nat.cast_nonneg _
    have hinv : (1 : ℝ) ≤ 4 * Real.log |γ| / c * ‖((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ‖ := by
      have hfac : (0 : ℝ) < 4 * Real.log |γ| / c := by positivity
      have hmul := mul_le_mul_of_nonneg_left hd hfac.le
      have hone : 4 * Real.log |γ| / c * (c / (4 * Real.log |γ|)) = 1 := by
        field_simp
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
  have hprod : (∑ ρ ∈ Z, (m ρ : ℝ)) * (4 * Real.log |γ| / c)
      ≤ 4 * E / c * Real.log |γ| ^ (2 : ℕ) := by
    have hfac : (0 : ℝ) ≤ 4 * Real.log |γ| / c := by positivity
    have hstep := mul_le_mul_of_nonneg_right hcnt hfac
    calc (∑ ρ ∈ Z, (m ρ : ℝ)) * (4 * Real.log |γ| / c)
        ≤ (E * Real.log |γ|) * (4 * Real.log |γ| / c) := hstep
      _ = 4 * E / c * Real.log |γ| ^ (2 : ℕ) := by field_simp
  have hlin : 320 / 21 * wideD * Real.log |γ|
      ≤ 320 / 21 * wideD * Real.log |γ| ^ (2 : ℕ) := by
    have hsq : (0 : ℝ) ≤ Real.log |γ| ^ (2 : ℕ) - Real.log |γ| := by nlinarith [hL1]
    nlinarith [mul_nonneg (le_of_lt wideD_pos) hsq]
  calc ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
      ≤ ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ∑ ρ ∈ Z, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ)‖
        + ‖∑ ρ ∈ Z, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ)‖ := hsplit
    _ ≤ 320 / 21 * wideD * Real.log |γ|
          + (∑ ρ ∈ Z, (m ρ : ℝ)) * (4 * Real.log |γ| / c) := by
        linarith [hkeyz, hsumz]
    _ ≤ 320 / 21 * wideD * Real.log |γ| ^ (2 : ℕ) + 4 * E / c * Real.log |γ| ^ (2 : ℕ) := by
        linarith [hlin, hprod]
    _ = (320 / 21 * wideD + 4 * E / c) * Real.log |γ| ^ (2 : ℕ) := by ring

/-- **`ζ'/ζ` is `O(log²|γ|)` inside the zero-free region.** -/
theorem exists_logDeriv_zeta_bound :
    ∃ c' C T : ℝ, 0 < c' ∧ 0 < C ∧ 4 ≤ T ∧
      ∀ σ γ : ℝ, T ≤ |γ| → 1 - c' / Real.log |γ| ≤ σ → σ ≤ 9 / 8 →
        ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
          ≤ C * Real.log |γ| ^ (2 : ℕ) := by
  obtain ⟨c, T₀, hc0, hT₀, hregion⟩ := exists_zero_free_region
  obtain ⟨C, hC0, hb⟩ := exists_logDeriv_zeta_bound_of_region hc0 hregion
  exact ⟨min (c / 4) (1 / 160), C, max 4 (T₀ + 1),
    lt_min (by linarith) (by norm_num), hC0, le_max_left _ _, hb⟩

/-- **The same bound with a threshold of `10`.**  Feeding the region that is valid from height nine
replaces the asymptotic threshold by an absolute one; only the constant `C` degrades. -/
theorem exists_logDeriv_zeta_bound_from_ten :
    ∃ c' C : ℝ, 0 < c' ∧ 0 < C ∧
      ∀ σ γ : ℝ, (10 : ℝ) ≤ |γ| → 1 - c' / Real.log |γ| ≤ σ → σ ≤ 9 / 8 →
        ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
          ≤ C * Real.log |γ| ^ (2 : ℕ) := by
  obtain ⟨c, hc0, hregion⟩ := exists_zero_free_region_from_nine
  obtain ⟨C, hC0, hb⟩ := exists_logDeriv_zeta_bound_of_region (T₀ := 9) hc0 hregion
  refine ⟨min (c / 4) (1 / 160), C, lt_min (by linarith) (by norm_num), hC0,
    fun σ γ hγ => hb σ γ ?_⟩
  rw [show max (4 : ℝ) (9 + 1) = 10 by norm_num]
  exact hγ

/-- **The bound with the strip width exposed.**  Instantiating the explicit region
(`1/(10000 log|γ|)`) gives the width `1/(40000 log|γ|)`. -/
theorem exists_logDeriv_zeta_bound_explicit :
    ∃ C T : ℝ, 0 < C ∧ 4 ≤ T ∧
      ∀ σ γ : ℝ, T ≤ |γ| → 1 - 1 / 40000 / Real.log |γ| ≤ σ → σ ≤ 9 / 8 →
        ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
          ≤ C * Real.log |γ| ^ (2 : ℕ) := by
  obtain ⟨T, hT, hregion⟩ := exists_zero_free_region_explicit
  obtain ⟨C, hC0, hb⟩ :=
    exists_logDeriv_zeta_bound_of_region (c := 1 / 10000) (T₀ := T) (by norm_num) hregion
  refine ⟨C, max 4 (T + 1), hC0, le_max_left _ _, fun σ γ hγ hlow hhigh => hb σ γ hγ ?_ hhigh⟩
  rw [show min ((1 / 10000 : ℝ) / 4) (1 / 160) = 1 / 40000 by norm_num]
  exact hlow

end RHTower.Sieve
