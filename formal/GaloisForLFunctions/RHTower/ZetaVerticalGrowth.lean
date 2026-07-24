import GaloisForLFunctions.RHTower.ZetaTruncatedExtension
import GaloisForLFunctions.RHTower.ScaleSigmaSum

/-!
# Vertical growth of ζ near the one-line

`|ζ(σ+it)| ≤ 14·log|t|` for `|t| ≥ 8` and `1 − 1/log|t| ≤ σ ≤ 2`:
the truncated representation at `N = ⌊|t|⌋` prices the Dirichlet head by
`e·(log N + 2)` (each `n^{-σ} ≤ e/n` since `N^{1/log|t|} ≤ e`), the pole
term by `e/|t|`, and the sawtooth tail by `5e` — the growth input of the
de la Vallée Poussin zero-free region.
-/

noncomputable section

namespace RHTower

open Set Filter

set_option maxHeartbeats 1600000 in
/-- **Vertical growth bound**: `|ζ(σ+it)| ≤ 14·log|t|` for `|t| ≥ 8`,
`1 − 1/log|t| ≤ σ ≤ 2`. -/
theorem abs_riemannZeta_le_log {σ t : ℝ} (ht : 8 ≤ |t|)
    (hσ1 : 1 - 1 / Real.log |t| ≤ σ) (hσ2 : σ ≤ 2) :
    ‖riemannZeta (σ + t * Complex.I)‖ ≤ 14 * Real.log |t| := by
  have ht0 : (0 : ℝ) < |t| := by linarith
  have ht1 : (1 : ℝ) ≤ |t| := by linarith
  -- `log|t| > 2`
  have hexp2 : Real.exp 2 < 8 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have h3 : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 := by
      nlinarith [Real.exp_pos 1]
    rw [h2]
    nlinarith [h3]
  have hlogt2 : 2 < Real.log |t| := by
    have h1 : Real.log (Real.exp 2) < Real.log |t| :=
      Real.log_lt_log (Real.exp_pos 2) (lt_of_lt_of_le hexp2 ht)
    rwa [Real.log_exp] at h1
  have hσ0 : (1 : ℝ) / 2 ≤ σ := by
    have h1 : 1 / Real.log |t| ≤ 1 / 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlogt2.le
    linarith
  -- the real and imaginary parts of `s`
  have hre : (↑σ + ↑t * Complex.I).re = σ := by
    simp [Complex.add_re, Complex.mul_re]
  have him : (↑σ + ↑t * Complex.I).im = t := by
    simp [Complex.add_im, Complex.mul_im]
  have hs0 : 0 < (↑σ + ↑t * Complex.I).re := by rw [hre]; linarith
  have hs1 : (↑σ + ↑t * Complex.I) ≠ 1 := by
    intro h
    have h2 := congrArg Complex.im h
    rw [him] at h2
    simp at h2
    rw [h2] at ht
    simp at ht
    linarith
  -- the truncation level
  have hN1 : 1 ≤ ⌊|t|⌋₊ := Nat.le_floor (by exact_mod_cast ht1)
  have hN0 : (0 : ℝ) < (⌊|t|⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊|t|⌋₊)
  have hNt : (⌊|t|⌋₊ : ℝ) ≤ |t| := Nat.floor_le ht0.le
  have hNlow : |t| - 1 < (⌊|t|⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one |t|
    linarith
  have hNhalf : |t| / 2 ≤ (⌊|t|⌋₊ : ℝ) := by linarith
  -- the power helper: `x^{1-σ} ≤ e` on `[1, |t|]`
  have hE1 : (1 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp 1]
  have hpow : ∀ x : ℝ, 1 ≤ x → x ≤ |t| → x ^ (1 - σ) ≤ Real.exp 1 := by
    intro x hx1 hxt
    rcases le_or_gt (1 - σ) 0 with hc | hc
    · exact le_trans (Real.rpow_le_one_of_one_le_of_nonpos hx1 hc) hE1
    · have h1 : x ^ (1 - σ) ≤ |t| ^ (1 - σ) :=
        Real.rpow_le_rpow (by linarith) hxt hc.le
      have h2 : |t| ^ (1 - σ) ≤ |t| ^ (1 / Real.log |t|) :=
        Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
      have h3 : |t| ^ (1 / Real.log |t|) = Real.exp 1 := by
        rw [Real.rpow_def_of_pos ht0, mul_one_div,
          div_self (by linarith : Real.log |t| ≠ 0)]
      linarith
  -- rewrite through the truncated representation
  rw [zeta_eq_truncated_of_re_pos hN1 hs0 hs1, zetaTruncated]
  have htri : ‖(∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊,
        (n : ℂ) ^ (-(↑σ + ↑t * Complex.I)))
      + (⌊|t|⌋₊ : ℂ) ^ (1 - (↑σ + ↑t * Complex.I))
          / ((↑σ + ↑t * Complex.I) - 1)
      - (↑σ + ↑t * Complex.I)
          * zetaSawtoothTail ⌊|t|⌋₊ (↑σ + ↑t * Complex.I)‖
      ≤ ‖∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊,
          (n : ℂ) ^ (-(↑σ + ↑t * Complex.I))‖
        + ‖(⌊|t|⌋₊ : ℂ) ^ (1 - (↑σ + ↑t * Complex.I))
            / ((↑σ + ↑t * Complex.I) - 1)‖
        + ‖(↑σ + ↑t * Complex.I)
            * zetaSawtoothTail ⌊|t|⌋₊ (↑σ + ↑t * Complex.I)‖ := by
    calc _ ≤ ‖(∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊,
          (n : ℂ) ^ (-(↑σ + ↑t * Complex.I)))
        + (⌊|t|⌋₊ : ℂ) ^ (1 - (↑σ + ↑t * Complex.I))
            / ((↑σ + ↑t * Complex.I) - 1)‖
        + ‖(↑σ + ↑t * Complex.I)
            * zetaSawtoothTail ⌊|t|⌋₊ (↑σ + ↑t * Complex.I)‖ :=
          norm_sub_le _ _
      _ ≤ _ := by
          have := norm_add_le (∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊,
              (n : ℂ) ^ (-(↑σ + ↑t * Complex.I)))
            ((⌊|t|⌋₊ : ℂ) ^ (1 - (↑σ + ↑t * Complex.I))
              / ((↑σ + ↑t * Complex.I) - 1))
          linarith
  refine le_trans htri ?_
  -- (i) the Dirichlet head
  have hhead : ‖∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊,
      (n : ℂ) ^ (-(↑σ + ↑t * Complex.I))‖
      ≤ Real.exp 1 * (Real.log ⌊|t|⌋₊ + 2) := by
    calc ‖∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊,
          (n : ℂ) ^ (-(↑σ + ↑t * Complex.I))‖
        ≤ ∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊,
            ‖(n : ℂ) ^ (-(↑σ + ↑t * Complex.I))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, Real.exp 1 * (1 / (n : ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_Icc] at hn
          have hn0 : (0 : ℝ) < (n : ℝ) := by
            exact_mod_cast (by omega : 0 < n)
          have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast hn.1
          have hcast : ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) := by
            push_cast
            ring
          rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
          have hexp : (-(↑σ + ↑t * Complex.I)).re = -σ := by
            rw [Complex.neg_re, hre]
          rw [hexp]
          have h1 : (n : ℝ) ^ (-σ) = (n : ℝ) ^ (1 - σ) * (n : ℝ) ^ (-1 : ℝ) := by
            rw [← Real.rpow_add hn0]
            congr 1
            ring
          rw [h1, Real.rpow_neg_one]
          have h2 : (n : ℝ) ^ (1 - σ) ≤ Real.exp 1 := by
            apply hpow _ hn1
            calc (n : ℝ) ≤ (⌊|t|⌋₊ : ℝ) := by exact_mod_cast hn.2
              _ ≤ |t| := hNt
          have h3 : (0 : ℝ) ≤ ((n : ℝ))⁻¹ := by positivity
          calc (n : ℝ) ^ (1 - σ) * ((n : ℝ))⁻¹
              ≤ Real.exp 1 * ((n : ℝ))⁻¹ :=
                mul_le_mul_of_nonneg_right h2 h3
            _ = Real.exp 1 * (1 / (n : ℝ)) := by rw [one_div]
      _ = Real.exp 1 * ∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, 1 / (n : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ Real.exp 1 * (Real.log ⌊|t|⌋₊ + 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact sum_inv_le ⌊|t|⌋₊ hN1
  -- (ii) the pole term
  have hpole : ‖(⌊|t|⌋₊ : ℂ) ^ (1 - (↑σ + ↑t * Complex.I))
      / ((↑σ + ↑t * Complex.I) - 1)‖ ≤ Real.exp 1 / 8 := by
    rw [norm_div]
    have hden : |t| ≤ ‖(↑σ + ↑t * Complex.I) - 1‖ := by
      have h1 : |((↑σ + ↑t * Complex.I) - 1).im|
          ≤ ‖(↑σ + ↑t * Complex.I) - 1‖ := Complex.abs_im_le_norm _
      have h2 : ((↑σ + ↑t * Complex.I) - 1).im = t := by
        rw [Complex.sub_im, him]
        simp
      rwa [h2] at h1
    have hnum : ‖(⌊|t|⌋₊ : ℂ) ^ (1 - (↑σ + ↑t * Complex.I))‖
        ≤ Real.exp 1 := by
      have hcast : ((⌊|t|⌋₊ : ℕ) : ℂ) = (((⌊|t|⌋₊ : ℕ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hN0]
      have hexp : (1 - (↑σ + ↑t * Complex.I)).re = 1 - σ := by
        rw [Complex.sub_re, hre]
        simp
      rw [hexp]
      exact hpow _ (by exact_mod_cast hN1) hNt
    calc ‖(⌊|t|⌋₊ : ℂ) ^ (1 - (↑σ + ↑t * Complex.I))‖
          / ‖(↑σ + ↑t * Complex.I) - 1‖
        ≤ Real.exp 1 / ‖(↑σ + ↑t * Complex.I) - 1‖ :=
          div_le_div_of_nonneg_right hnum (norm_nonneg _)
      _ ≤ Real.exp 1 / |t| := by
          apply div_le_div_of_nonneg_left (by positivity) ht0 hden
      _ ≤ Real.exp 1 / 8 := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num) ht
  -- (iii) the tail term
  have htail : ‖(↑σ + ↑t * Complex.I)
      * zetaSawtoothTail ⌊|t|⌋₊ (↑σ + ↑t * Complex.I)‖
      ≤ 5 * Real.exp 1 := by
    rw [norm_mul]
    have hns : ‖(↑σ + ↑t * Complex.I)‖ ≤ 2 + |t| := by
      have h1 := Complex.norm_le_abs_re_add_abs_im (↑σ + ↑t * Complex.I)
      rw [hre, him] at h1
      have h2 : |σ| ≤ 2 := abs_le.2 ⟨by linarith, hσ2⟩
      linarith
    have htl := norm_zetaSawtoothTail_le
      (s := ↑σ + ↑t * Complex.I) hs0 hN1
    rw [hre] at htl
    have hNpow : (⌊|t|⌋₊ : ℝ) ^ (-σ) ≤ Real.exp 1 * (2 / |t|) := by
      have h1 : (⌊|t|⌋₊ : ℝ) ^ (-σ)
          = (⌊|t|⌋₊ : ℝ) ^ (1 - σ) * ((⌊|t|⌋₊ : ℝ))⁻¹ := by
        rw [← Real.rpow_neg_one (⌊|t|⌋₊ : ℝ), ← Real.rpow_add hN0]
        congr 1
        ring
      rw [h1]
      have h2 : (⌊|t|⌋₊ : ℝ) ^ (1 - σ) ≤ Real.exp 1 :=
        hpow _ (by exact_mod_cast hN1) hNt
      have h3 : ((⌊|t|⌋₊ : ℝ))⁻¹ ≤ 2 / |t| := by
        rw [inv_eq_one_div]
        rw [div_le_div_iff₀ hN0 ht0]
        linarith
      have h4 : (0 : ℝ) ≤ ((⌊|t|⌋₊ : ℝ))⁻¹ := by positivity
      calc (⌊|t|⌋₊ : ℝ) ^ (1 - σ) * ((⌊|t|⌋₊ : ℝ))⁻¹
          ≤ Real.exp 1 * ((⌊|t|⌋₊ : ℝ))⁻¹ :=
            mul_le_mul_of_nonneg_right h2 h4
        _ ≤ Real.exp 1 * (2 / |t|) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
    have htl2 : ‖zetaSawtoothTail ⌊|t|⌋₊ (↑σ + ↑t * Complex.I)‖
        ≤ Real.exp 1 * (2 / |t|) / (1 / 2) := by
      calc ‖zetaSawtoothTail ⌊|t|⌋₊ (↑σ + ↑t * Complex.I)‖
          ≤ (⌊|t|⌋₊ : ℝ) ^ (-σ) / σ := htl
        _ ≤ Real.exp 1 * (2 / |t|) / σ :=
            div_le_div_of_nonneg_right hNpow (by linarith)
        _ ≤ Real.exp 1 * (2 / |t|) / (1 / 2) := by
            apply div_le_div_of_nonneg_left (by positivity)
              (by norm_num) hσ0
    calc ‖(↑σ + ↑t * Complex.I)‖
          * ‖zetaSawtoothTail ⌊|t|⌋₊ (↑σ + ↑t * Complex.I)‖
        ≤ (2 + |t|) * (Real.exp 1 * (2 / |t|) / (1 / 2)) := by
          apply mul_le_mul hns htl2 (norm_nonneg _) (by linarith)
      _ = 4 * Real.exp 1 * (2 / |t| + 1) := by
          field_simp
          ring
      _ ≤ 5 * Real.exp 1 := by
          have h1 : 2 / |t| ≤ 1 / 4 := by
            rw [div_le_div_iff₀ ht0 (by norm_num)]
            linarith
          nlinarith [hE1]
  -- assemble
  have hlogN : Real.log (⌊|t|⌋₊ : ℝ) ≤ Real.log |t| :=
    Real.log_le_log hN0 hNt
  have hkey : Real.exp 1 * (Real.log |t| + 2) + Real.exp 1 / 8
      + 5 * Real.exp 1 ≤ 14 * Real.log |t| := by
    have hE := Real.exp_one_lt_d9
    nlinarith [mul_pos (show (0 : ℝ) < 14 - Real.exp 1 by linarith)
      (show (0 : ℝ) < Real.log |t| - 2 by linarith)]
  have hmono : Real.exp 1 * (Real.log (⌊|t|⌋₊ : ℝ) + 2)
      ≤ Real.exp 1 * (Real.log |t| + 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  linarith [hhead, hpole, htail, hmono, hkey]

end RHTower
