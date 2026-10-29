/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GaloisForLFunctions.HeckeLFunctions.HeckeLSeriesHaveEulerProducts
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# The three-four-one inequality for Hecke Euler products

Absolute convergence makes the prime-ideal Euler logarithm summable. The identity
`3 + 4 Re(z) + Re(z²) = 2 (1 + Re(z))²` on the unit circle makes its three-four-one
combination nonnegative, including vertical twists. Exponentiation gives a lower bound
of one for `|L(σ,1)³ L(σ+it,ψ)⁴ L(σ+2it,ψ²)|` when `σ > 1`.

The local Taylor-series argument adapts the Dirichlet-character proof in
`Mathlib.NumberTheory.LSeries.Nonvanishing`.
-/

noncomputable section

open Complex NumberField IsDedekindDomain
open scoped Classical

namespace GaloisForLFunctions.HeckeLFunctions

variable {K : Type*} [Field K] [NumberField K]
variable (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)

/-- The logarithms of the prime-ideal Euler factors are summable on `Re s > 1`. -/
theorem summable_heckeEulerLog {s : ℂ} (hs : 1 < s.re) :
    Summable (fun v => -log (1 - heckePrimeTerm 𝔪 ψ s v)) :=
  (summable_norm_heckePrimeTerm 𝔪 ψ hs).of_norm.clog_one_sub.neg

/-- Exponentiating the sum of Euler logarithms gives the actual Hecke L-series. -/
theorem exp_tsum_heckeEulerLog {s : ℂ} (hs : 1 < s.re) :
    exp (∑' v, -log (1 - heckePrimeTerm 𝔪 ψ s v)) = heckeL 𝔪 ψ s := by
  have h := (summable_heckeEulerLog 𝔪 ψ hs).hasSum.cexp
  simp only [Function.comp_def, exp_neg,
    exp_log (heckeEulerDenominator_ne_zero 𝔪 ψ hs _)] at h
  exact h.unique (heckeL_eulerProduct_hasProd 𝔪 ψ hs)

/-- Taking the square of a character squares each extended ideal value. -/
theorem heckeValue_sq (I : Ideal (𝓞 K)) :
    heckeValue 𝔪 (ψ ^ 2) I = heckeValue 𝔪 ψ I ^ 2 := by
  by_cases h : ∃ hI : I ≠ ⊥, idealUnit hI ∈ idealGroup 𝔪
  · obtain ⟨hI, hm⟩ := h
    rw [heckeValue_of_mem 𝔪 (ψ ^ 2) hI hm, heckeValue_of_mem 𝔪 ψ hI hm,
      MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
  · rw [heckeValue_of_not_mem 𝔪 (ψ ^ 2) h, heckeValue_of_not_mem 𝔪 ψ h, zero_pow two_ne_zero]

/-- The Taylor coefficients reduce to `2 aⁿ (1 + Re(zⁿ))² / n`. -/
private theorem three_four_one_eulerLog_nonneg {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re +
      (-log (1 - a * z ^ 2)).re := by
  have h0 : ‖(a : ℂ)‖ < 1 := by simpa only [Complex.norm_of_nonneg ha] using ha1
  have h1 : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have h2 : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  have H := ((hasSum_re (hasSum_taylorSeries_neg_log h0)).mul_left 3).add
    ((hasSum_re (hasSum_taylorSeries_neg_log h1)).mul_left 4) |>.add
    (hasSum_re (hasSum_taylorSeries_neg_log h2))
  rw [← H.tsum_eq]
  refine tsum_nonneg fun n => ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im,
    zero_mul, sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_norm_sub_sq_re, norm_pow, hz]
    convert! (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

/-- The three logarithmic Euler factors have nonnegative combined real part at every prime. -/
theorem heckeEulerLog_three_four_one_nonneg {σ : ℝ} (hσ : 1 < σ) (t : ℝ)
    (v : HeightOneSpectrum (𝓞 K)) :
    0 ≤ 3 * (-log (1 - heckePrimeTerm 𝔪 1 σ v)).re +
      4 * (-log (1 - heckePrimeTerm 𝔪 ψ (σ + I * t) v)).re +
      (-log (1 - heckePrimeTerm 𝔪 (ψ ^ 2) (σ + 2 * I * t) v)).re := by
  have hn : 1 < Ideal.absNorm v.asIdeal :=
    lt_of_lt_of_le (Nat.lt_succ_self 1)
      (ArtinMertens.two_le_absNorm_of_isPrime v.isPrime v.ne_bot)
  have hn0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast (lt_trans Nat.zero_lt_one hn).ne'
  by_cases hm : idealUnit v.ne_bot ∈ idealGroup 𝔪
  · let z : ℂ := ψ (rayClass 𝔪 ⟨_, hm⟩)
    have hz : ‖z‖ = 1 := norm_char_eq_one ψ _
    have ha : (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn) (neg_neg_of_pos (lt_trans zero_lt_one hσ))
    have hz' : ‖z * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(I * t))‖ = 1 := by
      rw [norm_mul, hz, ← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos
        (by exact_mod_cast lt_trans Nat.zero_lt_one hn)]
      simp only [neg_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im,
        mul_zero, sub_self, neg_zero, Real.rpow_zero, one_mul]
    simp only [heckePrimeTerm, heckeValue_sq, heckeValue_of_mem 𝔪 1 v.ne_bot hm,
      heckeValue_of_mem 𝔪 ψ v.ne_bot hm, MonoidHom.one_apply, Units.val_one, one_mul]
    change 0 ≤ 3 * (-log (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-(σ : ℂ)))).re +
      4 * (-log (1 - z * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(σ + I * t)))).re +
      (-log (1 - z ^ 2 * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(σ + 2 * I * t)))).re
    convert three_four_one_eulerLog_nonneg (by positivity) ha hz' using 6
    · simp only [ofReal_cpow (Nat.cast_nonneg _) (-σ), ofReal_natCast, ofReal_neg]
    · congr 2
      rw [neg_add, cpow_add _ _ hn0, ← ofReal_neg,
        ofReal_cpow (Nat.cast_nonneg _) (-σ), ofReal_natCast, mul_left_comm]
    · rw [neg_add, cpow_add _ _ hn0, ← ofReal_neg,
        ofReal_cpow (Nat.cast_nonneg _) (-σ), ofReal_natCast,
        show -(2 * I * t) = (2 : ℕ) * -(I * t) by ring,
        cpow_nat_mul, mul_pow, mul_left_comm]
  · have hbad : ¬ ∃ hI : v.asIdeal ≠ ⊥, idealUnit hI ∈ idealGroup 𝔪 :=
      fun ⟨_, h⟩ => hm h
    simp only [heckePrimeTerm, heckeValue_of_not_mem 𝔪 _ hbad, zero_mul, sub_zero,
      log_one, neg_zero, zero_re, mul_zero, add_zero, le_refl]

/-- Euler-factor positivity bounds the three-four-one product below by one. -/
theorem one_le_norm_heckeL_three_four_one {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    1 ≤ ‖heckeL 𝔪 1 σ ^ 3 * heckeL 𝔪 ψ (σ + I * t) ^ 4 *
      heckeL 𝔪 (ψ ^ 2) (σ + 2 * I * t)‖ := by
  have h0 : 1 < (σ : ℂ).re := hσ
  have h1 : 1 < (σ + I * t : ℂ).re := by simpa using hσ
  have h2 : 1 < (σ + 2 * I * t : ℂ).re := by simpa using hσ
  have H0 := summable_heckeEulerLog 𝔪 1 h0
  have H1 := summable_heckeEulerLog 𝔪 ψ h1
  have H2 := summable_heckeEulerLog 𝔪 (ψ ^ 2) h2
  have S0 := (hasSum_re H0.hasSum).summable.mul_left 3
  have S1 := (hasSum_re H1.hasSum).summable.mul_left 4
  have S2 := (hasSum_re H2.hasSum).summable
  rw [← exp_tsum_heckeEulerLog 𝔪 1 h0, ← exp_tsum_heckeEulerLog 𝔪 ψ h1,
    ← exp_tsum_heckeEulerLog 𝔪 (ψ ^ 2) h2]
  simp only [← exp_nat_mul, Nat.cast_ofNat, ← exp_add, norm_exp, add_re, mul_re,
    re_ofNat, im_ofNat, zero_mul, sub_zero, Real.one_le_exp_iff]
  rw [re_tsum H0, re_tsum H1, re_tsum H2, ← tsum_mul_left, ← tsum_mul_left,
    ← S0.tsum_add S1, ← (S0.add S1).tsum_add S2]
  exact tsum_nonneg (heckeEulerLog_three_four_one_nonneg 𝔪 ψ hσ t)

end GaloisForLFunctions.HeckeLFunctions

