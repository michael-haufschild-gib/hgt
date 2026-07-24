import GaloisForLFunctions.RHTower.XiWeilArithmeticGram

/-!
# The 3-4-1 positivity of the von Mangoldt series

The Euler product enters the zero problem through one sign: `Λ(n) ≥ 0`.  Tested
against the trigonometric identity

`3 + 4 cos θ + cos 2θ = 2 (1 + cos θ)² ≥ 0`

it produces a positivity that no functional-equation argument can supply.  In
series form, for `σ > 1` and every real `τ`,

`0 ≤ 3 Re L(Λ, σ) + 4 Re L(Λ, σ + iτ) + Re L(Λ, σ + 2iτ)`,

each summand being `Λ(n) n^{−σ} · 2(1 + cos(τ log n))²`.  This is the arithmetic
primitive available to the positivity question for the Weil Gram: its entries
carry the von Mangoldt series, whose coefficients are nonnegative but whose
weights oscillate, and the identity above is the classical way to force a sign
out of that configuration.
-/

open Complex

namespace RHTower

noncomputable section

/-- Real part of a natural power with complex exponent. -/
theorem re_natCast_cpow_neg {n : ℕ} (hn : 0 < n) (σ τ : ℝ) :
    ((n : ℂ) ^ (-(((σ : ℂ)) + ((τ : ℂ)) * Complex.I))).re =
      (n : ℝ) ^ (-σ) * Real.cos (τ * Real.log n) := by
  have hn0 : ((n : ℂ)) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr hn.ne'
  have hlog : Complex.log ((n : ℂ)) = ((Real.log n : ℝ) : ℂ) :=
    (Complex.natCast_log).symm
  rw [Complex.cpow_def_of_ne_zero hn0, hlog, Complex.exp_re]
  have hre : (((Real.log n : ℝ) : ℂ) *
      -(((σ : ℂ)) + ((τ : ℂ)) * Complex.I)).re = -σ * Real.log n := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.add_re,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him : (((Real.log n : ℝ) : ℂ) *
      -(((σ : ℂ)) + ((τ : ℂ)) * Complex.I)).im = -(τ * Real.log n) := by
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [hre, him, Real.cos_neg]
  congr 1
  rw [Real.rpow_def_of_pos (by exact_mod_cast hn)]
  ring_nf

/-- The trigonometric core of the 3-4-1 inequality. -/
theorem three_four_one_cos (θ : ℝ) :
    3 + 4 * Real.cos θ + Real.cos (2 * θ) = 2 * (1 + Real.cos θ) ^ 2 := by
  rw [Real.cos_two_mul]
  ring

theorem three_four_one_cos_nonneg (θ : ℝ) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [three_four_one_cos]
  positivity

/-- Real part of a von Mangoldt `L`-series term. -/
theorem re_lseries_term_vonMangoldt {n : ℕ} (hn : 0 < n) (σ τ : ℝ) :
    (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      (((σ : ℂ)) + ((τ : ℂ)) * Complex.I) n).re =
      (ArithmeticFunction.vonMangoldt n : ℝ) * ((n : ℝ) ^ (-σ) *
        Real.cos (τ * Real.log n)) := by
  rw [LSeries.term_of_ne_zero hn.ne']
  have hn0 : ((n : ℂ)) ≠ 0 := by
    simpa using (Nat.cast_ne_zero (R := ℂ)).mpr hn.ne'
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  rw [Complex.mul_re, re_natCast_cpow_neg hn σ τ]
  have him : ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ).im = 0 :=
    Complex.ofReal_im _
  rw [him, Complex.ofReal_re, zero_mul, sub_zero]

/-- Real part of a von Mangoldt term at a real point. -/
theorem re_lseries_term_vonMangoldt_real {n : ℕ} (hn : 0 < n) (σ : ℝ) :
    (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      ((σ : ℂ)) n).re =
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) := by
  have h := re_lseries_term_vonMangoldt hn σ 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero, Real.cos_zero,
    mul_one] at h
  rw [h]

/-- **The 3-4-1 positivity, in series form.**  For `σ > 1` and every real `τ`,
the weighted combination of three von Mangoldt series is nonnegative, because
each prime power contributes `Λ(n) n^{−σ} · 2(1 + cos(τ log n))² ≥ 0`. -/
theorem three_four_one_vonMangoldt {σ τ : ℝ} (hσ : 1 < σ) :
    0 ≤ 3 * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          ((σ : ℂ))).re +
        4 * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (((σ : ℂ)) + ((τ : ℂ)) * Complex.I)).re +
        (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (((σ : ℂ)) + ((2 * τ : ℝ) : ℂ) * Complex.I)).re := by
  have hre0 : ((σ : ℂ)).re = σ := Complex.ofReal_re σ
  have hre1 : (((σ : ℂ)) + ((τ : ℂ)) * Complex.I).re = σ := by
    simp [Complex.add_re, Complex.mul_re]
  have hre2 : (((σ : ℂ)) + ((2 * τ : ℝ) : ℂ) * Complex.I).re = σ := by
    simp [Complex.add_re, Complex.mul_re]
  have hs0 := ArithmeticFunction.LSeriesSummable_vonMangoldt (by rw [hre0]; exact hσ)
  have hs1 := ArithmeticFunction.LSeriesSummable_vonMangoldt (by rw [hre1]; exact hσ)
  have hs2 := ArithmeticFunction.LSeriesSummable_vonMangoldt (by rw [hre2]; exact hσ)
  rw [LSeries, LSeries, LSeries, Complex.re_tsum hs0, Complex.re_tsum hs1,
    Complex.re_tsum hs2]
  have hsr0 : Summable (fun n : ℕ =>
      (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        ((σ : ℂ)) n).re) :=
    (Complex.hasSum_re hs0.hasSum).summable
  have hsr1 : Summable (fun n : ℕ =>
      (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        (((σ : ℂ)) + ((τ : ℂ)) * Complex.I) n).re) :=
    (Complex.hasSum_re hs1.hasSum).summable
  have hsr2 : Summable (fun n : ℕ =>
      (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        (((σ : ℂ)) + ((2 * τ : ℝ) : ℂ) * Complex.I) n).re) :=
    (Complex.hasSum_re hs2.hasSum).summable
  rw [← hsr0.tsum_mul_left, ← hsr1.tsum_mul_left,
    ← (hsr0.mul_left 3).tsum_add (hsr1.mul_left 4),
    ← ((hsr0.mul_left 3).add (hsr1.mul_left 4)).tsum_add hsr2]
  apply tsum_nonneg
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [LSeries.term_zero]
  · rw [re_lseries_term_vonMangoldt_real hn σ,
      re_lseries_term_vonMangoldt hn σ τ,
      re_lseries_term_vonMangoldt hn σ (2 * τ)]
    have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hp : 0 < (n : ℝ) ^ (-σ) :=
      Real.rpow_pos_of_pos (by exact_mod_cast hn) _
    have hcos : 0 ≤ 3 + 4 * Real.cos (τ * Real.log n) +
        Real.cos (2 * (τ * Real.log n)) := three_four_one_cos_nonneg _
    have hdouble : (2 * τ) * Real.log n = 2 * (τ * Real.log n) := by ring
    rw [hdouble]
    have hfac : 3 * ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)) +
        4 * ((ArithmeticFunction.vonMangoldt n : ℝ) *
          ((n : ℝ) ^ (-σ) * Real.cos (τ * Real.log n))) +
        (ArithmeticFunction.vonMangoldt n : ℝ) *
          ((n : ℝ) ^ (-σ) * Real.cos (2 * (τ * Real.log n))) =
        ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)) *
          (3 + 4 * Real.cos (τ * Real.log n) +
            Real.cos (2 * (τ * Real.log n))) := by
      ring
    rw [hfac]
    exact mul_nonneg (mul_nonneg hΛ (le_of_lt hp)) hcos

end

end RHTower
