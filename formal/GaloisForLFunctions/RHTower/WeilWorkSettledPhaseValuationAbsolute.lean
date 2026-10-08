import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationTightness

/-!
# Absolute valuation rows from square energy

Apply the paid divisibility energy estimate to coefficient moduli. This
controls absolute row sums, without assuming coefficient signs.
-/

open Complex
noncomputable section
namespace RHTower.WeilSingularArithmetic

def normCoeff (f : ℕ → ℂ) (n : ℕ) : ℂ := (‖f n‖ : ℂ)

theorem term_normCoeff (f : ℕ → ℂ) (s : ℝ) (n : ℕ) :
    LSeries.term (normCoeff f) (s : ℂ) n = (‖LSeries.term f (s : ℂ) n‖ : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.norm_term_eq, if_neg hn]
    simp only [normCoeff, Complex.ofReal_re, Complex.ofReal_div]
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    rfl

theorem summable_normCoeff {f : ℕ → ℂ} {s : ℝ}
    (hf : LSeriesSummable f (s : ℂ)) : LSeriesSummable (normCoeff f) (s : ℂ) := by
  refine hf.norm.of_norm_bounded fun n => ?_
  rw [term_normCoeff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem norm_LSeries_normCoeff (f : ℕ → ℂ) (s : ℝ) :
    ‖LSeries (normCoeff f) (s : ℂ)‖ = ∑' n, ‖LSeries.term f (s : ℂ) n‖ := by
  simp only [LSeries, term_normCoeff, ← Complex.ofReal_tsum, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg fun n => norm_nonneg _)]

theorem divisibilityPart_normCoeff (q : ℕ) (f : ℕ → ℂ) :
    divisibilityPart q (normCoeff f) = normCoeff (divisibilityPart q f) := by
  funext n
  by_cases hn : q ∣ n <;> simp [divisibilityPart, divisibilityMask, normCoeff, hn]

theorem absolute_divisibility_LSeries_le {f : ℕ → ℂ} {q : ℕ}
    (hq : q ≠ 0) {s : ℝ} (hs : 1 < s) (hf : LSeriesSummable f (s : ℂ))
    (he : Summable (fun n : ℕ => ‖f n‖ ^ 2 / (n : ℝ) ^ s)) :
    ∑' n, ‖LSeries.term (divisibilityPart q f) (s : ℂ) n‖ ≤
      Real.sqrt ((∑' n : ℕ, ‖f n‖ ^ 2 / (n : ℝ) ^ s) *
        ∑' n : ℕ, 1 / (n : ℝ) ^ s) / Real.sqrt q := by
  have he' : Summable (fun n : ℕ => ‖normCoeff f n‖ ^ 2 / (n : ℝ) ^ s) := by
    simpa only [normCoeff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      using he
  have hh := norm_divisibility_LSeries_sq_le_energy hq hs (summable_normCoeff hf) he'
  have hn (n : ℕ) : ‖normCoeff f n‖ = ‖f n‖ := by
    simp only [normCoeff, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
  simp only [hn] at hh
  rw [divisibilityPart_normCoeff, norm_LSeries_normCoeff] at hh
  have henergy : 0 ≤ (∑' n : ℕ, ‖f n‖ ^ 2 / (n : ℝ) ^ s) *
      ∑' n : ℕ, 1 / (n : ℝ) ^ s := by
    apply mul_nonneg <;> apply tsum_nonneg <;> intro n <;> positivity
  have hroot := Real.sqrt_le_sqrt hh
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (tsum_nonneg fun n => norm_nonneg _),
    Real.sqrt_div henergy] at hroot
  exact hroot

theorem absolute_valuation_LSeries_le {f : ℕ → ℂ} {p : ℕ} (hp : p.Prime)
    {s : ℝ} (hs : 1 < s) (hf : LSeriesSummable f (s : ℂ))
    (he : Summable (fun n : ℕ => ‖f n‖ ^ 2 / (n : ℝ) ^ s)) (k : ℕ) :
    ∑' n, ‖LSeries.term (valuationPart p k f) (s : ℂ) n‖ ≤
      Real.sqrt ((∑' n : ℕ, ‖f n‖ ^ 2 / (n : ℝ) ^ s) *
        ∑' n : ℕ, 1 / (n : ℝ) ^ s) * (Real.sqrt p)⁻¹ ^ k := by
  have hrow := absolute_divisibility_LSeries_le (pow_ne_zero k hp.ne_zero) hs hf he
  rw [sqrt_nat_pow, div_eq_mul_inv, ← inv_pow] at hrow
  apply le_trans ?_ hrow
  apply (summable_valuationPart p k hf).norm.tsum_le_tsum
    ?_ (summable_divisibilityPart (p ^ k) hf).norm
  intro n
  apply LSeries.norm_term_le
  by_cases hn : p ^ k ∣ n ∧ ¬ p ^ (k + 1) ∣ n
  · simp [valuationPart, valuationMask, divisibilityPart, divisibilityMask, hn]
  · simp [valuationPart, valuationMask, hn]

end RHTower.WeilSingularArithmetic
