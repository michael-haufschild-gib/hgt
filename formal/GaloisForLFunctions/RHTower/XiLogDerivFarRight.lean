import GaloisForLFunctions.RHTower.DigammaTwoSided
import GaloisForLFunctions.RHTower.DigammaVerticalMinimum

/-!
# Uniform far-right growth of the real Xi logarithmic derivative

The von Mangoldt series is bounded by its absolute sum at two. The vertical
minimum and real lower bound for digamma then give a lower bound growing
with the real part, uniformly over every imaginary part.
-/

open Complex

namespace RHTower

/-- Absolute convergence at two bounds the prime logarithmic derivative on the full half-plane. -/
theorem norm_LSeries_vonMangoldt_le_at_two {s : ℂ} (hs : 2 ≤ s.re) :
    ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s‖ ≤
      ∑' n, ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) 2 n‖ := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  have hsum2 : Summable (fun n => ‖LSeries.term f 2 n‖) :=
    summable_norm_iff.mpr
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num : 1 < (2 : ℂ).re))
  have hle : ∀ n, ‖LSeries.term f s n‖ ≤ ‖LSeries.term f 2 n‖ :=
    LSeries.norm_term_le_of_re_le_re f (by simpa using hs)
  have hsum : Summable (fun n => ‖LSeries.term f s n‖) :=
    hsum2.of_nonneg_of_le (fun _ => norm_nonneg _) hle
  exact (norm_tsum_le_tsum_norm hsum).trans (hsum.tsum_le_tsum hle hsum2)

/-- An explicit lower bound depending only on the real part. -/
theorem re_logDeriv_xi_lower_bound {s : ℂ} (hs : 2 ≤ s.re) :
    (Real.log (s.re / 2) - 1 - Real.log Real.pi) / 2 -
        (∑' n, ‖LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) 2 n‖) ≤
      (logDeriv xi s).re := by
  have hspos : 0 < s.re := by linarith
  have hhalf : 0 < s.re / 2 := by positivity
  have hpsi := (log_sub_inv_le_re_digamma hhalf).trans
    (digamma_real_le_re_digamma_add_mul_I hhalf (s.im / 2))
  have heq : ((s.re / 2 : ℝ) : ℂ) + ((s.im / 2 : ℝ) : ℂ) * I = s / 2 := by
    apply Complex.ext <;> simp
  rw [heq] at hpsi
  have hinv : 1 / (s.re / 2) ≤ (1 : ℝ) := by
    rw [div_le_iff₀ hhalf]
    linarith
  have hzero : 0 ≤ s⁻¹.re := by
    rw [Complex.inv_re]
    exact div_nonneg hspos.le (Complex.normSq_nonneg _)
  have hone : 0 ≤ (s - 1)⁻¹.re := by
    rw [Complex.inv_re]
    exact div_nonneg (by simp only [Complex.sub_re, Complex.one_re]; linarith)
      (Complex.normSq_nonneg _)
  have hprime := (Complex.re_le_norm _).trans (norm_LSeries_vonMangoldt_le_at_two hs)
  rw [logDeriv_xi_eq_arithmetic (by linarith), logDeriv_Gammaℝ_eq hspos]
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.div_ofNat_re,
    Complex.ofReal_re]
  linarith

/-- Every real lower bound holds uniformly on a sufficiently far right half-plane. -/
theorem exists_re_logDeriv_xi_ge_halfPlane (B : ℝ) :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ s : ℂ, R ≤ s.re → B ≤ (logDeriv xi s).re := by
  let C : ℝ := ∑' n, ‖LSeries.term
    (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) 2 n‖
  let A : ℝ := 2 * (B + C) + 1 + Real.log Real.pi
  refine ⟨max 2 (2 * Real.exp A), le_max_left _ _, fun s hs => ?_⟩
  have hs2 : 2 ≤ s.re := (le_max_left _ _).trans hs
  have hexp : Real.exp A ≤ s.re / 2 := by
    have := (le_max_right 2 (2 * Real.exp A)).trans hs
    linarith
  have hlog := Real.log_le_log (Real.exp_pos A) hexp
  rw [Real.log_exp] at hlog
  have hbound := re_logDeriv_xi_lower_bound hs2
  change (Real.log (s.re / 2) - 1 - Real.log Real.pi) / 2 - C ≤ _ at hbound
  dsimp [A] at hlog
  linarith

end RHTower
