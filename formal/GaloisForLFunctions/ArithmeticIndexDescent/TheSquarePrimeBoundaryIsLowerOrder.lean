import GaloisForLFunctions.ArithmeticIndexDescent.TheSquarePrimeBoundaryRetainsGammaEnergy
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivIsSublogarithmic

/-!
# The regular square-prime boundary is lower order than Gamma

The even-power source has its pole on the one-line. That pole has zero real
part away from the origin, so the sublogarithmic zeta logarithmic derivative
bounds the absolute regular multiplier. Gamma grows logarithmically; every
positive Gamma share therefore dominates the square multiplier at infinity.
-/

noncomputable section
open Complex Real
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

/-- At large frequency the original Gamma increment dominates half the logarithm. -/
theorem exists_half_log_le_gammaIncrement :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ t : ℝ, T ≤ |t| →
      Real.log |t| / 2 ≤ gammaIncrementSymbol t := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ,
      C = Real.log (2 * Real.pi) + 4 + Real.pi + 2 * gammaHardyPhaseRate 0 := ⟨_, rfl⟩
  refine ⟨max 2 (Real.exp (2 * C)), le_max_left _ _, ?_⟩
  intro t ht
  have ht2 : (2 : ℝ) ≤ |t| := (le_max_left _ _).trans ht
  have ht0 : 0 < |t| := by linarith only [ht2]
  have hte : Real.exp (2 * C) ≤ |t| := (le_max_right _ _).trans ht
  have hlog : 2 * C ≤ Real.log |t| := by
    have hh := Real.log_le_log (Real.exp_pos _) hte
    rwa [Real.log_exp] at hh
  have hfirst : 2 / |t| ^ 2 ≤ (2 : ℝ) :=
    div_le_self (by norm_num) (one_le_pow₀ (by linarith only [ht2]))
  have hsecond : Real.pi / (2 * |t|) ≤ Real.pi / 2 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by linarith only [ht2])
  have hb := gammaHardyPhaseRate_ge_log_conductor ht0
  rw [Real.log_div ht0.ne' (by positivity)] at hb
  rw [← gammaIncrementSymbol_abs, gammaIncrementSymbol]
  rw [hC] at hlog
  linarith only [hb, hfirst, hsecond, hlog]

/-- The removed square-source pole is purely imaginary off the origin. -/
theorem squarePrimeRegularSymbol_eq_neg_re_logDeriv {t : ℝ} (ht : t ≠ 0) :
    squarePrimeRegularSymbol t =
      -2 * (logDeriv riemannZeta ((1 : ℂ) + 2 * (t : ℂ) * I)).re := by
  have hs : (1 : ℂ) + 2 * (t : ℂ) * I ≠ 1 := by
    intro hh
    have hi : 2 * t = 0 := by simpa using congrArg Complex.im hh
    exact ht (by linarith only [hi])
  have hz : riemannZeta ((1 : ℂ) + 2 * (t : ℂ) * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp)
  have hb := congrArg Complex.re (Sieve.neg_logDeriv_riemannZeta_eq_of_ne_zero hs hz)
  have hpole : (((1 : ℂ) + 2 * (t : ℂ) * I - 1)⁻¹).re = 0 := by
    rw [Complex.inv_re]
    simp
  simp only [Complex.neg_re, Complex.add_re, hpole, zero_add] at hb
  rw [squarePrimeRegularSymbol]
  linarith only [hb]

/-- The regular square-prime multiplier uses arbitrarily little Gamma at high frequency. -/
theorem exists_squarePrime_regular_abs_le_epsilon_gamma {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ t : ℝ, T ≤ |t| →
      |squarePrimeRegularSymbol t| ≤ ε * gammaIncrementSymbol t := by
  obtain ⟨TZ, hTZ, hz⟩ := Sieve.exists_logDeriv_zeta_le_epsilon_log_abs
    (show 0 < ε / 8 by positivity)
  obtain ⟨TG, hTG, hg⟩ := exists_half_log_le_gammaIncrement
  refine ⟨max TZ TG, hTZ.trans (le_max_left _ _), ?_⟩
  intro t ht
  have htZ : TZ ≤ |t| := (le_max_left _ _).trans ht
  have htG : TG ≤ |t| := (le_max_right _ _).trans ht
  have ht2 : (2 : ℝ) ≤ |t| := hTG.trans htG
  have ht0 : 0 < |t| := by linarith only [ht2]
  have htne : t ≠ 0 := abs_pos.mp ht0
  have habs : |2 * t| = 2 * |t| := by rw [abs_mul]; norm_num
  have hzeta := hz (2 * t) (by rw [habs]; linarith only [htZ, ht0])
  have heq : (1 : ℂ) + ((2 * t : ℝ) : ℂ) * I =
      (1 : ℂ) + 2 * (t : ℂ) * I := by
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [heq, habs] at hzeta
  have hnorm : |squarePrimeRegularSymbol t| ≤
      2 * ‖logDeriv riemannZeta ((1 : ℂ) + 2 * (t : ℂ) * I)‖ := by
    rw [squarePrimeRegularSymbol_eq_neg_re_logDeriv htne, abs_mul]
    rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by norm_num)
  have hlog : Real.log (2 * |t|) ≤ 2 * Real.log |t| := by
    rw [Real.log_mul (by norm_num) ht0.ne']
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ht2
    linarith only [hh]
  have hlogpay := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ ε / 4 by positivity)
  have hgammapay := mul_le_mul_of_nonneg_left (hg t htG) hε.le
  linarith only [hnorm, hzeta, hlogpay, hgammapay]

end GaloisForLFunctions.ArithmeticIndexDescent
