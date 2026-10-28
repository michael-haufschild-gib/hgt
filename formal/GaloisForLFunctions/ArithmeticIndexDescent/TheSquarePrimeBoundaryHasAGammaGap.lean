import GaloisForLFunctions.RHTower.DirichletArchimedeanSymbolPositivity
import GaloisForLFunctions.RHTower.XiLogDerivFactorization
import GaloisForLFunctions.RHTower.XiLogDerivRePositiveRightOfStrip
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegular
import GaloisForLFunctions.RHTower.GammaHardyPhaseRateLevyKhintchine

/-!
# A positive Gamma gap for the regular square-prime boundary

The exact boundary of the even-power prime Dirichlet series is compared
with the original Gamma jump symbol. Digamma duplication and reflection
leave a positive scalar gap and twice the completed Xi field on Re s = 1.
The zero-free edge makes that field nonnegative without a critical-line
hypothesis. The pole of the prime series is separate from this regular
symbol and must be restored in any physical-form application.
-/

noncomputable section
open Complex Real
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

/-- The Fourier symbol of the original Gamma jump energy, in angular frequency. -/
def gammaIncrementSymbol (t : ℝ) : ℝ :=
  2 * (gammaHardyPhaseRate t - gammaHardyPhaseRate 0)

/-- The regular boundary multiplier of the even-power prime source, after its pole is removed. -/
def squarePrimeRegularSymbol (t : ℝ) : ℝ :=
  2 * (RHTower.Sieve.zetaLogDerivReg ((1 : ℂ) + 2 * (t : ℂ) * I)).re

theorem gammaIncrementSymbol_eq_digamma (t : ℝ) :
    gammaIncrementSymbol t =
      (Complex.digamma (1 / 4 + I * (t : ℂ) / 2)).re -
        (Complex.digamma (1 / 4 : ℂ)).re := by
  have hp : linePt t / 2 = 1 / 4 + I * (t : ℂ) / 2 := by
    simp only [linePt]
    push_cast
    ring
  have hz : linePt 0 / 2 = (1 / 4 : ℂ) := by
    norm_num [linePt]
  simp only [gammaIncrementSymbol, gammaHardyPhaseRate, hp, hz]
  ring

/-- Duplication and reflection give the exact shift from the Gamma symbol to the square boundary. -/
theorem re_digamma_half_sub_quarter (t : ℝ) :
    (Complex.digamma (1 / 2 + I * (t : ℂ))).re -
      (Complex.digamma (1 / 4 + I * (t : ℂ) / 2)).re =
        Real.log 2 + Real.pi / (2 * Real.cosh (Real.pi * t)) := by
  let z : ℂ := 1 / 4 + I * (t : ℂ) / 2
  have hc : ∀ n : ℕ, 2 * z ≠ -(n : ℂ) := by
    intro n h
    have hr := congrArg Complex.re h
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp [z, Complex.mul_re] at hr
    linarith only [hr, hn]
  have he : 2 * z = 1 / 2 + I * (t : ℂ) := by dsimp only [z]; ring
  have hd0 := congrArg Complex.re (HTGeometry.digamma_duplication z hc)
  rw [he] at hd0
  have hd : 2 * (Complex.digamma (1 / 2 + I * (t : ℂ))).re =
      (Complex.digamma z).re + (Complex.digamma (z + 1 / 2)).re + 2 * Real.log 2 := by
    simpa [Complex.mul_re, Complex.log_re] using hd0
  have hr := RHTower.re_digamma_threeQuarter_sub_quarter t
  have h1 : 1 / 4 + (1 : ℂ) / 2 + I * (t : ℂ) / 2 = z + 1 / 2 := by dsimp only [z]; ring
  have h0 : 1 / 4 + ((0 : ℕ) : ℂ) / 2 + I * (t : ℂ) / 2 = z := by dsimp only [z]; ring
  rw [h1, h0] at hr
  change (Complex.digamma (1 / 2 + I * (t : ℂ))).re - (Complex.digamma z).re = _
  have hf : Real.pi / (2 * Real.cosh (Real.pi * t)) =
      (Real.pi / Real.cosh (Real.pi * t)) / 2 := by ring
  rw [hf]
  linarith only [hd, hr]

private theorem log_four_pi_eq : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
  rw [Real.log_mul (by norm_num) Real.pi_pos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.log_pow]
  norm_num

private theorem two_lt_log_four_pi : 2 < Real.log (4 * Real.pi) := by
  have h8 : (8 : ℝ) < 4 * Real.pi := by linarith only [Real.pi_gt_d2]
  have hl := Real.log_lt_log (by norm_num : (0 : ℝ) < 8) h8
  have he : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [he] at hl
  linarith only [hl, Real.log_two_gt_d9]

/-- The exact regular square-boundary gap retains the completed Xi field with its positive sign. -/
theorem gammaIncrement_sub_squarePrimeRegular_eq {t : ℝ} (ht : t ≠ 0) :
    gammaIncrementSymbol t - squarePrimeRegularSymbol t =
      Real.eulerMascheroniConstant + Real.log (4 * Real.pi) + Real.pi / 2 -
        Real.pi / (2 * Real.cosh (Real.pi * t)) - 2 / (1 + 4 * t ^ 2) +
          2 * (logDeriv xi ((1 : ℂ) + 2 * (t : ℂ) * I)).re := by
  let s : ℂ := 1 + 2 * (t : ℂ) * I
  have hsre : s.re = 1 := by simp [s]
  have hsim : s.im ≠ 0 := by simpa [s] using mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) ht
  have hs1 : s ≠ 1 := fun h => hsim (by rw [h]; simp)
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hsre])
  have hfour := logDeriv_xi_fourFactor_offReal hsim hz
  have hreg := RHTower.Sieve.neg_logDeriv_riemannZeta_eq_of_ne_zero hs1 hz
  have he : logDeriv xi s = 1 / s - (Real.log Real.pi : ℂ) / 2 +
      Complex.digamma (s / 2) / 2 - RHTower.Sieve.zetaLogDerivReg s := by
    rw [hfour]
    linear_combination -hreg
  have hinv : ((1 : ℂ) / s).re = 1 / (1 + 4 * t ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    simp [s]
    ring
  have hhalf : s / 2 = 1 / 2 + I * (t : ℂ) := by dsimp only [s]; ring
  have hdiv (z : ℂ) : (z / 2).re = z.re / 2 := by simp
  have hre := congrArg Complex.re he
  simp only [Complex.sub_re, Complex.add_re, hdiv, Complex.ofReal_re, hinv, hhalf] at hre
  have hd := re_digamma_half_sub_quarter t
  have hq := RHTower.re_digamma_one_quarter
  rw [gammaIncrementSymbol_eq_digamma, squarePrimeRegularSymbol, log_four_pi_eq]
  change (Complex.digamma (1 / 4 + I * (t : ℂ) / 2)).re -
      (Complex.digamma (1 / 4 : ℂ)).re - 2 * (RHTower.Sieve.zetaLogDerivReg s).re = _
  change _ = Real.eulerMascheroniConstant + (2 * Real.log 2 + Real.log Real.pi) + Real.pi / 2 -
    Real.pi / (2 * Real.cosh (Real.pi * t)) - 2 / (1 + 4 * t ^ 2) + 2 * (logDeriv xi s).re
  linear_combination -2 * hre - hd - hq

/-- The regular square-prime boundary is below the original Gamma symbol by a fixed positive gap. -/
theorem eulerConstant_le_gammaIncrement_sub_squarePrimeRegular (t : ℝ) :
    Real.eulerMascheroniConstant ≤ gammaIncrementSymbol t - squarePrimeRegularSymbol t := by
  by_cases ht : t = 0
  · subst t
    simp only [gammaIncrementSymbol, sub_self, mul_zero, squarePrimeRegularSymbol,
      Complex.ofReal_zero, mul_zero, zero_mul, add_zero, RHTower.Sieve.zetaLogDerivReg_one,
      Complex.neg_re, Complex.ofReal_re]
    linarith only [Real.one_half_lt_eulerMascheroniConstant]
  · rw [gammaIncrement_sub_squarePrimeRegular_eq ht]
    have hcosh : Real.pi / (2 * Real.cosh (Real.pi * t)) ≤ Real.pi / 2 :=
      div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
        (by linarith only [Real.one_le_cosh (Real.pi * t)])
    have hrat : 2 / (1 + 4 * t ^ 2) ≤ (2 : ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < 1 + 4 * t ^ 2)).mpr
      nlinarith only [sq_nonneg t]
    have hxi : 0 ≤ (logDeriv xi ((1 : ℂ) + 2 * (t : ℂ) * I)).re :=
      re_logDeriv_xi_nonneg_of_one_le_re (by simp)
    linarith only [hcosh, hrat, hxi, two_lt_log_four_pi]

theorem one_half_lt_gammaIncrement_sub_squarePrimeRegular (t : ℝ) :
    1 / 2 < gammaIncrementSymbol t - squarePrimeRegularSymbol t :=
  Real.one_half_lt_eulerMascheroniConstant.trans_le
    (eulerConstant_le_gammaIncrement_sub_squarePrimeRegular t)

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.re_digamma_half_sub_quarter
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.gammaIncrement_sub_squarePrimeRegular_eq
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.eulerConstant_le_gammaIncrement_sub_squarePrimeRegular
