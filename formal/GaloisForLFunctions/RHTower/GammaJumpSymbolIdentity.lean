import GaloisForLFunctions.RHTower.GammaJumpMultiplier
import GaloisForLFunctions.HTGeometry.DigammaGaussSeries

/-!
# The Gamma jump symbol is the explicit positive series

The Fourier multiplier of the Gamma jump operator is the literal symbol

`r(η) = ψ(1 + iη) + ψ(1 − iη) + 2γ`.

Pairing the two Gauss series for digamma cancels Euler's constant and both harmonic tails, and each
conjugate pair of reciprocals collapses:

`2/a − 1/(a+iη) − 1/(a−iη) = 2η²/(a(a²+η²))`,   `a = n+1`.

Hence the literal symbol is exactly the explicit nonnegative series `2 Σ_{n≥1} η²/(n(n²+η²))`.  In
particular it is real and nonnegative, and the elementary growth bounds proved for that series are
bounds on the Gamma symbol itself, not on a model of it.
-/

open Complex Filter

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The literal Gamma jump symbol. -/
def gammaJumpSymbol (η : ℝ) : ℂ :=
  Complex.digamma (1 + (η : ℂ) * Complex.I) +
    Complex.digamma (1 - (η : ℂ) * Complex.I) +
    2 * (Real.eulerMascheroniConstant : ℂ)

/-- The conjugate pair of Gauss terms collapses onto twice the jump term. -/
theorem gaussDigammaSeriesTerm_pair (η : ℝ) (n : ℕ) :
    _root_.RHTower.gaussDigammaSeriesTerm (1 + (η : ℂ) * Complex.I) n +
        _root_.RHTower.gaussDigammaSeriesTerm (1 - (η : ℂ) * Complex.I) n =
      2 * ((gammaJumpTerm η n : ℝ) : ℂ) := by
  have hapos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have ha : ((n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast hapos.ne'
  have hA : (((n : ℝ) + 1) ^ 2 + η ^ 2) ≠ 0 := by positivity
  have hAC : (((n : ℂ) + 1) ^ 2 + (η : ℂ) ^ 2) ≠ 0 := by
    have : ((((n : ℝ) + 1) ^ 2 + η ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA
    convert this using 1
    push_cast
    ring
  have hp : (1 + (η : ℂ) * Complex.I + (n : ℂ)) = ((n : ℂ) + 1) + (η : ℂ) * Complex.I := by ring
  have hm : (1 - (η : ℂ) * Complex.I + (n : ℂ)) = ((n : ℂ) + 1) - (η : ℂ) * Complex.I := by ring
  have hprod : (((n : ℂ) + 1) + (η : ℂ) * Complex.I) * (((n : ℂ) + 1) - (η : ℂ) * Complex.I)
      = ((n : ℂ) + 1) ^ 2 + (η : ℂ) ^ 2 := by
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    ring_nf
    rw [Complex.I_sq]
    ring
  have hpne : (((n : ℂ) + 1) + (η : ℂ) * Complex.I) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact hAC hprod.symm
  have hmne : (((n : ℂ) + 1) - (η : ℂ) * Complex.I) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hprod
    exact hAC hprod.symm
  rw [_root_.RHTower.gaussDigammaSeriesTerm, _root_.RHTower.gaussDigammaSeriesTerm,
    hp, hm, gammaJumpTerm]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The literal Gamma symbol is the explicit positive series.** -/
theorem gammaJumpSymbol_eq (η : ℝ) :
    gammaJumpSymbol η = ((gammaJumpMultiplier η : ℝ) : ℂ) := by
  have hre1 : (0 : ℝ) < (1 + (η : ℂ) * Complex.I).re := by simp
  have hre2 : (0 : ℝ) < (1 - (η : ℂ) * Complex.I).re := by simp
  have h1 := _root_.RHTower.digamma_eq_neg_euler_add_tsum_gauss hre1
  have h2 := _root_.RHTower.digamma_eq_neg_euler_add_tsum_gauss hre2
  have hs1 := _root_.RHTower.summable_gaussDigammaSeriesTerm hre1
  have hs2 := _root_.RHTower.summable_gaussDigammaSeriesTerm hre2
  have hcast : ((gammaJumpMultiplier η : ℝ) : ℂ)
      = 2 * ∑' n : ℕ, ((gammaJumpTerm η n : ℝ) : ℂ) := by
    rw [gammaJumpMultiplier]
    push_cast
    congr 1
  have hpair : ∑' n : ℕ,
      (_root_.RHTower.gaussDigammaSeriesTerm (1 + (η : ℂ) * Complex.I) n +
        _root_.RHTower.gaussDigammaSeriesTerm (1 - (η : ℂ) * Complex.I) n)
      = 2 * ∑' n : ℕ, ((gammaJumpTerm η n : ℝ) : ℂ) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => gaussDigammaSeriesTerm_pair η n
  rw [gammaJumpSymbol, h1, h2, hcast, ← hpair, hs1.tsum_add hs2]
  ring

/-- The literal Gamma symbol is real and nonnegative. -/
theorem gammaJumpSymbol_eq_ofReal_nonneg (η : ℝ) :
    ∃ v : ℝ, 0 ≤ v ∧ gammaJumpSymbol η = (v : ℂ) :=
  ⟨gammaJumpMultiplier η, gammaJumpMultiplier_nonneg η, gammaJumpSymbol_eq η⟩

/-- The literal Gamma symbol obeys the elementary affine growth bound. -/
theorem norm_gammaJumpSymbol_le (η : ℝ) :
    ‖gammaJumpSymbol η‖ ≤ (∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + 1) ^ 2)) * (1 + |η|) := by
  rw [gammaJumpSymbol_eq, Complex.norm_real, Real.norm_eq_abs]
  exact abs_gammaJumpMultiplier_le η

end

end GaloisForLFunctions.RHTower
