import GaloisForLFunctions.RHTower.SourceHorizontalWoldPrimeClockProfile
import GaloisForLFunctions.HTGeometry.GapSeriesEntireCarrier

/-!
# Entire complex carrier for the source-horizontal Wold prime-clock profile

The literal real prime-clock profile is an odd factorial series. This module supplies the
coefficient-wise complex carrier. Its first nonzero Taylor coefficients are the exact source
coefficients `-1/9` and `-1/150`, so no fitted analytic correction enters the construction. The
summable reindexing that identifies its real restriction with the existing real profile is left
to the subsequent source-faithfulness bridge.
-/

open Filter PowerSeries
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Odd exponents of the literal source-horizontal Wold prime-clock profile. -/
def sourceHorizontalWoldPrimeClockComplexExponent (k : ℕ) : ℕ := 2 * k + 1

/-- Literal complexification of the source-horizontal Wold prime-clock coefficient. -/
def sourceHorizontalWoldPrimeClockComplexCoeff (k : ℕ) : ℂ :=
  (((1 / (sourceHorizontalWoldPrimeClockComplexExponent k : ℕ) : ℝ) - 1) /
    (sourceHorizontalWoldPrimeClockComplexExponent k).factorial : ℝ)

/-- Entire complex carrier with the literal odd source coefficients. -/
def sourceHorizontalWoldPrimeClockComplexCarrier : ℂ → ℂ :=
  GaloisForLFunctions.HTGeometry.gapFun sourceHorizontalWoldPrimeClockComplexExponent
    sourceHorizontalWoldPrimeClockComplexCoeff

private theorem sourceHorizontalWoldPrimeClockComplexExponent_injective :
    Function.Injective sourceHorizontalWoldPrimeClockComplexExponent := by
  intro a b hab
  dsimp [sourceHorizontalWoldPrimeClockComplexExponent] at hab
  omega

/-- Factorial decay makes the coefficient-faithful complex source carrier entire. -/
theorem sourceHorizontalWoldPrimeClockComplexCarrier_entire :
    GaloisForLFunctions.HTGeometry.EntireCoeffs
      (GaloisForLFunctions.HTGeometry.gapCoeff sourceHorizontalWoldPrimeClockComplexExponent
        sourceHorizontalWoldPrimeClockComplexCoeff) := by
  apply GaloisForLFunctions.HTGeometry.entireCoeffs_gapCoeff
    sourceHorizontalWoldPrimeClockComplexExponent_injective
  intro k
  have hden : (1 : ℝ) ≤ sourceHorizontalWoldPrimeClockComplexExponent k := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (by simp [sourceHorizontalWoldPrimeClockComplexExponent] :
        sourceHorizontalWoldPrimeClockComplexExponent k ≠ 0))
  have hden0 : (0 : ℝ) < sourceHorizontalWoldPrimeClockComplexExponent k := by positivity
  have hinv0 : 0 ≤
      (1 / (sourceHorizontalWoldPrimeClockComplexExponent k : ℕ) : ℝ) := by positivity
  have hinv :
      (1 / (sourceHorizontalWoldPrimeClockComplexExponent k : ℕ) : ℝ) ≤ 1 :=
    (div_le_one hden0).2 hden
  have hnum :
      |(1 / (sourceHorizontalWoldPrimeClockComplexExponent k : ℕ) : ℝ) - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hfac : 0 < ((sourceHorizontalWoldPrimeClockComplexExponent k).factorial : ℝ) := by
    positivity
  simp only [sourceHorizontalWoldPrimeClockComplexCoeff, Complex.norm_real, Real.norm_eq_abs]
  change |((1 / (sourceHorizontalWoldPrimeClockComplexExponent k : ℕ) : ℝ) - 1) /
      ((sourceHorizontalWoldPrimeClockComplexExponent k).factorial : ℝ)| ≤
    1 / ((sourceHorizontalWoldPrimeClockComplexExponent k).factorial : ℝ)
  rw [abs_div, abs_of_pos hfac]
  exact (div_le_div_iff_of_pos_right hfac).2 hnum

/-- The complex carrier has no linear source jet. -/
theorem sourceHorizontalWoldPrimeClockComplexCarrier_taylor_one :
    PowerSeries.coeff 1
      (GaloisForLFunctions.taylorPS sourceHorizontalWoldPrimeClockComplexCarrier) = 0 := by
  unfold sourceHorizontalWoldPrimeClockComplexCarrier
  rw [GaloisForLFunctions.HTGeometry.coeff_taylorPS_gapFun
    sourceHorizontalWoldPrimeClockComplexCarrier_entire]
  simpa [sourceHorizontalWoldPrimeClockComplexExponent,
    sourceHorizontalWoldPrimeClockComplexCoeff] using
    (GaloisForLFunctions.HTGeometry.gapCoeff_apply
      sourceHorizontalWoldPrimeClockComplexExponent_injective
      sourceHorizontalWoldPrimeClockComplexCoeff 0)

/-- Exact cubic source jet of the entire Wold carrier. -/
theorem sourceHorizontalWoldPrimeClockComplexCarrier_taylor_three :
    PowerSeries.coeff 3
      (GaloisForLFunctions.taylorPS sourceHorizontalWoldPrimeClockComplexCarrier) =
        -(1 / 9 : ℂ) := by
  unfold sourceHorizontalWoldPrimeClockComplexCarrier
  rw [GaloisForLFunctions.HTGeometry.coeff_taylorPS_gapFun
    sourceHorizontalWoldPrimeClockComplexCarrier_entire]
  rw [show (3 : ℕ) = sourceHorizontalWoldPrimeClockComplexExponent 1 by
    norm_num [sourceHorizontalWoldPrimeClockComplexExponent],
    GaloisForLFunctions.HTGeometry.gapCoeff_apply
      sourceHorizontalWoldPrimeClockComplexExponent_injective]
  norm_num [sourceHorizontalWoldPrimeClockComplexCoeff,
    sourceHorizontalWoldPrimeClockComplexExponent]

/-- Exact quintic source jet of the entire Wold carrier. -/
theorem sourceHorizontalWoldPrimeClockComplexCarrier_taylor_five :
    PowerSeries.coeff 5
      (GaloisForLFunctions.taylorPS sourceHorizontalWoldPrimeClockComplexCarrier) =
        -(1 / 150 : ℂ) := by
  unfold sourceHorizontalWoldPrimeClockComplexCarrier
  rw [GaloisForLFunctions.HTGeometry.coeff_taylorPS_gapFun
    sourceHorizontalWoldPrimeClockComplexCarrier_entire]
  rw [show (5 : ℕ) = sourceHorizontalWoldPrimeClockComplexExponent 2 by
    norm_num [sourceHorizontalWoldPrimeClockComplexExponent],
    GaloisForLFunctions.HTGeometry.gapCoeff_apply
      sourceHorizontalWoldPrimeClockComplexExponent_injective]
  norm_num [sourceHorizontalWoldPrimeClockComplexCoeff,
    sourceHorizontalWoldPrimeClockComplexExponent]

end

end RHTower
