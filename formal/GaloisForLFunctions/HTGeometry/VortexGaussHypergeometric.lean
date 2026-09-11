import GaloisForLFunctions.HTGeometry.VortexWardOperator
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-!
# Gauss hypergeometric series as a vortex recurrence

The coefficient-to-Ward-operator construction in arXiv:2609.09298, Section 2.9,
applies to the existing Gauss hypergeometric coefficients. Totalized inverse at a zero
Pochhammer denominator introduces a source term. The denominator-regularized Ward identity
holds for all complex parameters; positive integral denominators need no regularization.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open PowerSeries

def vortexGaussSeries (a b c : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (ordinaryHypergeometricCoefficient a b c)

def vortexGaussDenominator (c : ℂ) (n : ℕ) : ℂ := (n : ℂ) * (c + n - 1)
def vortexGaussNumerator (a b : ℂ) (n : ℕ) : ℂ := (a + n) * (b + n)

/-- Ratio recurrence valid even when a Pochhammer denominator vanishes. -/
theorem vortexGauss_coefficient_ratio (a b c : ℂ) (n : ℕ) :
    ordinaryHypergeometricCoefficient a b c (n + 1) =
      vortexGaussNumerator a b n / vortexGaussDenominator c (n + 1) *
        ordinaryHypergeometricCoefficient a b c n := by
  have hd : vortexGaussDenominator c (n + 1) = (n + 1 : ℂ) * (c + n) := by
    simp only [vortexGaussDenominator, Nat.cast_add, Nat.cast_one]
    ring
  rw [hd]
  simp only [ordinaryHypergeometricCoefficient, ascPochhammer_succ_eval,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    vortexGaussNumerator, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Existing Gauss coefficients are exactly a vortex ratio product. -/
theorem vortexGaussSeries_eq_ratio (a b c : ℂ) :
    vortexGaussSeries a b c =
      vortexRatioSeries (vortexGaussDenominator c) (vortexGaussNumerator a b) := by
  ext n
  induction n with
  | zero => simp [vortexGaussSeries, vortexRatioSeries, vortexProductSeries,
      ordinaryHypergeometricCoefficient]
  | succ n ih =>
    simp only [vortexGaussSeries, coeff_mk] at ih ⊢
    rw [vortexGauss_coefficient_ratio, vortexRatioSeries_recurrence, ih]

/-- The denominator factor regularizes the Gauss Ward equation at every complex parameter,
including nonpositive integral denominator parameters. -/
theorem vortexGauss_regularized_ward (a b c : ℂ) :
    vortexDiagonal (vortexGaussDenominator c)
      (vortexWard (vortexGaussDenominator c) (vortexGaussNumerator a b)
        (vortexGaussSeries a b c)) = 0 := by
  rw [vortexGaussSeries_eq_ratio, vortexRatioSeries_regularized_ward]
  simp [vortexGaussDenominator]

/-- Positive integral denominator parameters have no resonant defect, so the ordinary
second-order Gauss Ward equation holds without any restrictions on the numerator parameters. -/
theorem vortexGauss_positive_denominator_ward (a b : ℂ) (m : ℕ) :
    vortexWard (vortexGaussDenominator (m + 1)) (vortexGaussNumerator a b)
      (vortexGaussSeries a b (m + 1)) = 0 := by
  rw [vortexGaussSeries_eq_ratio, vortexRatioSeries_exact_residual]
  have hres : vortexResonanceSeries (vortexGaussDenominator (m + 1))
      (vortexGaussNumerator a b) = 0 := by
    unfold vortexResonanceSeries
    suffices h : PowerSeries.mk (fun n =>
        if vortexGaussDenominator (m + 1) (n + 1) = 0 then
          vortexGaussNumerator a b n * coeff n
            (vortexRatioSeries (vortexGaussDenominator (m + 1)) (vortexGaussNumerator a b))
        else 0) = 0 by rw [h, mul_zero]
    ext n
    have hden : vortexGaussDenominator (m + 1) (n + 1) ≠ 0 := by
      have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have hmn : (m + 1 + n : ℂ) ≠ 0 := by
        exact_mod_cast (show m + 1 + n ≠ 0 by omega)
      have he : vortexGaussDenominator (m + 1) (n + 1) =
          (n + 1 : ℂ) * (m + 1 + n) := by
        simp only [vortexGaussDenominator, Nat.cast_add, Nat.cast_one]
        ring
      rw [he]
      exact mul_ne_zero hn hmn
    simp [hden]
  rw [hres]
  simp [vortexGaussDenominator]

/-- At denominator parameter zero, the totalized Gauss series is the constant one. -/
theorem vortexGaussSeries_zero_denominator (a b : ℂ) :
    vortexGaussSeries a b 0 = 1 := by
  ext n
  cases n with
  | zero => simp [vortexGaussSeries, ordinaryHypergeometricCoefficient]
  | succ n => simp [vortexGaussSeries, ordinaryHypergeometricCoefficient]

/-- At the first resonant parameter, the unregularized equation has a concrete nonzero source
unless a numerator also terminates immediately. -/
theorem vortexGauss_zero_denominator_residual (a b : ℂ) :
    vortexWard (vortexGaussDenominator 0) (vortexGaussNumerator a b)
      (vortexGaussSeries a b 0) = - (C (a * b) * X) := by
  rw [vortexGaussSeries_zero_denominator]
  ext n
  cases n with
  | zero => simp [vortexWard, vortexGaussDenominator]
  | succ n =>
    simp only [vortexWard, map_sub, coeff_vortexDiagonal, coeff_succ_X_mul,
      coeff_one, Nat.succ_ne_zero, if_false, mul_zero, zero_sub,
      map_neg, coeff_C_mul, coeff_X]
    by_cases hn : n = 0
    · subst n
      simp [vortexGaussNumerator]
    · simp [hn]

end
end GaloisForLFunctions.HTGeometry
