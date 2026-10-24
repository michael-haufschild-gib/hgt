import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.MaskedPairHeatThreshold
import GaloisForLFunctions.RHTower.XiSliceHeatMaskedPairThreshold

/-!
# Exact Hermite normalization of the masked-pair threshold

The Gaussian parameter is twice the polynomial heat time. Each order also carries the
strictly positive factor `λ^j (2j)!`. This identifies the entire model moment cone while
retaining the separate signed cofactor estimate required by the actual Xi receiver.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry
open RHTower.DeBruijn

namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

/-- Falling factorials cancel the Gaussian moment factorial exactly, including orders above
the monomial degree, where both sides vanish. -/
theorem evenMonomialHermite_heat_coeff (lam : ℝ) (r j : ℕ) :
    lam ^ r * (2 * r).descFactorial (2 * j) * gaussEvenMoment (r - j) =
      lam ^ j * (2 * j).factorial * evenHeatMonomialCoeff (lam / 2) r j := by
  by_cases hj : j ≤ r
  · have hf : ((2 * r).descFactorial (2 * j) : ℝ) * (2 * (r - j)).factorial =
        (2 * r).factorial := by
      have h := Nat.factorial_mul_descFactorial (show 2 * j ≤ 2 * r by omega)
      rw [show 2 * r - 2 * j = 2 * (r - j) by omega] at h
      have hcast := congrArg (fun n : ℕ => (n : ℝ)) h
      push_cast at hcast
      simpa only [mul_comm] using hcast
    have hg : ((2 * r).descFactorial (2 * j) : ℝ) * gaussEvenMoment (r - j) =
        (2 * r).factorial * (1 / 2 : ℝ) ^ (r - j) / (r - j).factorial := by
      rw [gaussEvenMoment]
      calc
        _ = (((2 * r).descFactorial (2 * j) : ℝ) * (2 * (r - j)).factorial) *
            (1 / 2 : ℝ) ^ (r - j) / (r - j).factorial := by ring
        _ = _ := by rw [hf]
    have hp : lam ^ r = lam ^ j * lam ^ (r - j) := by
      rw [← pow_add, show j + (r - j) = r by omega]
    have hfj : ((2 * j).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hfr : ((r - j).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [mul_assoc, hg, hp, evenHeatMonomialCoeff, if_pos hj,
      show lam / 2 = lam * (1 / 2) by ring, mul_pow]
    field_simp
  · have hdesc : (2 * r).descFactorial (2 * j) = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [hdesc, Nat.cast_zero, mul_zero, zero_mul, evenHeatMonomialCoeff, if_neg hj, mul_zero]

/-- Exact parameter and factorial conversion to the existing all-order Hermite moment. -/
theorem maskedPairMoment_eq_heat_coeff (b lam : ℝ) (m j : ℕ) :
    maskedPairMoment b lam m j = lam ^ j * (2 * j).factorial *
      (forwardPolyHeat (lam / 2) (centralMaskedPair (b ^ 2) m)).coeff (2 * j) := by
  have h₀ := evenMonomialHermite_heat_coeff lam m j
  have h₁ := evenMonomialHermite_heat_coeff lam (m + 1) j
  have h₂ := evenMonomialHermite_heat_coeff lam (m + 2) j
  rw [centralMaskedPair_heat_coeff_even]
  unfold maskedPairMoment
  rw [show 2 * m + 2 = 2 * (m + 1) by omega, show 2 * m + 4 = 2 * (m + 2) by omega]
  linear_combination b ^ 4 * h₀ - 2 * b ^ 2 * h₁ + h₂

/-- At positive Gaussian heat, the complete Hermite sign test is the polynomial heat cone. -/
theorem maskedPairMoments_nonneg_iff {lam : ℝ} (hlam : 0 < lam) (b : ℝ) (m : ℕ) :
    (∀ j, 0 ≤ maskedPairMoment b lam m j) ↔
      CoeffNonneg (forwardPolyHeat (lam / 2) (centralMaskedPair (b ^ 2) m)) := by
  have hw : ∀ j, 0 < lam ^ j * ((2 * j).factorial : ℝ) := by intro j; positivity
  constructor
  · intro h n
    by_cases he : n % 2 = 0
    · rw [show n = 2 * (n / 2) by omega]
      have hm := h (n / 2)
      rw [maskedPairMoment_eq_heat_coeff] at hm
      exact (mul_nonneg_iff_of_pos_left (hw _)).mp hm
    · rw [show n = 2 * (n / 2) + 1 by omega, centralMaskedPair_heat_coeff_odd]
  · intro h j
    rw [maskedPairMoment_eq_heat_coeff]
    exact mul_nonneg (hw j).le (h _)

/-- The whole Gaussian moment cone has the exact depth-scaled threshold, including zero depth. -/
theorem maskedPairMoments_nonneg_iff_threshold {lam : ℝ} (hlam : 0 < lam) (b : ℝ) (m : ℕ) :
    (∀ j, 0 ≤ maskedPairMoment b lam m j) ↔
      2 * b ^ 2 * maskedPairHeatThreshold m ≤ lam := by
  rw [maskedPairMoments_nonneg_iff hlam]
  have hs : 0 ≤ lam / 2 := by positivity
  have h := centralMaskedPair_heat_cone_classification (b ^ 2) (lam / 2) m
  simp only [hs, true_and, max_eq_left (sq_nonneg b)] at h
  rw [h]
  constructor <;> intro hh <;> nlinarith only [hh]

/-- Below the exact threshold some genuine Hermite order is negative; above it none is. -/
theorem exists_negative_maskedPairMoment_iff {lam : ℝ} (hlam : 0 < lam) (b : ℝ) (m : ℕ) :
    (∃ j, maskedPairMoment b lam m j < 0) ↔
      lam < 2 * b ^ 2 * maskedPairHeatThreshold m := by
  have h := not_congr (maskedPairMoments_nonneg_iff_threshold hlam b m)
  push Not at h
  exact h

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
