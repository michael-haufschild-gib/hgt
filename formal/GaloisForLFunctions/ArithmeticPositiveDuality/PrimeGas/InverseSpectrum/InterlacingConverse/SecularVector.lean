import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InterlacingConverse.Residues
import Mathlib.Analysis.Real.Sqrt

/-! # The normalized eigenvector equation from the inverse spectral residues -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Finset

/-- Coordinates of the omitted unit direction before applying heat. -/
def missingCoeff {m : ℕ} (a : Fin (m+1) → ℝ) (b : Fin m → ℝ) (i : Fin (m+1)) := Real.sqrt (residueMass a b i)

theorem missingCoeff_sq {m : ℕ} {a : Fin (m+1) → ℝ} (ha : StrictAnti a) {b : Fin m → ℝ}
    (hb : ∀ j, a j.succ < b j ∧ b j < a j.castSucc) (i : Fin (m+1)) :
    missingCoeff a b i ^ 2 = residueMass a b i := Real.sq_sqrt (residueMass_pos ha hb i).le

theorem missingCoeff_unit {m : ℕ} {a : Fin (m+1) → ℝ} (ha : StrictAnti a) {b : Fin m → ℝ}
    (hb : ∀ j, a j.succ < b j ∧ b j < a j.castSucc) : ∑ i, missingCoeff a b i ^ 2 = 1 := by
  simpa only [missingCoeff_sq ha hb] using sum_residueMass ha.injective b

/-- The heat-visible missing vector has overlap one with each resolvent vector. -/
theorem heated_resolvent_overlap {m : ℕ} {a d : Fin (m+1) → ℝ} (ha : StrictAnti a) (hd : ∀ i, d i^2 = a i)
    {b : Fin m → ℝ} (hb : ∀ j, a j.succ < b j ∧ b j < a j.castSucc) (j : Fin m) :
    ∑ i, (d i*missingCoeff a b i)*((d i*missingCoeff a b i)/(a i-b j)) = 1 := by
  have he (i : Fin (m+1)) : (d i*missingCoeff a b i)*((d i*missingCoeff a b i)/(a i-b j)) =
      residueMass a b i + b j*(residueMass a b i/(a i-b j)) := by
    rw [← mul_div_assoc,← sq,mul_pow,hd,missingCoeff_sq ha hb]
    field_simp [sub_ne_zero.mpr (node_ne_gap ha hb i j)]
    ring
  simp only [he,Finset.sum_add_distrib,← Finset.mul_sum,residueMass_secular ha hb j,mul_zero,add_zero,sum_residueMass ha.injective]

#print axioms missingCoeff_unit
#print axioms heated_resolvent_overlap

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
