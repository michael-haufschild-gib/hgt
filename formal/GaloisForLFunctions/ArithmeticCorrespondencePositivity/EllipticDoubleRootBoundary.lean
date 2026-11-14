import GaloisForLFunctions.ArithmeticCorrespondencePositivity.DoubleRootSpecialization
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheMertensBudgetOfAnEllipticCurveIsStrictHasse

/-!
# Exact elliptic Mertens energy at the Hasse boundary

At trace `a=2r` and field-size parameter `q=r²`, the two Frobenius roots
coincide. The reciprocal numerator coefficients are `(k+1)r^k`, and the
full reciprocal zeta coefficients retain the factor `-(r-1)²`. Their
normalized cumulative energy is exactly cubic. The formula also includes
the cancellation at `r=1` and the totalized zero-denominator case `r=0`.
-/

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open Finset

noncomputable section

/-- The elliptic `H¹` row at a double Frobenius root. -/
theorem h1Row_double_root (r : ℝ) (k : ℕ) :
    h1Row (2 * r) (r ^ 2) k = ((k + 1 : ℕ) : ℝ) * r ^ k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [h1Row]
  | one => simp [h1Row]
  | more k h₀ h₁ =>
    change 2 * r * h1Row (2 * r) (r ^ 2) (k + 1) -
      r ^ 2 * h1Row (2 * r) (r ^ 2) k = _
    rw [h₀, h₁]
    simp only [pow_add, pow_one]
    push_cast
    ring

/-- The elliptic row is the same repeated-root coefficient system as the spectral row. -/
theorem h1Row_double_root_eq_spectral (r : ℝ) (k : ℕ) :
    (h1Row (2 * r) (r ^ 2) k : ℂ) = spectralMertensRow ![(r : ℂ), (r : ℂ)] k := by
  rw [h1Row_double_root, spectralMertensRow_double]
  push_cast
  rfl

/-- The full elliptic Mertens row retains the square of the distance from the trivial root. -/
theorem ellipticMertens_double_root (r : ℝ) (k : ℕ) :
    ellipticMertens (2 * r) (r ^ 2) (k + 1) =
      -(r - 1) ^ 2 * ((k + 1 : ℕ) : ℝ) * r ^ k := by
  rw [ellipticMertens, h1Row_double_root]
  ring

/-- Exact cubic energy on both Hasse boundaries, including the cancellation at `r=1`. -/
theorem ellipticMertensEnergy_double_root (r : ℝ) (N : ℕ) :
    ellipticMertensEnergy (2 * r) (r ^ 2) N =
      ((r - 1) ^ 4 / r ^ 2) *
        ((N : ℝ) * ((N : ℝ) + 1) * (2 * (N : ℝ) + 1) / 6) := by
  by_cases hr : r = 0
  · subst r
    simp [ellipticMertensEnergy]
  have hterm (k : ℕ) :
      ellipticMertens (2 * r) (r ^ 2) (k + 1) ^ 2 / (r ^ 2) ^ (k + 1) =
        ((r - 1) ^ 4 / r ^ 2) * ((k : ℝ) + 1) ^ 2 := by
    have hpow : (r ^ 2) ^ (k + 1) = r ^ 2 * (r ^ k) ^ 2 := by
      rw [pow_succ', ← pow_mul, Nat.mul_comm 2 k, pow_mul]
    rw [ellipticMertens_double_root, hpow]
    push_cast
    field_simp [hr]
  rw [ellipticMertensEnergy]
  simp_rw [hterm]
  rw [← mul_sum]
  congr 1
  simpa only [spectralMertensRow_double_phase_norm] using
    spectralMertensRow_double_phase_energy 0 N

end

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
