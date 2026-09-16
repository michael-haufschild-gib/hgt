import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Nat.Choose.Cast

/-!
# Uniform interleaving mass

The factorial identity underlying the independence of a uniformly chosen sample,
an independent order on the sample, and an independent order on its complement.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Choosing a `k`-subset and independently ordering it and its complement assigns
each resulting interleaving the uniform mass `1 / n!`. -/
theorem uniform_interleaving_mass {n k : ℕ} (hk : k ≤ n) :
    (1 / (n.choose k : ℚ)) * (1 / (k.factorial : ℚ)) *
        (1 / ((n - k).factorial : ℚ)) = 1 / (n.factorial : ℚ) := by
  have hfactorial :
      (n.choose k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ) =
        (n.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  calc
    (1 / (n.choose k : ℚ)) * (1 / (k.factorial : ℚ)) *
          (1 / ((n - k).factorial : ℚ)) =
        ((n.choose k : ℚ) * (k.factorial : ℚ) *
          ((n - k).factorial : ℚ))⁻¹ := by
            simp only [div_eq_mul_inv, one_mul]
            rw [mul_inv, mul_inv]
    _ = 1 / (n.factorial : ℚ) := by
      simp only [div_eq_mul_inv, one_mul]
      rw [hfactorial]

/-- Premise-free two-block form of `uniform_interleaving_mass`. -/
theorem uniform_interleaving_mass_add (i j : ℕ) :
    (1 / ((i + j).choose j : ℚ)) * (1 / (j.factorial : ℚ)) *
        (1 / (i.factorial : ℚ)) = 1 / ((i + j).factorial : ℚ) := by
  simpa using uniform_interleaving_mass (n := i + j) (k := j) (Nat.le_add_left j i)

end GaloisForLFunctions.HTGeometry
