import GaloisForLFunctions.RHTower.Sieve.SymbolImaginaryPart
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The concrete root of unity and its angles

Everything so far has been stated for an abstract primitive root `ζ`.  Instantiating at
`ζ = exp(2πi/Q)` makes the angles explicit: `ζ^j = exp(iθ_j)` with `θ_j = 2πj/Q`, and the range
`1 ≤ j`, `2j ≤ Q` is exactly `0 < θ_j ≤ π`, where the uniform symbol bound applies.

That range is the natural half of the frequencies: the symbol at `j` and at `Q - j` are conjugate,
so bounding one half bounds the whole.
-/

namespace RHTower.Sieve

open Finset

/-- The standard primitive `Q`-th root of unity. -/
noncomputable def rootOfUnity (Q : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi / Q : ℝ) : ℂ) * Complex.I)

/-- Its powers are the exponentials of the multiples of the base angle. -/
theorem rootOfUnity_pow (Q j : ℕ) :
    (rootOfUnity Q) ^ j = Complex.exp (((j * (2 * Real.pi / Q) : ℝ) : ℂ) * Complex.I) :=
  exp_I_pow _ j

/-- It is a primitive `Q`-th root of unity. -/
theorem isPrimitiveRoot_rootOfUnity {Q : ℕ} (hQ : Q ≠ 0) :
    IsPrimitiveRoot (rootOfUnity Q) Q := by
  have h := Complex.isPrimitiveRoot_exp Q hQ
  have heq : rootOfUnity Q = Complex.exp (2 * Real.pi * Complex.I / Q) := by
    rw [rootOfUnity]
    congr 1
    push_cast
    field_simp
  rw [heq]
  exact h

/-- **Uniform symbol bound at a concrete frequency.**  On the half range `1 ≤ j`, `2j ≤ Q` the base
angle lies in `(0, π]`, where the harmonic sine bound applies. -/
theorem abs_sum_im_rootOfUnity_pow_div_le {Q j : ℕ} (hQ : 0 < Q) (hj1 : 1 ≤ j)
    (h2j : 2 * j ≤ Q) (M : ℕ) :
    |∑ d ∈ Finset.range M,
        (1 / ((d : ℝ) + 1)) * (((rootOfUnity Q) ^ j) ^ d).im| ≤ 1 + 3 * Real.pi := by
  have hQR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have h2jR : (2 : ℝ) * (j : ℝ) ≤ (Q : ℝ) := by exact_mod_cast h2j
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set θ : ℝ := (j : ℝ) * (2 * Real.pi / (Q : ℝ)) with hθ
  have h0 : 0 < θ := by
    rw [hθ]
    positivity
  have hle : θ ≤ Real.pi := by
    rw [hθ, div_eq_inv_mul, ← mul_assoc]
    rw [mul_comm ((j : ℝ)) ((Q : ℝ)⁻¹)]
    rw [mul_assoc]
    rw [inv_mul_le_iff₀ hQR]
    nlinarith [h2jR, hpi]
  have hpow : ((rootOfUnity Q) ^ j) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [rootOfUnity_pow Q j, hθ]
  rw [hpow]
  exact abs_sum_im_exp_pow_div_le h0 hle M

end RHTower.Sieve
