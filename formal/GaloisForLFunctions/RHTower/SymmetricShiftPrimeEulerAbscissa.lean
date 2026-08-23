import GaloisForLFunctions.RHTower.SymmetricShiftFiniteEuler

namespace GaloisForLFunctions.RHTower

open Complex

noncomputable section

/-- The dominant `p^a` branch of the shifted infinite Euler factor at a prime. -/
def symmetricShiftPrimeEulerBranch (a : ℝ) (s : ℂ) (p : Nat.Primes) : ℂ :=
  (((p : ℝ) ^ a : ℝ) : ℂ) * ((p : ℂ) ^ (-s))

/-- The norm of the dominant shifted Euler branch is the real prime power at exponent `a - Re s`. -/
theorem norm_symmetricShiftPrimeEulerBranch (a : ℝ) (s : ℂ) (p : Nat.Primes) :
    ‖symmetricShiftPrimeEulerBranch a s p‖ = (p : ℝ) ^ (a - s.re) := by
  have hp : (0 : ℝ) < p := by
    exact_mod_cast p.property.pos
  unfold symmetricShiftPrimeEulerBranch
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hp.le _),
    Complex.norm_natCast_cpow_of_pos p.property.pos]
  rw [← Real.rpow_add hp]
  congr 1

/-- Exact absolute-convergence wall for the dominant infinite Euler branch. -/
theorem summable_norm_symmetricShiftPrimeEulerBranch_iff (a : ℝ) (s : ℂ) :
    Summable (fun p : Nat.Primes => ‖symmetricShiftPrimeEulerBranch a s p‖) ↔
      1 + a < s.re := by
  have hnorm : (fun p : Nat.Primes => ‖symmetricShiftPrimeEulerBranch a s p‖) =
      fun p : Nat.Primes => (p : ℝ) ^ (a - s.re) := by
    funext p
    exact norm_symmetricShiftPrimeEulerBranch a s p
  rw [hnorm, Nat.Primes.summable_rpow]
  constructor <;> intro h <;> linarith

end

end GaloisForLFunctions.RHTower
