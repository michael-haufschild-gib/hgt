import GaloisForLFunctions.RHTower.ArithmeticDilationTraceClass

/-!
# Exact zero set of the arithmetic dilation Fredholm product

Absolute summability rules out a spurious zero caused by infinitely many nonzero factors.  Hence
the bare determinant `∏ n, (1 + z g n)` vanishes exactly when one of its linear factors vanishes.
For the constrained-prolate arithmetic spectrum, whose entries are all strictly positive, this
identifies the complete zero set with the advertised negative reciprocal spectrum.
-/

noncomputable section

namespace RHTower

/-- An absolutely summable bare Fredholm product vanishes exactly when one of its factors does. -/
theorem arithmeticDiagonalFredholmDeterminant_eq_zero_iff
    (g : ℕ → ℂ) (hg : Summable fun n => ‖g n‖) (z : ℂ) :
    arithmeticDiagonalFredholmDeterminant g z = 0 ↔
      ∃ n : ℕ, 1 + z * g n = 0 := by
  rw [arithmeticDiagonalFredholmDeterminant]
  constructor
  · intro hzero
    by_contra hfactor
    simp only [not_exists] at hfactor
    have hsum : Summable fun n : ℕ => ‖z * g n‖ := by
      simpa [norm_mul] using hg.mul_left ‖z‖
    exact (tprod_one_add_ne_zero_of_summable hfactor hsum) hzero
  · rintro ⟨n, hn⟩
    exact tprod_of_exists_eq_zero ⟨n, hn⟩

/-- **Complete zero classification for the constrained-prolate arithmetic determinant.**
There are no zeros beyond the negative reciprocals of the explicit positive eigenvalues. -/
theorem constrainedProlateArithmeticFredholmDeterminant_eq_zero_iff (z : ℂ) :
    constrainedProlateArithmeticFredholmDeterminant z = 0 ↔
      ∃ n : ℕ, z =
        -(GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ)⁻¹ := by
  rw [constrainedProlateArithmeticFredholmDeterminant,
    arithmeticDiagonalFredholmDeterminant_eq_zero_iff _
      summable_norm_constrainedProlateArithmeticEigenvalue_complex]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hk : (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt
        (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_pos n)
    apply (mul_right_cancel₀ hk)
    field_simp
    linear_combination hn
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    have hk : (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt
        (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_pos n)
    field_simp
    ring

end RHTower

end
