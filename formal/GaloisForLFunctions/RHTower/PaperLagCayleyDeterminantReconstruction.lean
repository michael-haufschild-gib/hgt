import GaloisForLFunctions.RHTower.PaperLagCayleyRelativeApproximation
import GaloisForLFunctions.RHTower.PaperLagCayleyGreenBoundary

/-! # Recovering the signed lag from adjacent relative determinants

Adjacent tail determinants recover each source Cayley phase. Inverse Cayley
and the original affine charges then recover the literal integer lag.
-/

namespace RHTower.PaperLagCayley
noncomputable section
open GaloisForLFunctions.HTGeometry HilbertSchmidt _root_.Complex

theorem relativeAngleTail_step (N : ℕ) :
    relativeAngleTail N = relativeAngle N + relativeAngleTail (N + 1) := by
  have hs := (summable_nat_add_iff N).mpr summable_relativeAngle
  have h := hs.sum_add_tsum_nat_add 1
  simpa only [relativeAngleTail, Finset.sum_range_one, Nat.zero_add,
    Nat.add_assoc, Nat.add_comm 1] using h.symm

theorem fredholmDetOp_relativeDefect_step (N : ℕ) :
    fredholmDetOp (lpBasis ℕ) (relativeDefect N) =
      relativePhase N * fredholmDetOp (lpBasis ℕ) (relativeDefect (N + 1)) := by
  rw [fredholmDetOp_relativeDefect, fredholmDetOp_relativeDefect,
    relativePhase_eq_exp, relativeAngleTail_step, Complex.ofReal_add,
    add_mul, Complex.exp_add]

theorem phase_from_relative_determinants (N : ℕ) :
    (arithmeticPhase N : ℂ) *
      (fredholmDetOp (lpBasis ℕ) (relativeDefect N) /
        fredholmDetOp (lpBasis ℕ) (relativeDefect (N + 1))) = phase N := by
  rw [fredholmDetOp_relativeDefect_step, mul_div_cancel_right₀ _
    (fredholmDetOp_relativeDefect_ne_zero (N + 1)), relativePhase]
  field_simp [Circle.coe_ne_zero]

theorem source_from_relative_determinants (N : ℕ) :
    paperRealCayleyInverse ((arithmeticPhase N : ℂ) *
      (fredholmDetOp (lpBasis ℕ) (relativeDefect N) /
        fredholmDetOp (lpBasis ℕ) (relativeDefect (N + 1)))) = source N := by
  rw [phase_from_relative_determinants, source_from_phase]

theorem lag_from_relative_determinants (N : ℕ) :
    (affineBase + N * affineSlope + ∑ n ∈ Finset.range N,
      ((N : ℝ) - n) *
        (paperRealCayleyInverse ((arithmeticPhase n : ℂ) *
          (fredholmDetOp (lpBasis ℕ) (relativeDefect n) /
            fredholmDetOp (lpBasis ℕ) (relativeDefect (n + 1)))) / (n + 3 : ℝ))) /
          Real.sqrt (N + 3 : ℝ) = integerLag (N + 3) := by
  simp only [phase_from_relative_determinants]
  exact lagFromPhases_source N

end
end RHTower.PaperLagCayley
