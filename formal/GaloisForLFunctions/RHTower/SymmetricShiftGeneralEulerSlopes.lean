import GaloisForLFunctions.RHTower.SymmetricShiftEulerSlopes

/-!
# General reciprocal-root slopes under symmetric shifts

The unitary specialization records the tempered boundary.  This leaf proves the preceding general
identity for every nonzero reciprocal local root: its two shifted slopes are its original slope
minus and plus the shift parameter.
-/

open Complex

namespace RHTower

noncomputable section

/-- A nonzero reciprocal local Euler root. -/
abbrev NonzeroLocalRoot := {alpha : ℂ // alpha ≠ 0}

/-- Reciprocal roots after symmetric shifting of an arbitrary nonzero local root. -/
def symmetricShiftGeneralLocalRoots
    (p : EulerPrime) (a : ℝ) (alpha : NonzeroLocalRoot) : ℂ × ℂ :=
  (alpha.1 * (((p.1 : ℝ) ^ (-a) : ℝ) : ℂ),
    alpha.1 * (((p.1 : ℝ) ^ a : ℝ) : ℂ))

/-- Exact moduli of the symmetric shifts of an arbitrary nonzero reciprocal root. -/
theorem norm_symmetricShiftGeneralLocalRoots
    (p : EulerPrime) (a : ℝ) (alpha : NonzeroLocalRoot) :
    ‖(symmetricShiftGeneralLocalRoots p a alpha).1‖ =
        ‖alpha.1‖ * (p.1 : ℝ) ^ (-a) ∧
      ‖(symmetricShiftGeneralLocalRoots p a alpha).2‖ =
        ‖alpha.1‖ * (p.1 : ℝ) ^ a := by
  have hp : (0 : ℝ) < p.1 := by
    exact_mod_cast Nat.zero_lt_of_lt (Nat.Prime.one_lt p.2)
  constructor <;> unfold symmetricShiftGeneralLocalRoots
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hp _)]
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hp _)]

/-- General symmetric-shift slope law: every base slope changes by exactly `∓a`. -/
theorem localRootLogSlope_symmetricShiftGeneralLocalRoots
    (p : EulerPrime) (a : ℝ) (alpha : NonzeroLocalRoot) :
    localRootLogSlope p (symmetricShiftGeneralLocalRoots p a alpha).1 =
        localRootLogSlope p alpha.1 - a ∧
      localRootLogSlope p (symmetricShiftGeneralLocalRoots p a alpha).2 =
        localRootLogSlope p alpha.1 + a := by
  have hp : (0 : ℝ) < p.1 := by
    exact_mod_cast Nat.zero_lt_of_lt (Nat.Prime.one_lt p.2)
  have hpone : (1 : ℝ) < p.1 := by
    exact_mod_cast Nat.Prime.one_lt p.2
  have hlog : Real.log (p.1 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hpone)
  have halpha : ‖alpha.1‖ ≠ 0 := norm_ne_zero_iff.mpr alpha.2
  have hnorm := norm_symmetricShiftGeneralLocalRoots p a alpha
  simp only [localRootLogSlope]
  constructor
  · rw [hnorm.1, Real.log_mul halpha
      (Real.rpow_pos_of_pos hp (-a)).ne', Real.log_rpow hp]
    field_simp
    ring
  · rw [hnorm.2, Real.log_mul halpha
      (Real.rpow_pos_of_pos hp a).ne', Real.log_rpow hp]
    field_simp

end

end RHTower
