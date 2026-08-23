import GaloisForLFunctions.RHTower.SymmetricShiftFunctionalEquation

namespace RHTower

noncomputable section

/-- A positive rational prime, used as an Euler place without requiring an external primality premise. -/
abbrev EulerPrime := {p : ℕ // Nat.Prime p}

/-- A reciprocal local root of unit modulus. -/
abbrev UnitaryLocalRoot := {alpha : ℂ // ‖alpha‖ = 1}

/-- Reciprocal roots after the symmetric Euler shift at one unitary local factor. -/
def symmetricShiftLocalRoots (p : EulerPrime) (a : ℝ) (alpha : UnitaryLocalRoot) : ℂ × ℂ :=
  (alpha.1 * (((p.1 : ℝ) ^ (-a) : ℝ) : ℂ), alpha.1 * (((p.1 : ℝ) ^ a : ℝ) : ℂ))

/-- The logarithmic modulus slope of a local reciprocal root at an Euler prime. -/
def localRootLogSlope (p : EulerPrime) (alpha : ℂ) : ℝ :=
  Real.log ‖alpha‖ / Real.log (p.1 : ℝ)

/-- Exact moduli of the two roots created by a symmetric shift. -/
theorem norm_symmetricShiftLocalRoots (p : EulerPrime) (a : ℝ) (alpha : UnitaryLocalRoot) :
    ‖(symmetricShiftLocalRoots p a alpha).1‖ = (p.1 : ℝ) ^ (-a) ∧
      ‖(symmetricShiftLocalRoots p a alpha).2‖ = (p.1 : ℝ) ^ a := by
  have hp : (0 : ℝ) < p.1 := by
    exact_mod_cast Nat.zero_lt_of_lt (Nat.Prime.one_lt p.2)
  constructor <;> unfold symmetricShiftLocalRoots
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hp _), alpha.2, one_mul]
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hp _), alpha.2, one_mul]

/-- Symmetric shifting changes the two logarithmic local slopes by exactly `-a` and `a`. -/
theorem localRootLogSlope_symmetricShiftLocalRoots (p : EulerPrime) (a : ℝ)
    (alpha : UnitaryLocalRoot) :
    localRootLogSlope p (symmetricShiftLocalRoots p a alpha).1 = -a ∧
      localRootLogSlope p (symmetricShiftLocalRoots p a alpha).2 = a := by
  have hp : (0 : ℝ) < p.1 := by
    exact_mod_cast Nat.zero_lt_of_lt (Nat.Prime.one_lt p.2)
  have hpone : (1 : ℝ) < p.1 := by
    exact_mod_cast Nat.Prime.one_lt p.2
  have hlog : Real.log (p.1 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hpone)
  have hnorm := norm_symmetricShiftLocalRoots p a alpha
  rw [localRootLogSlope, localRootLogSlope, hnorm.1, hnorm.2]
  constructor
  · rw [Real.log_rpow hp]
    field_simp
  · rw [Real.log_rpow hp]
    field_simp

/-- For a unitary base factor, transverse zero displacement equals the largest local modulus slope. -/
theorem max_abs_localRootLogSlope_symmetricShiftLocalRoots (p : EulerPrime) (a : ℝ)
    (alpha : UnitaryLocalRoot) :
    max |localRootLogSlope p (symmetricShiftLocalRoots p a alpha).1|
        |localRootLogSlope p (symmetricShiftLocalRoots p a alpha).2| = |a| := by
  have hslope := localRootLogSlope_symmetricShiftLocalRoots p a alpha
  rw [hslope.1, hslope.2, abs_neg, max_self]

/-- Both shifted local roots are tempered exactly at the collision parameter. -/
def symmetricShiftLocalTempered (p : EulerPrime) (a : ℝ) (alpha : UnitaryLocalRoot) : Prop :=
  ‖(symmetricShiftLocalRoots p a alpha).1‖ = 1 ∧
    ‖(symmetricShiftLocalRoots p a alpha).2‖ = 1

/-- The symmetric shift of a unitary local factor is tempered precisely when `a = 0`. -/
theorem symmetricShiftLocalTempered_iff (p : EulerPrime) (a : ℝ) (alpha : UnitaryLocalRoot) :
    symmetricShiftLocalTempered p a alpha ↔ a = 0 := by
  have hp : (0 : ℝ) < p.1 := by
    exact_mod_cast Nat.zero_lt_of_lt (Nat.Prime.one_lt p.2)
  have hpone : (1 : ℝ) < p.1 := by
    exact_mod_cast Nat.Prime.one_lt p.2
  have hlog : Real.log (p.1 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hpone)
  constructor
  · intro h
    have hpow : (p.1 : ℝ) ^ a = 1 := (norm_symmetricShiftLocalRoots p a alpha).2.symm.trans h.2
    have hzero : a * Real.log (p.1 : ℝ) = 0 := by
      have := congrArg Real.log hpow
      simpa [Real.log_rpow hp] using this
    exact (mul_eq_zero.mp hzero).resolve_right hlog
  · rintro rfl
    unfold symmetricShiftLocalTempered
    have hnorm := norm_symmetricShiftLocalRoots p 0 alpha
    simpa using hnorm

end

end RHTower
