import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.PNat.Basic

/-!
# Critical scalar dilations retain every multiplicative phase

Dividing a multiplicative unit-norm phase by the square root of its positive
integer argument gives a scalar action with exact critical energy. Thus
numeric order of the scaled quadratic forms alone does not restrict phases.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry

/-- Square-root normalization of a multiplicative complex character. -/
def criticalScalarCharacter (eta : ℕ+ →* ℂ) : ℕ+ →* ℂ where
  toFun p := eta p / (Real.sqrt (p : ℝ) : ℂ)
  map_one' := by simp
  map_mul' p q := by
    have hp : (0 : ℝ) ≤ p := (Nat.cast_nonneg (p : ℕ))
    simp only [map_mul, PNat.mul_coe, Nat.cast_mul, Real.sqrt_mul hp,
      Complex.ofReal_mul, div_eq_mul_inv, mul_inv_rev]
    ring

/-- Critical normalization retains the entire multiplicative phase. -/
theorem criticalScalarCharacter_phase (eta : ℕ+ →* ℂ) (p : ℕ+) :
    (Real.sqrt (p : ℝ) : ℂ) * criticalScalarCharacter eta p = eta p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.pos
  have hs : (Real.sqrt (p : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hp).ne'
  change (Real.sqrt (p : ℝ) : ℂ) * (eta p / (Real.sqrt (p : ℝ) : ℂ)) = eta p
  field_simp [hs]

/-- The scalar dilations multiply according to their positive integer indices. -/
theorem criticalScalarCharacter_action_mul (eta : ℕ+ →* ℂ) (p q : ℕ+) (z : ℂ) :
    criticalScalarCharacter eta (p * q) * z =
      criticalScalarCharacter eta p * (criticalScalarCharacter eta q * z) := by
  rw [map_mul, mul_assoc]

/-- Every unit-norm multiplicative phase gives the same critical quadratic form. -/
theorem criticalScalarCharacter_energy (eta : ℕ+ →* ℂ)
    (heta : ∀ p, ‖eta p‖ = 1) (p : ℕ+) (z : ℂ) :
    (p : ℝ) * ‖criticalScalarCharacter eta p * z‖ ^ 2 = ‖z‖ ^ 2 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.pos
  have hn : ‖criticalScalarCharacter eta p‖ = 1 / Real.sqrt (p : ℝ) := by
    change ‖eta p / (Real.sqrt (p : ℝ) : ℂ)‖ = _
    simp only [norm_div, heta, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [norm_mul, hn, mul_pow, div_pow, one_pow, Real.sq_sqrt hp.le]
  field_simp [hp.ne']

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.criticalScalarCharacter
#print axioms GaloisForLFunctions.HTGeometry.criticalScalarCharacter_phase
#print axioms GaloisForLFunctions.HTGeometry.criticalScalarCharacter_action_mul
#print axioms GaloisForLFunctions.HTGeometry.criticalScalarCharacter_energy
end
