import GaloisForLFunctions.RHTower.DeningerHilbertKummerCharacter

/-!
# Polar decomposition of a Deninger character

A character of a group with values in `ℂ` never vanishes, so it factors pointwise as its unitary
part times the exponential of its logarithmic modulus.  Both factors are multiplicative, and under
the power map the unitary part is raised to the exponent while the modulus is multiplied by it.

* `deningerCharacter_polar` : `P α = η_P(α) · exp(L_P α)`.
* `deningerUnitPart_zpow`, `deningerLogModulus_zpow` : the behaviour of the two factors under
  powers.
-/

namespace RHTower

section Polar

variable {G : Type*} [Group G]

/-- **Polar decomposition of a character.**  The value of a character is its unitary part times
the exponential of its logarithmic modulus. -/
theorem deningerCharacter_polar (P : G →* ℂ) (a : G) :
    P a = deningerUnitPart P a * (Real.exp (deningerLogModulus P a) : ℂ) := by
  have hpos := deningerChar_norm_pos P a
  have hne : (‖P a‖ : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [deningerUnitPart_apply, deningerLogModulus, Real.exp_log hpos]
  field_simp

/-- The polar decomposition written with the modulus replacement. -/
theorem deningerCharacter_eq_modulusReplace (P : G →* ℂ) (a : G) :
    P a = deningerModulusReplace (deningerUnitPart P) (deningerLogModulus P) a :=
  (deningerModulusReplace_eq_self P rfl).symm

/-- **The unitary part is multiplicative in the exponent.** -/
theorem deningerUnitPart_zpow (P : G →* ℂ) (a : G) (n : ℤ) :
    deningerUnitPart P (a ^ n) = (deningerUnitPart P a) ^ n :=
  map_zpow (deningerUnitPart P) a n

/-- The unitary part of a character has modulus one, and the two factors of the polar
decomposition are therefore genuinely a phase and a positive scale. -/
theorem deningerCharacter_polar_norm (P : G →* ℂ) (a : G) :
    ‖deningerUnitPart P a‖ = 1 ∧ 0 < Real.exp (deningerLogModulus P a) :=
  ⟨deningerUnitPart_norm P a, Real.exp_pos _⟩

end Polar

end RHTower
