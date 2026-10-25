import GaloisForLFunctions.ArithmeticOrientationTheory.UnpayabilityIsLocatedOnTheBohrPolydisk

/-!
# Normalized Bohr points represent distinct Wiener characters

Wiener evaluation ignores the zero coefficient. Fixing that Bohr coordinate
to zero gives canonical representatives, separated by point-mass evaluation.
-/

section

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open WienerAlgebraAt

/-- Canonical representatives of Bohr characters fix the unused zero coordinate. -/
abbrev NormalizedBohrPoint := {ω : BohrPoint // ω.ω 0 = 0}

/-- Setting the zero coordinate to zero preserves every positive Bohr coordinate. -/
def BohrPoint.normalize (ω : BohrPoint) : NormalizedBohrPoint :=
  ⟨{ ω := fun n => if n = 0 then 0 else ω.ω n
     map_one := by simp [ω.map_one]
     map_mul := by
       intro m n
       rcases eq_or_ne m 0 with rfl | hm
       · simp
       rcases eq_or_ne n 0 with rfl | hn
       · simp
       simp only [if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn), ω.map_mul]
     norm_le_one := by
       intro n
       rcases eq_or_ne n 0 with rfl | hn
       · simp
       · simpa only [if_neg hn] using ω.norm_le_one n }, by simp⟩

theorem BohrPoint.normalize_apply_ne_zero (ω : BohrPoint) {n : ℕ} (hn : n ≠ 0) :
    ω.normalize.val.ω n = ω.ω n := if_neg hn

/-- The unused zero coordinate does not change a Wiener character. -/
theorem bohrEval_normalize {σ : ℝ} (a : WienerAlgebraAt σ) (ω : BohrPoint) :
    bohrEval σ a.toFn ω.normalize.val = bohrEval σ a.toFn ω :=
  bohrEval_congr a.toFn (fun _ hn => ω.normalize_apply_ne_zero hn)

/-- Wiener characters separate normalized Bohr points exactly. -/
theorem normalizedBohrPoint_eq_of_character_eq {σ : ℝ}
    (ω ψ : NormalizedBohrPoint)
    (h : ∀ a : WienerAlgebraAt σ, bohrEval σ a.toFn ω.val = bohrEval σ a.toFn ψ.val) :
    ω = ψ := by
  apply Subtype.ext
  have hfun : ω.val.ω = ψ.val.ω := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ω.property.trans ψ.property.symm
    · have hp := h (pointMass n)
      rw [toFn_pointMass, bohrEval_pointMass hn.ne', bohrEval_pointMass hn.ne'] at hp
      have hpow : (n : ℂ) ^ (σ : ℂ) ≠ 0 := by
        rw [ne_eq, Complex.cpow_eq_zero_iff]
        exact fun hz => hn.ne' (by exact_mod_cast hz.1)
      have h := congrArg (fun z : ℂ => z * (n : ℂ) ^ (σ : ℂ)) hp
      simpa only [div_mul_cancel₀ _ hpow] using h
  rcases ω with ⟨⟨w, hw1, hwm, hwb⟩, hω⟩
  rcases ψ with ⟨⟨p, hp1, hpm, hpb⟩, hψ⟩
  change w = p at hfun
  cases hfun
  rfl

/-- Every algebra character has a normalized Bohr representative. -/
def normalizedBohrPointOfCharacter {σ : ℝ} (φ : WienerAlgebraAt σ →ₐ[ℂ] ℂ) :
    NormalizedBohrPoint :=
  ⟨characterBohrPoint (WeakDual.CharacterSpace.equivAlgHom.symm φ), by
    simp [characterBohrPoint]⟩

theorem normalizedBohrPointOfCharacter_eval {σ : ℝ}
    (φ : WienerAlgebraAt σ →ₐ[ℂ] ℂ) (a : WienerAlgebraAt σ) :
    bohrEval σ a.toFn (normalizedBohrPointOfCharacter φ).val = φ a :=
  (apply_eq_bohrEval (WeakDual.CharacterSpace.equivAlgHom.symm φ) a).symm

end GaloisForLFunctions.ArithmeticOrientationTheory

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.normalizedBohrPoint_eq_of_character_eq
end
end
