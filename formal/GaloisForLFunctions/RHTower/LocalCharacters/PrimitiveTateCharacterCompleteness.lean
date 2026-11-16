import GaloisForLFunctions.RHTower.LocalCharacters.PadicCharacterDecomposition
import GaloisForLFunctions.RHTower.FieldOnePadicRamifiedTateEquation258

/-!
# Completeness of the primitive p-adic Tate characters

Every continuous unitary character of `ℚ_pˣ` is one of the existing Tate
characters, with a primitive Dirichlet angular character at its exact
prime-power conductor. Finite angular descent follows from compactness;
passing to the primitive Dirichlet character removes redundant conductor
depth. The valuation phase is the character's value at `p`.
-/

noncomputable section
namespace GaloisForLFunctions.RHTower.LocalCharacters

variable (p : ℕ) [Fact p.Prime]

private theorem primitive_prime_power_lift {n d : ℕ} (hd : d ∣ p ^ n)
    (χ : DirichletCharacter ℂ d) (hχ : χ.IsPrimitive) :
    ∃ m ≤ n, ∃ ξ : FieldOnePadicPrimitiveAngularCharacter p m,
      ∀ u : ℤ_[p]ˣ, ξ.1 (fieldOnePadicUnitReduction p m u) =
        (χ.changeLevel hd) (fieldOnePadicUnitReduction p n u) := by
  obtain ⟨m, hmn, rfl⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd
  refine ⟨m, hmn, ⟨χ, hχ⟩, fun u => ?_⟩
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd]
  congr 1
  exact (PadicInt.cast_toZModPow m n hmn (u : ℤ_[p])).symm

/-- Every finite angular character descends to an exact prime-power conductor. -/
theorem exists_primitive_angular_lift (n : ℕ) (χ : DirichletCharacter ℂ (p ^ n)) :
    ∃ m ≤ n, ∃ ξ : FieldOnePadicPrimitiveAngularCharacter p m,
      ∀ u : ℤ_[p]ˣ, ξ.1 (fieldOnePadicUnitReduction p m u) =
        χ (fieldOnePadicUnitReduction p n u) := by
  obtain ⟨m, hmn, ξ, hξ⟩ := primitive_prime_power_lift p χ.conductor_dvd_level
    χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
  refine ⟨m, hmn, ξ, fun u => ?_⟩
  rw [hξ, χ.changeLevel_primitiveCharacter]

/-- Arbitrary continuous unit characters occur among the primitive angular characters. -/
theorem exists_primitive_unit_character (χ : ℤ_[p]ˣ →ₜ* Circle) :
    ∃ (n : ℕ) (ξ : FieldOnePadicPrimitiveAngularCharacter p n),
      ∀ u : ℤ_[p]ˣ, (χ u : ℂ) = ξ.1 (fieldOnePadicUnitReduction p n u) := by
  obtain ⟨n, θ, hθ, _⟩ := exists_unique_finite_character p χ
  let ψ : DirichletCharacter ℂ (p ^ n) := MulChar.ofUnitHom (Circle.toUnits.comp θ)
  obtain ⟨m, _, ξ, hξ⟩ := exists_primitive_angular_lift p n ψ
  refine ⟨m, ξ, fun u => ?_⟩
  rw [hξ]
  change (χ u : ℂ) = MulChar.ofUnitHom (Circle.toUnits.comp θ)
    (fieldOnePadicUnitReduction p n u : ZMod (p ^ n))
  rw [MulChar.ofUnitHom_coe]
  change (χ u : ℂ) = (θ (fieldOnePadicUnitReduction p n u) : ℂ)
  rw [hθ]

/-- The existing primitive Tate-character family exhausts all continuous unitary characters. -/
theorem exists_primitive_tate_character (χ : ℚ_[p]ˣ →ₜ* Circle) :
    ∃ (n : ℕ) (ξ : FieldOnePadicPrimitiveAngularCharacter p n),
      ∀ a : ℚ_[p]ˣ, (χ a : ℂ) = fieldOnePadicRamifiedCriticalCharacter p n ξ
        (χ (fieldOnePadicValuationUnitMulEquiv p (Multiplicative.ofAdd 1, 1))) a := by
  obtain ⟨n, ξ, hξ⟩ := exists_primitive_unit_character p (unitRestriction p χ)
  refine ⟨n, ξ, fun a => ?_⟩
  rw [character_split p χ a, Circle.coe_mul, Circle.coe_zpow, hξ]
  rfl

#print axioms exists_primitive_unit_character
#print axioms exists_primitive_tate_character

end GaloisForLFunctions.RHTower.LocalCharacters
