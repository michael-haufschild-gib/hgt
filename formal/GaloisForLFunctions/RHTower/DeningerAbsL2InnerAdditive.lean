import GaloisForLFunctions.RHTower.DeningerL2InnerTorsion

/-!
# Additivity of the absolute `L²` inner product

Additivity in the first argument involves three algebraic numbers at once, so it is proved in the
field they generate, which is finite over `ℚ`.  Together with symmetry, vanishing on torsion and
independence of the field of definition, this is the full set of properties the form needs in
order to descend to the Kummer group and extend to `𝒢 ⊗ ℚ`.

* `deningerAbsL2Inner_mul_left` : additivity in the first argument.
* `deningerAbsL2Inner_mul_right` : additivity in the second argument.
-/

namespace RHTower

open NumberField Module

open scoped IntermediateField

section AbsoluteAdditive

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

instance deningerAdjoinTriple_numberField (α β γ : F) : NumberField ℚ⟮α, β, γ⟯ where
  to_finiteDimensional := by
    have h : Module.Finite ℚ ℚ⟮α, β, γ⟯ := by
      refine IntermediateField.finiteDimensional_adjoin (K := ℚ) (S := {α, β, γ}) ?_
      intro z _
      exact (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
    convert h using 2
    exact Subsingleton.elim _ _

/-- **The absolute inner product is additive in the first argument.** -/
theorem deningerAbsL2Inner_mul_left {α α' β : F} (hα : α ≠ 0) (hα' : α' ≠ 0) (hβ : β ≠ 0) :
    deningerAbsL2Inner (α * α') β = deningerAbsL2Inner α β + deningerAbsL2Inner α' β := by
  have hαm : α ∈ (ℚ⟮α, α', β⟯ : IntermediateField ℚ F) :=
    IntermediateField.subset_adjoin ℚ {α, α', β} (by simp)
  have hα'm : α' ∈ (ℚ⟮α, α', β⟯ : IntermediateField ℚ F) :=
    IntermediateField.subset_adjoin ℚ {α, α', β} (by simp)
  have hβm : β ∈ (ℚ⟮α, α', β⟯ : IntermediateField ℚ F) :=
    IntermediateField.subset_adjoin ℚ {α, α', β} (by simp)
  have hprodm : α * α' ∈ (ℚ⟮α, α', β⟯ : IntermediateField ℚ F) := mul_mem hαm hα'm
  rw [deningerAbsL2Inner_intermediateField (ℚ⟮α, α', β⟯ : IntermediateField ℚ F) hprodm hβm
      (mul_ne_zero hα hα') hβ,
    deningerAbsL2Inner_intermediateField (ℚ⟮α, α', β⟯ : IntermediateField ℚ F) hαm hβm hα hβ,
    deningerAbsL2Inner_intermediateField (ℚ⟮α, α', β⟯ : IntermediateField ℚ F) hα'm hβm hα' hβ,
    deningerNormalizedL2Inner, deningerNormalizedL2Inner, deningerNormalizedL2Inner,
    show (⟨α * α', hprodm⟩ : (ℚ⟮α, α', β⟯ : IntermediateField ℚ F))
        = (⟨α, hαm⟩ : (ℚ⟮α, α', β⟯ : IntermediateField ℚ F)) * ⟨α', hα'm⟩ from rfl,
    deningerL2Inner_mul_left (deningerIntermediate_ne_zero hαm hα)
      (deningerIntermediate_ne_zero hα'm hα'),
    add_div]

/-- **The absolute inner product is additive in the second argument.** -/
theorem deningerAbsL2Inner_mul_right {α β β' : F} (hα : α ≠ 0) (hβ : β ≠ 0) (hβ' : β' ≠ 0) :
    deningerAbsL2Inner α (β * β') = deningerAbsL2Inner α β + deningerAbsL2Inner α β' := by
  rw [deningerAbsL2Inner_comm hα (mul_ne_zero hβ hβ'),
    deningerAbsL2Inner_mul_left hβ hβ' hα,
    deningerAbsL2Inner_comm hβ hα, deningerAbsL2Inner_comm hβ' hα]

end AbsoluteAdditive

end RHTower
