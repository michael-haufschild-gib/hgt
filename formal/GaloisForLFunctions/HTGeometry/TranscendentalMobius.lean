import GaloisForLFunctions.HTGeometry.OrdinaryLuroth
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Möbius form of a generating element over a transcendental

Transporting the degree-one Lüroth theorem across the isomorphism
`RatFunc C ≃ₐ[C] C⟮y⟯` (`algEquivOfTranscendental`, valid for `y` transcendental) gives its
abstract-field form: if `z` lies in `C(y)` and `y` lies in `C(z)` (so `z` generates `C(y)`), then
`z` is a Möbius transform of `y`,

`z · (c y + d) = a y + b`,  `a d - b c ≠ 0`,  `a, b, c, d ∈ C`.

This is the connector that turns the differential order-zero rigidity (`σ y ∈ C(y)`,
`σ⁻¹ y ∈ C(y)`) into the explicit `PGL₂` element of the clock-character classification.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open RatFunc

variable {C E : Type*} [Field C] [Field E] [Algebra C E]

/-- Evaluation of rational functions at a transcendental element `y`, as a `C`-algebra hom
`RatFunc C →ₐ[C] E` sending `X` to `y`. -/
def ratFuncEval (y : E) (hy : Transcendental C y) : RatFunc C →ₐ[C] E :=
  (IntermediateField.adjoin C {y}).val.comp (RatFunc.algEquivOfTranscendental y hy).toAlgHom

theorem ratFuncEval_injective (y : E) (hy : Transcendental C y) :
    Function.Injective (ratFuncEval y hy) :=
  (IntermediateField.adjoin C {y}).val.injective.comp
    (RatFunc.algEquivOfTranscendental y hy).injective

@[simp] theorem ratFuncEval_X (y : E) (hy : Transcendental C y) :
    ratFuncEval y hy RatFunc.X = y := by
  rw [ratFuncEval, AlgHom.comp_apply, AlgEquiv.coe_algHom]
  exact RatFunc.algEquivOfTranscendental_X y hy

@[simp] theorem ratFuncEval_C (y : E) (hy : Transcendental C y) (c : C) :
    ratFuncEval y hy (RatFunc.C c) = algebraMap C E c := by
  rw [← RatFunc.algebraMap_eq_C, AlgHom.commutes]

/-- **Möbius form of a generating element.**  If `z ∈ C(y)` and `y ∈ C(z)` with `y` transcendental,
then `z` is a fractional-linear transform of `y` with coefficients in `C`. -/
theorem adjoin_generator_mobius {y z : E} (hy : Transcendental C y)
    (hz : z ∈ IntermediateField.adjoin C {y})
    (hyin : y ∈ IntermediateField.adjoin C {z}) :
    ∃ a b c d : C, a * d - b * c ≠ 0 ∧
      z * (algebraMap C E c * y + algebraMap C E d)
        = algebraMap C E a * y + algebraMap C E b := by
  set φ := RatFunc.algEquivOfTranscendental y hy with hφ
  set g : RatFunc C := φ.symm ⟨z, hz⟩ with hgdef
  have hevg : ratFuncEval y hy g = z := by
    simp only [ratFuncEval, AlgHom.comp_apply, AlgEquiv.coe_algHom,
      hgdef, hφ, AlgEquiv.apply_symm_apply]
    rfl
  -- `g` generates `RatFunc C`
  have hggen : IntermediateField.adjoin C {g} = ⊤ := by
    have hXmem : (RatFunc.X : RatFunc C) ∈ IntermediateField.adjoin C {g} := by
      have hmem : ratFuncEval y hy RatFunc.X
          ∈ IntermediateField.map (ratFuncEval y hy)
            (IntermediateField.adjoin C {g}) := by
        rw [IntermediateField.adjoin_map]
        simp only [Set.image_singleton, hevg, ratFuncEval_X]
        exact hyin
      rw [IntermediateField.mem_map] at hmem
      obtain ⟨w, hw, hwx⟩ := hmem
      rwa [ratFuncEval_injective y hy hwx] at hw
    rw [← top_le_iff, ← RatFunc.adjoin_X]
    exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hXmem)
  obtain ⟨a, b, c, d, hdet, hrel⟩ := ratFunc_generator_mobius hggen
  refine ⟨a, b, c, d, hdet, ?_⟩
  have hpush := congrArg (ratFuncEval y hy) hrel
  simpa only [map_mul, map_add, ratFuncEval_C, ratFuncEval_X, hevg] using hpush

/-- **Möbius form from adjoin membership.**  A `C`-algebra automorphism `σ` of `E` that maps the
generator `y` and its `σ`-preimage back into `C(y)` acts on `y` by a fractional-linear transform.
This is the automorphism-level engine of both the differential constraint (§1) and the semilinear
clock (§3): all that is used is that `σ` preserves the rational subfield `C(y)`. -/
theorem algEquiv_generator_mobius_of_mem
    (σ : E ≃ₐ[C] E) {y : E} (hy : Transcendental C y)
    (hz : σ y ∈ IntermediateField.adjoin C {y})
    (hsymm : σ.symm y ∈ IntermediateField.adjoin C {y}) :
    ∃ a b c d : C, a * d - b * c ≠ 0 ∧
      σ y * (algebraMap C E c * y + algebraMap C E d)
        = algebraMap C E a * y + algebraMap C E b := by
  have hyin : y ∈ IntermediateField.adjoin C {σ y} := by
    have hmap : IntermediateField.map σ.toAlgHom (IntermediateField.adjoin C {y})
        = IntermediateField.adjoin C {σ y} := by
      rw [IntermediateField.adjoin_map]; simp
    rw [← hmap, IntermediateField.mem_map]
    exact ⟨σ.symm y, hsymm, by simp⟩
  exact adjoin_generator_mobius hy hz hyin

end GaloisForLFunctions.HTGeometry
