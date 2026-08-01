import GaloisForLFunctions.HTGeometry.CenteredGenericCoefficients

/-!
# The centered roots generate the centered field

Read inside the field they generate, the centered roots generate everything over the constants,
hence also over the field the centered coefficients generate.

So an automorphism of the centered field over the centered coefficients is determined by its values
on the centered roots: the elements on which two such automorphisms agree form an intermediate
field, and it contains the generators.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Polynomial

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

/-- The centered roots, read inside the field they generate. -/
noncomputable def centeredRootIn (K : Type*) [Field K] [CharZero K] (d : ℕ) (i : Fin d) :
    centeredField K d :=
  ⟨centeredRoot K d i, centeredRoot_mem_centeredField i⟩

@[simp]
theorem coe_centeredRootIn (i : Fin d) :
    ((centeredRootIn K d i : centeredField K d) : SymmetricRationalField K d) =
      centeredRoot K d i := rfl

/-- **The centered roots generate the centered field over the constants.** -/
theorem adjoin_centeredRootIn_eq_top :
    IntermediateField.adjoin K (Set.range (centeredRootIn K d)) = ⊤ := by
  refine le_antisymm le_top fun x _ => ?_
  have hmap : (IntermediateField.adjoin K (Set.range (centeredRootIn K d))).map
      (centeredField K d).val = centeredField K d := by
    rw [IntermediateField.adjoin_map, ← Set.range_comp]
    congr 1
  have hx : ((x : SymmetricRationalField K d)) ∈
      (IntermediateField.adjoin K (Set.range (centeredRootIn K d))).map
        (centeredField K d).val := by
    rw [hmap]
    exact x.2
  obtain ⟨y, hy, hyx⟩ := hx
  have hyeq : y = x := Subtype.ext hyx
  rwa [← hyeq]

set_option maxHeartbeats 2000000 in
/-- **The centered roots generate the centered field over the centered coefficients.** -/
theorem adjoin_centeredRootIn_over_coeff_eq_top :
    IntermediateField.adjoin (centeredCoeffField K d) (Set.range (centeredRootIn K d)) = ⊤ := by
  refine le_antisymm le_top fun x _ => ?_
  have hx : x ∈ IntermediateField.adjoin K (Set.range (centeredRootIn K d)) := by
    rw [adjoin_centeredRootIn_eq_top]
    exact IntermediateField.mem_top
  have hle : IntermediateField.adjoin K (Set.range (centeredRootIn K d)) ≤
      (IntermediateField.adjoin (centeredCoeffField K d)
        (Set.range (centeredRootIn K d))).restrictScalars K := by
    rw [IntermediateField.adjoin_le_iff]
    exact fun z hz => IntermediateField.subset_adjoin _ _ hz
  have h2 := hle hx
  rwa [IntermediateField.mem_restrictScalars] at h2

/-- The elements on which two automorphisms agree. -/
noncomputable def centeredAlgEquivEqualizer
    (σ τ : (centeredField K d) ≃ₐ[centeredCoeffField K d] (centeredField K d)) :
    IntermediateField (centeredCoeffField K d) (centeredField K d) where
  carrier := {x | σ x = τ x}
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]
  one_mem' := by simp only [Set.mem_setOf_eq, map_one]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_add, map_add, ha, hb]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [map_inv₀, map_inv₀, ha]
  algebraMap_mem' := by
    intro c
    simp only [Set.mem_setOf_eq, AlgEquiv.commutes]

set_option maxHeartbeats 2000000 in
/-- **An automorphism over the centered coefficients is determined by its values on the centered
roots.** -/
theorem centeredAlgEquiv_ext
    {σ τ : (centeredField K d) ≃ₐ[centeredCoeffField K d] (centeredField K d)}
    (h : ∀ i : Fin d, σ (centeredRootIn K d i) = τ (centeredRootIn K d i)) : σ = τ := by
  have hle : IntermediateField.adjoin (centeredCoeffField K d)
      (Set.range (centeredRootIn K d)) ≤ centeredAlgEquivEqualizer σ τ := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact h i
  rw [adjoin_centeredRootIn_over_coeff_eq_top] at hle
  refine AlgEquiv.ext fun x => ?_
  exact hle (IntermediateField.mem_top (x := x))

end GaloisForLFunctions.HTGeometry
