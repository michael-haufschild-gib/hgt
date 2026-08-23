import GaloisForLFunctions.HTGeometry.MilnorKTameValuation

/-! # Hasse classification of valuation-zero units by residue -/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped WithZero

universe u

noncomputable section

/-- Units of an integer-valued valuation ring map canonically into valuation-zero field units. -/
noncomputable def integerValuationUnitsToTameValKernel
    {K : Type u} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ))) :
    v.integerˣ →* (tameValHom v).ker :=
  MonoidHom.codRestrict
    (Units.map (algebraMap v.integer K).toMonoidHom)
    (tameValHom v).ker fun x => by
      rw [tameValHom_mem_ker_iff]
      exact Valuation.Integers.valuation_unit (Valuation.integer.integers v) x

/-- Reduction exhausts residue units already on the valuation-zero subgroup. -/
theorem tameResHom_surjective
    {K : Type u} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ))) :
    Function.Surjective (tameResHom v) := by
  intro a
  have hres : Function.Surjective (IsLocalRing.residue v.integer) :=
    IsLocalRing.residue_surjective
  obtain ⟨x, hx⟩ := IsLocalRing.surjective_units_map_of_local_ringHom
    (IsLocalRing.residue v.integer) hres hres.isLocalHom a
  refine ⟨integerValuationUnitsToTameValKernel v x, ?_⟩
  change Units.map (IsLocalRing.residue v.valuationSubring).toMonoidHom
      (tameUnit v _) = a
  rw [show tameUnit v _ = x by apply Units.ext; rfl]
  exact hx

/-- Valuation-zero field units modulo equal-residue units are the residue-field units. -/
noncomputable def tameUnitsModResidueKernelEquiv
    {K : Type u} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ))) :
    (tameValHom v).ker ⧸ (tameResHom v).ker ≃*
      (IsLocalRing.ResidueField v.integer)ˣ :=
  QuotientGroup.quotientKerEquivOfSurjective (tameResHom v)
    (tameResHom_surjective v)

@[simp] theorem tameUnitsModResidueKernelEquiv_mk
    {K : Type u} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ)))
    (x : (tameValHom v).ker) :
    tameUnitsModResidueKernelEquiv v (QuotientGroup.mk x) = tameResHom v x := by
  rfl

/-- Valuation-zero field units have equal residues exactly modulo the residue kernel. -/
theorem tameResHom_congr_hasse_iff
    {K : Type u} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ)))
    (x y : (tameValHom v).ker) :
    x * y⁻¹ ∈ (tameResHom v).ker ↔ tameResHom v x = tameResHom v y := by
  change tameResHom v (x * y⁻¹) = 1 ↔ _
  rw [map_mul, map_inv, mul_inv_eq_one]

/-- Every residue unit has a valuation-zero representative, unique modulo equal residue. -/
theorem tameResHom_exists_unique_mod_kernel
    {K : Type u} [Field K] (v : Valuation K (WithZero (Multiplicative ℤ)))
    (a : (IsLocalRing.ResidueField v.integer)ˣ) :
    ∃ x : (tameValHom v).ker,
      tameResHom v x = a ∧
      ∀ y : (tameValHom v).ker,
        tameResHom v y = a ↔ y * x⁻¹ ∈ (tameResHom v).ker := by
  obtain ⟨x, hx⟩ := tameResHom_surjective v a
  refine ⟨x, hx, fun y => ?_⟩
  rw [tameResHom_congr_hasse_iff v y x, hx]

end


end GaloisForLFunctions.HTGeometry.ABHN
