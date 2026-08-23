import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldValuationSequence

/-! # Hasse classification of the first local unit quotient -/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

@[simp] theorem nonarchimedeanLocalFieldUnitsModPrincipalUnitsEquivResidueUnits_mk
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (x : (ValuativeRel.valuation K).integerˣ) :
    nonarchimedeanLocalFieldUnitsModPrincipalUnitsEquivResidueUnits K
        (QuotientGroup.mk x) = nonarchimedeanLocalFieldReductionUnits K x := by
  rfl

/-- Integral units have equal residue exactly modulo principal units. -/
theorem nonarchimedeanLocalFieldReductionUnits_congr_hasse_iff
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (x y : (ValuativeRel.valuation K).integerˣ) :
    x * y⁻¹ ∈ nonarchimedeanLocalFieldPrincipalUnitGroup K ↔
      nonarchimedeanLocalFieldReductionUnits K x =
        nonarchimedeanLocalFieldReductionUnits K y := by
  change x * y⁻¹ ∈ (nonarchimedeanLocalFieldReductionUnits K).ker ↔ _
  rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]

/-- Every residue unit has an integral representative, unique modulo principal units. -/
theorem nonarchimedeanLocalFieldReductionUnits_exists_unique_mod_principal
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (a : (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)ˣ) :
    ∃ x : (ValuativeRel.valuation K).integerˣ,
      nonarchimedeanLocalFieldReductionUnits K x = a ∧
      ∀ y : (ValuativeRel.valuation K).integerˣ,
        nonarchimedeanLocalFieldReductionUnits K y = a ↔
          y * x⁻¹ ∈ nonarchimedeanLocalFieldPrincipalUnitGroup K := by
  obtain ⟨x, hx⟩ := nonarchimedeanLocalFieldReductionUnits_surjective K a
  refine ⟨x, hx, fun y => ?_⟩
  rw [nonarchimedeanLocalFieldReductionUnits_congr_hasse_iff K y x, hx]

end GaloisForLFunctions.HTGeometry.ABHN
