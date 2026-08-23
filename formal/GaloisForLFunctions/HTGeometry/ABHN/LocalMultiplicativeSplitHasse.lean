import GaloisForLFunctions.HTGeometry.SplitSurjectiveHasse
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldValuationSequence

/-! # Split Hasse coordinates for local multiplicative groups -/

namespace GaloisForLFunctions.HTGeometry.ABHN

open GaloisForLFunctions.HTGeometry

universe u v

noncomputable section

/-- A residue datum splits field units into valuation and valuation-zero coordinates. -/
noncomputable def residueDataUnitsEquivValuationProdKernel
    {K : Type u} [Field K] {k : Type v} [Field k] (D : ResidueData K k) :
    Kˣ ≃* Multiplicative ℤ × D.val.ker :=
  splitSurjectiveCommGroupHomEquivProdKer D.val
    (residueDataValuationSection D) (residueDataValuationSection_rightInverse D)

@[simp] theorem residueDataUnitsEquivValuationProdKernel_fst
    {K : Type u} [Field K] {k : Type v} [Field k] (D : ResidueData K k) (x : Kˣ) :
    (residueDataUnitsEquivValuationProdKernel D x).1 = D.val x := by
  rfl

@[simp] theorem residueDataUnitsEquivValuationProdKernel_snd
    {K : Type u} [Field K] {k : Type v} [Field k] (D : ResidueData K k) (x : Kˣ) :
    (residueDataUnitsEquivValuationProdKernel D x).2.1 = D.unitPart x := by
  simp [residueDataUnitsEquivValuationProdKernel,
    splitSurjectiveCommGroupHomEquivProdKer, residueDataValuationSection,
    ResidueData.unitPart, ResidueData.val', TameData.v]

/-- Valuation and unit part jointly detect equality of field units. -/
theorem residueDataUnits_congr_hasse_iff
    {K : Type u} [Field K] {k : Type v} [Field k] (D : ResidueData K k) (x y : Kˣ) :
    D.val x = D.val y ∧ D.unitPart x = D.unitPart y ↔ x = y := by
  let e := residueDataUnitsEquivValuationProdKernel D
  constructor
  · rintro ⟨hv, hu⟩
    apply e.injective
    apply Prod.ext hv
    apply Subtype.ext
    simpa [e] using hu
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- At every finite Dedekind place, units split into valuation and local-unit coordinates. -/
noncomputable def finitePlaceUnitsEquivValuationProdKernel
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    (L : Type v) [Field L] [Algebra R L] [IsFractionRing R L]
    (p : IsDedekindDomain.HeightOneSpectrum R) :
    Lˣ ≃* Multiplicative ℤ × (residueDataAtPlace L p).val.ker :=
  residueDataUnitsEquivValuationProdKernel (residueDataAtPlace L p)

/-- A nonarchimedean local field splits into integer valuation and valuation-zero units. -/
noncomputable def nonarchimedeanLocalFieldUnitsEquivValuationProdKernel
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    Kˣ ≃* Multiplicative ℤ × (nonarchimedeanLocalFieldResidueData K).val.ker :=
  residueDataUnitsEquivValuationProdKernel (nonarchimedeanLocalFieldResidueData K)

/-- Integral local units split into Teichmüller residue units and principal units. -/
noncomputable def nonarchimedeanIntegralUnitsEquivResidueProdPrincipal
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    (ValuativeRel.valuation K).integerˣ ≃*
      (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer)ˣ ×
        nonarchimedeanLocalFieldPrincipalUnitGroup K :=
  splitSurjectiveCommGroupHomEquivProdKer
    (nonarchimedeanLocalFieldReductionUnits K)
    (nonarchimedeanLocalFieldTeichmullerUnitHom K)
    (nonarchimedeanLocalFieldReductionUnits_teichmuller K)

@[simp] theorem nonarchimedeanIntegralUnitsEquivResidueProdPrincipal_fst
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (x : (ValuativeRel.valuation K).integerˣ) :
    (nonarchimedeanIntegralUnitsEquivResidueProdPrincipal K x).1 =
      nonarchimedeanLocalFieldReductionUnits K x := by
  rfl

@[simp] theorem nonarchimedeanIntegralUnitsEquivResidueProdPrincipal_snd
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (x : (ValuativeRel.valuation K).integerˣ) :
    (nonarchimedeanIntegralUnitsEquivResidueProdPrincipal K x).2.1 =
      x * (nonarchimedeanLocalFieldTeichmullerUnitHom K
        (nonarchimedeanLocalFieldReductionUnits K x))⁻¹ := by
  rfl

/-- Every integral local unit is its Teichmüller coordinate times its principal coordinate. -/
theorem nonarchimedeanIntegralUnit_split_hasse
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (x : (ValuativeRel.valuation K).integerˣ) :
    x = nonarchimedeanLocalFieldTeichmullerUnitHom K
        (nonarchimedeanIntegralUnitsEquivResidueProdPrincipal K x).1 *
      (nonarchimedeanIntegralUnitsEquivResidueProdPrincipal K x).2.1 := by
  rw [mul_comm]
  exact (nonarchimedeanIntegralUnitsEquivResidueProdPrincipal K).symm_apply_apply x |>.symm

/-- Residue and principal coordinates jointly detect equality of integral local units. -/
theorem nonarchimedeanIntegralUnits_congr_hasse_iff
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (x y : (ValuativeRel.valuation K).integerˣ) :
    nonarchimedeanLocalFieldReductionUnits K x =
        nonarchimedeanLocalFieldReductionUnits K y ∧
      x * (nonarchimedeanLocalFieldTeichmullerUnitHom K
          (nonarchimedeanLocalFieldReductionUnits K x))⁻¹ =
        y * (nonarchimedeanLocalFieldTeichmullerUnitHom K
          (nonarchimedeanLocalFieldReductionUnits K y))⁻¹ ↔ x = y :=
  splitSurjectiveCommGroupHom_congr_hasse_iff
    (nonarchimedeanLocalFieldReductionUnits K)
    (nonarchimedeanLocalFieldTeichmullerUnitHom K) x y

end


end GaloisForLFunctions.HTGeometry.ABHN
