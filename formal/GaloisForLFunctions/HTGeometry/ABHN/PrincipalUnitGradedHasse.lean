import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldValuationSequence

/-! # Hasse classification of successive principal-unit layers -/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

noncomputable section

/-- The `n`th associated graded principal-unit group. -/
abbrev nonarchimedeanLocalFieldPrincipalUnitGraded
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :=
  (nonarchimedeanLocalFieldPrincipalUnitFiltration K n) ⧸
    (nonarchimedeanLocalFieldPrincipalUnitFiltration K (n + 1)).subgroupOf
      (nonarchimedeanLocalFieldPrincipalUnitFiltration K n)

/-- The first-order linearization kernel is precisely the next principal-unit layer. -/
theorem nonarchimedeanLocalFieldPrincipalUnitLinearization_ker_eq_successor
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) (hn : 0 < n) :
    (nonarchimedeanLocalFieldPrincipalUnitLinearization K n hn).ker =
      (nonarchimedeanLocalFieldPrincipalUnitFiltration K (n + 1)).subgroupOf
        (nonarchimedeanLocalFieldPrincipalUnitFiltration K n) := by
  ext x
  rw [Subgroup.mem_subgroupOf]
  exact nonarchimedeanLocalField_mem_principalUnitLinearization_ker_iff K n hn x

/-- The associated graded principal-unit group is the range of first-order linearization. -/
noncomputable def nonarchimedeanLocalFieldPrincipalUnitGradedEquivLinearizationRange
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) (hn : 0 < n) :
    nonarchimedeanLocalFieldPrincipalUnitGraded K n ≃*
      (nonarchimedeanLocalFieldPrincipalUnitLinearization K n hn).range :=
  (QuotientGroup.quotientMulEquivOfEq
    (nonarchimedeanLocalFieldPrincipalUnitLinearization_ker_eq_successor K n hn).symm).trans
      (QuotientGroup.quotientKerEquivRange
        (nonarchimedeanLocalFieldPrincipalUnitLinearization K n hn))

@[simp] theorem nonarchimedeanLocalFieldPrincipalUnitGradedEquivLinearizationRange_mk
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) (hn : 0 < n)
    (x : nonarchimedeanLocalFieldPrincipalUnitFiltration K n) :
    nonarchimedeanLocalFieldPrincipalUnitGradedEquivLinearizationRange K n hn
        (QuotientGroup.mk x) =
      ⟨nonarchimedeanLocalFieldPrincipalUnitLinearization K n hn x,
        ⟨x, rfl⟩⟩ := by
  rfl

/-- Two `Uⁿ` elements have the same linearization exactly modulo `Uⁿ⁺¹`. -/
theorem nonarchimedeanLocalFieldPrincipalUnitLinearization_congr_hasse_iff
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) (hn : 0 < n)
    (x y : nonarchimedeanLocalFieldPrincipalUnitFiltration K n) :
    x * y⁻¹ ∈
        (nonarchimedeanLocalFieldPrincipalUnitFiltration K (n + 1)).subgroupOf
          (nonarchimedeanLocalFieldPrincipalUnitFiltration K n) ↔
      nonarchimedeanLocalFieldPrincipalUnitLinearization K n hn x =
        nonarchimedeanLocalFieldPrincipalUnitLinearization K n hn y := by
  rw [← nonarchimedeanLocalFieldPrincipalUnitLinearization_ker_eq_successor K n hn]
  change nonarchimedeanLocalFieldPrincipalUnitLinearization K n hn (x * y⁻¹) = 1 ↔ _
  rw [map_mul, map_inv, mul_inv_eq_one]

/-- Every realized linearized coordinate has a representative unique modulo `Uⁿ⁺¹`. -/
theorem nonarchimedeanLocalFieldPrincipalUnitLinearization_exists_unique_mod_successor
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) (hn : 0 < n)
    (a : (nonarchimedeanLocalFieldPrincipalUnitLinearization K n hn).range) :
    ∃ x : nonarchimedeanLocalFieldPrincipalUnitFiltration K n,
      nonarchimedeanLocalFieldPrincipalUnitLinearization K n hn x = a.1 ∧
      ∀ y : nonarchimedeanLocalFieldPrincipalUnitFiltration K n,
        nonarchimedeanLocalFieldPrincipalUnitLinearization K n hn y = a.1 ↔
          y * x⁻¹ ∈
            (nonarchimedeanLocalFieldPrincipalUnitFiltration K (n + 1)).subgroupOf
              (nonarchimedeanLocalFieldPrincipalUnitFiltration K n) := by
  obtain ⟨x, hx⟩ := a.2
  refine ⟨x, hx, fun y => ?_⟩
  rw [nonarchimedeanLocalFieldPrincipalUnitLinearization_congr_hasse_iff K n hn y x, hx]

end


end GaloisForLFunctions.HTGeometry.ABHN
