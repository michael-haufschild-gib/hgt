import GaloisForLFunctions.HTGeometry.FundamentalGroupProduct
import GaloisForLFunctions.HTGeometry.FundamentalGroupTopologicalGroup
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Fundamental group generators of the complex torus chart

The exponential universal cover makes the fundamental group of `ℂˣ` cyclic.  Product path
classes and contractibility of affine space then give two explicit generators for
`(ℂˣ)² × ℂᵏ`.  Every loop is a product of integer powers of these two coordinate loops.
-/

namespace GaloisForLFunctions.HTGeometry

open Path

noncomputable section

/-- Period lattice of the complex exponential. -/
abbrev ComplexExponentialPeriodLattice :=
  AddSubgroup.zmultiples (2 * Real.pi * Complex.I)

/-- Complex exponential with codomain written as the unit group. -/
def complexExpUnits : ℂ → Units ℂ :=
  (unitsHomeomorphNeZero (G₀ := ℂ)).symm ∘
    fun z ↦ (⟨z.exp, z.exp_ne_zero⟩ : {w : ℂ // w ≠ 0})

/-- The exponential map to `ℂˣ` is the quotient universal cover by its period lattice. -/
theorem complexExpUnits_isAddQuotientCoveringMap :
    IsAddQuotientCoveringMap complexExpUnits ComplexExponentialPeriodLattice := by
  exact Complex.isAddQuotientCoveringMap_exp.homeomorph_comp
    (unitsHomeomorphNeZero (G₀ := ℂ)).symm

/-- Zero in the universal cover lies over the unit basepoint. -/
noncomputable def complexExpUnitsBasepoint : complexExpUnits ⁻¹' {(1 : Units ℂ)} :=
  ⟨0, by
    apply (unitsHomeomorphNeZero (G₀ := ℂ)).injective
    simp only [complexExpUnits, Function.comp_apply, Homeomorph.apply_symm_apply,
      Complex.exp_zero]
    apply Subtype.ext
    rfl⟩

/-- The fundamental group of `ℂˣ` is cyclic, obtained from the exponential universal cover. -/
theorem isCyclic_fundamentalGroup_complexUnits :
    IsCyclic (FundamentalGroup (Units ℂ) 1) := by
  letI : IsAddCyclic ComplexExponentialPeriodLattice :=
    AddSubgroup.isAddCyclic_zmultiples _
  letI : IsCyclic (Multiplicative ComplexExponentialPeriodLattice) := inferInstance
  have hop : IsCyclic ((Multiplicative ComplexExponentialPeriodLattice)ᵐᵒᵖ) :=
    (MulOpposite.opMulEquiv.isCyclic).mp inferInstance
  exact ((complexExpUnits_isAddQuotientCoveringMap.fundamentalGroupEquiv
    complexExpUnitsBasepoint).isCyclic).mpr hop

/-- Canonical-by-choice generator of the fundamental group of `ℂˣ`. -/
noncomputable def complexUnitsFundamentalGenerator : FundamentalGroup (Units ℂ) 1 :=
  (isCyclic_iff_exists_zpowers_eq_top.mp
    isCyclic_fundamentalGroup_complexUnits).choose

theorem zpowers_complexUnitsFundamentalGenerator :
    Subgroup.zpowers complexUnitsFundamentalGenerator = ⊤ :=
  (isCyclic_iff_exists_zpowers_eq_top.mp
    isCyclic_fundamentalGroup_complexUnits).choose_spec

/-- The affine factor, despite its multiplicative presentation, is simply connected. -/
theorem simplyConnectedSpace_complexAffineMultiplicative (k : ℕ) :
    SimplyConnectedSpace (Multiplicative (Fin k → ℂ)) := by
  letI : ContractibleSpace (Multiplicative (Fin k → ℂ)) :=
    (inferInstance : ContractibleSpace (Fin k → ℂ))
  infer_instance

/-- Fundamental group of the torus-affine chart is the product of its two torus factors. -/
noncomputable def fundamentalGroupComplexTorusAffineChartEquiv (k : ℕ) :
    FundamentalGroup (ComplexTorusAffineChart k) 1 ≃*
      FundamentalGroup (Units ℂ) 1 × FundamentalGroup (Units ℂ) 1 := by
  letI : SimplyConnectedSpace (Multiplicative (Fin k → ℂ)) :=
    simplyConnectedSpace_complexAffineMultiplicative k
  letI : Unique (FundamentalGroup (Multiplicative (Fin k → ℂ)) 1) :=
    { default := 1
      uniq := fun _ ↦ Subsingleton.elim _ _ }
  exact
    (fundamentalGroupProdMulEquiv (1 : Units ℂ) (1 : Units ℂ ×
      Multiplicative (Fin k → ℂ))).symm |>.trans
      ((MulEquiv.refl (FundamentalGroup (Units ℂ) 1)).prodCongr
        (fundamentalGroupProdMulEquiv (1 : Units ℂ)
          (1 : Multiplicative (Fin k → ℂ))).symm) |>.trans
      ((MulEquiv.refl (FundamentalGroup (Units ℂ) 1)).prodCongr MulEquiv.prodUnique)

/-- Loop around the first torus coordinate. -/
noncomputable def torusChartFirstFundamentalGenerator (k : ℕ) :
    FundamentalGroup (ComplexTorusAffineChart k) 1 :=
  (fundamentalGroupComplexTorusAffineChartEquiv k).symm
    (complexUnitsFundamentalGenerator, 1)

/-- Loop around the second torus coordinate. -/
noncomputable def torusChartSecondFundamentalGenerator (k : ℕ) :
    FundamentalGroup (ComplexTorusAffineChart k) 1 :=
  (fundamentalGroupComplexTorusAffineChartEquiv k).symm
    (1, complexUnitsFundamentalGenerator)

/-- **Exact loop exponent decomposition.**  Every chart loop is a product of integer powers of
the two coordinate loops. -/
theorem exists_eq_zpow_torusChartFundamentalGenerators (k : ℕ)
    (g : FundamentalGroup (ComplexTorusAffineChart k) 1) :
    ∃ a b : ℤ, g = torusChartFirstFundamentalGenerator k ^ a *
      torusChartSecondFundamentalGenerator k ^ b := by
  let e := fundamentalGroupComplexTorusAffineChartEquiv k
  have h₁ : ∃ a : ℤ, (e g).1 = complexUnitsFundamentalGenerator ^ a := by
    have hmem : (e g).1 ∈ Subgroup.zpowers complexUnitsFundamentalGenerator := by
      rw [zpowers_complexUnitsFundamentalGenerator]
      exact Subgroup.mem_top _
    obtain ⟨a, ha⟩ := hmem
    exact ⟨a, ha.symm⟩
  have h₂ : ∃ b : ℤ, (e g).2 = complexUnitsFundamentalGenerator ^ b := by
    have hmem : (e g).2 ∈ Subgroup.zpowers complexUnitsFundamentalGenerator := by
      rw [zpowers_complexUnitsFundamentalGenerator]
      exact Subgroup.mem_top _
    obtain ⟨b, hb⟩ := hmem
    exact ⟨b, hb.symm⟩
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  have hfirst : e (torusChartFirstFundamentalGenerator k) =
      (complexUnitsFundamentalGenerator, 1) := by
    simp [e, torusChartFirstFundamentalGenerator]
  have hsecond : e (torusChartSecondFundamentalGenerator k) =
      (1, complexUnitsFundamentalGenerator) := by
    simp [e, torusChartSecondFundamentalGenerator]
  refine ⟨a, b, e.injective ?_⟩
  rw [map_mul, map_zpow, map_zpow, hfirst, hsecond]
  apply Prod.ext
  · simpa using ha
  · simpa using hb

/-- Every group-valued monodromy representation of the chart is determined by two exponent
images. -/
theorem map_eq_zpow_torusChartFundamentalGenerators
    {H : Type*} [Group H] (k : ℕ)
    (φ : FundamentalGroup (ComplexTorusAffineChart k) 1 →* H)
    (g : FundamentalGroup (ComplexTorusAffineChart k) 1) :
    ∃ a b : ℤ, φ g = φ (torusChartFirstFundamentalGenerator k) ^ a *
      φ (torusChartSecondFundamentalGenerator k) ^ b := by
  obtain ⟨a, b, rfl⟩ := exists_eq_zpow_torusChartFundamentalGenerators k g
  refine ⟨a, b, ?_⟩
  rw [map_mul, map_zpow, map_zpow]

end

end GaloisForLFunctions.HTGeometry
