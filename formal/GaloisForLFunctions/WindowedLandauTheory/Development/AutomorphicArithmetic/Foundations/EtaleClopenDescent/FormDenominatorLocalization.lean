import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteEtaleFormTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GenericChartForms

/-! Pullback of differential forms respects towers, and regularity
after localization yields a single denominator in the base. -/

noncomputable section

open GlobalTheory.SchemeCohomology
open scoped GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

variable {k A C E : Type*} [CommRing k] [CommRing A] [CommRing C] [CommRing E]
  [Algebra k A] [Algebra k C] [Algebra k E] [Algebra A C] [Algebra C E] [Algebra A E]
  [IsScalarTower k A C] [IsScalarTower k C E] [IsScalarTower k A E] [IsScalarTower A C E]

/-- Extending a form through an intermediate algebra agrees with direct
extension to the top algebra. -/
theorem algebraFormPullback_trans (p : ℕ) (u : ExteriorDifferentials k A p) :
    algebraFormPullback k C E p (algebraFormPullback k A C p u) =
      algebraFormPullback k A E p u := by
  let f := IsScalarTower.toAlgHom k A C
  let g := IsScalarTower.toAlgHom k C E
  let h := IsScalarTower.toAlgHom k A E
  have he : g.comp f = h := AlgHom.ext fun a => (IsScalarTower.algebraMap_apply A C E a).symm
  rw [algebraFormPullback_eq_map k C E g rfl, algebraFormPullback_eq_map k A C f rfl,
    algebraFormPullback_eq_map k A E h rfl, ← ExteriorDifferentials.map_comp, he]

/-- A form regular over a localization acquires a regular preimage
over the original ring after clearing one localized denominator. -/
private theorem exists_smul_mem_formRange_of_localization (S : Submonoid A) [IsLocalization S C] {p : ℕ}
    {ω : ExteriorDifferentials k E p} (hω : ω ∈ LinearMap.range (algebraFormPullback k C E p)) :
    ∃ s : S, (s : A) • ω ∈ LinearMap.range (algebraFormPullback k A E p) := by
  obtain ⟨u, hu⟩ := hω
  letI : Algebra.FormallyEtale A C := .of_isLocalization S
  let f := algebraFormPullback k A C p
  letI : IsLocalizedModule S f := (isLocalizedModule_iff_isBaseChange S C f).mpr
    (algebraFormPullback_isBaseChange k A C p)
  obtain ⟨⟨v, s⟩, hv⟩ := IsLocalizedModule.surj S f u
  refine ⟨s, v, ?_⟩
  change algebraFormPullback k A E p v = (s : A) • ω
  calc
    _ = algebraFormPullback k C E p (algebraFormPullback k A C p v) :=
      (algebraFormPullback_trans p v).symm
    _ = algebraFormPullback k C E p ((s : A) • u) := congrArg (algebraFormPullback k C E p) hv.symm
    _ = _ := by
      rw [← IsScalarTower.algebraMap_smul C (s : A) u, map_smul, hu,
        ← IsScalarTower.algebraMap_smul E (algebraMap A C (s : A)) ω,
        ← IsScalarTower.algebraMap_apply A C E, IsScalarTower.algebraMap_smul E (s : A) ω]

/-- A form is regular over a localization exactly when a denominator
from the localizing set makes it regular over the original ring. -/
theorem mem_formRange_localization_iff (S : Submonoid A) [IsLocalization S C] {p : ℕ}
    (ω : ExteriorDifferentials k E p) :
    ω ∈ LinearMap.range (algebraFormPullback k C E p) ↔
      ∃ s : S, (s : A) • ω ∈ LinearMap.range (algebraFormPullback k A E p) := by
  refine ⟨exists_smul_mem_formRange_of_localization S, ?_⟩
  rintro ⟨s, v, hv⟩
  let u := (IsLocalization.map_units C s).unit
  have hu : (u : C) = algebraMap A C (s : A) := (IsLocalization.map_units C s).unit_spec
  have hinv : algebraMap C E (↑u⁻¹ : C) * algebraMap A E (s : A) = 1 := by
    rw [IsScalarTower.algebraMap_apply A C E, ← hu, ← map_mul, Units.inv_mul, map_one]
  refine ⟨(↑u⁻¹ : C) • algebraFormPullback k A C p v, ?_⟩
  rw [map_smul, algebraFormPullback_trans, hv, ← IsScalarTower.algebraMap_smul E (s : A) ω,
    ← IsScalarTower.algebraMap_smul E (↑u⁻¹ : C), smul_smul, hinv, one_smul]

end GlobalTheory.PD

namespace GlobalTheory.PD

open GlobalTheory.CechDR

/-- The regular rational forms of a fixed degree are exactly the image
of chart forms under pullback to the function field. -/
theorem mem_omB_iff_pullback_range {k E : Type*} [Field k] [Field E] [Algebra k E]
    (B : Subalgebra k E) {p : ℕ} (w : ExteriorDifferentials k E p) :
    (w : DR k E) ∈ omB k E B p ↔ w ∈ LinearMap.range (algebraFormPullback k B E p) := by
  rw [← range_genericForm]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, Subtype.ext ?_⟩
    exact (congrArg Subtype.val (algebraFormPullback_eq_map k B E B.val rfl p v)).trans hv
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    exact congrArg Subtype.val ((algebraFormPullback_eq_map k B E B.val rfl p v).symm.trans hv)

end GlobalTheory.PD
