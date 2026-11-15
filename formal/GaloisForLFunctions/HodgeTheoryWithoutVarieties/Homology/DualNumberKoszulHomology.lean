import GaloisForLFunctions.HodgeTheoryWithoutVarieties.Homology.CommonFactorShear
import GaloisForLFunctions.HTGeometry.DualNumberResidueQuotient

/-!
# Koszul homology over the doubled residue field

For the pair `(εa,εb)` over `K[ε]/(ε²)`, the closed generator and the
annihilator each contribute one residue-field copy to degree-one homology.
This applies the common-factor shear to the corpus's exact dual-number
residue sequence and exhibits the term lost by imposing regularity.
-/

noncomputable section
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties
variable {K : Type*} [Field K]

local instance dualKoszulResidueModule : Module (DualNumber K) K :=
  Module.compHom K (TrivSqZeroExt.fstHom K K K).toRingHom

/-- Multiplication by `ε` kills precisely the residue kernel. -/
theorem dualKoszul_annihilator_eq_residue_ker :
    commonFactorAnnihilator (DualNumber.eps : DualNumber K) =
      LinearMap.ker (dualNumberResidue (K := K)) := by
  ext x
  change dualNumberEpsMul x = 0 ↔ dualNumberResidue x = 0
  rw [dualNumberEpsMul_eq_socle_comp_residue, LinearMap.comp_apply]
  exact ⟨fun h => dualNumberSocleInclusion_injective (h.trans (map_zero _).symm),
    fun h => by rw [h, map_zero]⟩

/-- The principal epsilon ideal is the square-zero socle. -/
theorem dualKoszul_span_eq_socle_range :
    (Ideal.span ({DualNumber.eps} : Set (DualNumber K)) : Submodule (DualNumber K) (DualNumber K)) =
      LinearMap.range (dualNumberSocleInclusion (K := K)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hx
    refine ⟨dualNumberResidue y, ?_⟩
    rw [← LinearMap.comp_apply, ← dualNumberEpsMul_eq_socle_comp_residue]
    exact hy
  · rintro ⟨y, rfl⟩
    apply Ideal.mem_span_singleton.mpr
    refine ⟨TrivSqZeroExt.inl y, ?_⟩
    change dualNumberEpsMul (TrivSqZeroExt.inl y) = dualNumberSocleInclusion y
    rw [dualNumberEpsMul_eq_socle_comp_residue, LinearMap.comp_apply]
    rfl

/-- The epsilon annihilator is one copy of the residue field. -/
def dualKoszulAnnihilatorEquiv :
    commonFactorAnnihilator (DualNumber.eps : DualNumber K) ≃ₗ[DualNumber K] K := by
  let f : K →ₗ[DualNumber K] commonFactorAnnihilator (DualNumber.eps : DualNumber K) :=
    (dualNumberSocleInclusion (K := K)).codRestrict _ fun y => by
      rw [dualKoszul_annihilator_eq_residue_ker]
      exact (dualNumberSocle_range_eq_residue_ker (K := K)) ▸ ⟨y, rfl⟩
  refine (LinearEquiv.ofBijective f ⟨?_, ?_⟩).symm
  · intro x y h
    exact dualNumberSocleInclusion_injective (congrArg Subtype.val h)
  · intro x
    have hx := x.property
    rw [dualKoszul_annihilator_eq_residue_ker,
      ← dualNumberSocle_range_eq_residue_ker] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext hy⟩

/-- Degree-one homology has two residue-field summands, for every pair of units. -/
def dualNumberKoszulH1Equiv (a b : (DualNumber K)ˣ) :
    commonFactorKoszulH1 DualNumber.eps a b ≃ₗ[DualNumber K] K × K :=
  (commonFactorKoszulH1WithTorsion DualNumber.eps a b).trans
    (LinearEquiv.prodCongr dualKoszulAnnihilatorEquiv
      ((Submodule.quotEquivOfEq _ _ dualKoszul_span_eq_socle_range).trans
        dualNumberResidueQuotientEquiv))

/-- Degree-two homology is the recurring residue syzygy. -/
def dualNumberKoszulH2Equiv (a b : (DualNumber K)ˣ) :
    commonFactorKoszulH2 DualNumber.eps a b ≃ₗ[DualNumber K] K :=
  (LinearEquiv.ofEq _ _ (commonFactorKoszulH2_eq_annihilator DualNumber.eps a b)).trans
    dualKoszulAnnihilatorEquiv

#print axioms dualNumberKoszulH1Equiv
#print axioms dualNumberKoszulH2Equiv
end GaloisForLFunctions.HodgeTheoryWithoutVarieties
