import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExteriorDifferentials
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveTrace
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! The trace on differential forms along a finite étale ring map. -/

open TensorProduct GaloisForLFunctions.HTGeometry

noncomputable section

namespace GlobalTheory.SchemeCohomology

variable (k A B : Type*) [CommRing k] [CommRing A] [CommRing B] [Algebra k A]
  [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/-- The pullback of a differential form is linear over the source algebra. -/
def algebraFormPullback (n : ℕ) :
    ExteriorDifferentials k A n →ₗ[A] ExteriorDifferentials k B n :=
  exteriorMapOver n (KaehlerDifferential.map k k A B)

/-- Relative forms extend by scalar extension across a formally étale map. -/
theorem algebraFormPullback_isBaseChange [Algebra.FormallyEtale A B] (n : ℕ) :
    IsBaseChange B (algebraFormPullback k A B n) :=
  exteriorMapOver_isBaseChange (KaehlerDifferential.isBaseChange_of_formallyEtale k A B) n

/-- The scalar extension description agrees with the semilinear pullback on forms. -/
theorem algebraFormPullback_eq_map (f : A →ₐ[k] B) (hf : f.toRingHom = algebraMap A B)
    (n : ℕ) (ω : ExteriorDifferentials k A n) :
    algebraFormPullback k A B n ω = ExteriorDifferentials.map f n ω := by
  have hD (x : Ω[A⁄k]) :
      KaehlerDifferential.map k k A B x = algHomKaehlerMap f x := by
    have hx : x ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) := by
      rw [KaehlerDifferential.span_range_derivation]
      exact Submodule.mem_top
    refine Submodule.span_induction ?_ (by simp) ?_ ?_ hx
    · rintro _ ⟨a, rfl⟩
      rw [KaehlerDifferential.map_D, algHomKaehlerMap_D]
      exact congrArg (KaehlerDifferential.D k B) (DFunLike.congr_fun hf a).symm
    · intro a b _ _ ha hb
      simp only [map_add, ha, hb]
    · intro a x _ hx
      rw [map_smul, algHomKaehlerMap_smul, hx, ← IsScalarTower.algebraMap_smul B,
        ← DFunLike.congr_fun hf a]
      rfl
  have hω : ω ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n (M := Ω[A⁄k]))) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  refine Submodule.span_induction ?_ (by simp) ?_ ?_ hω
  · rintro _ ⟨v, rfl⟩
    simp only [algebraFormPullback, exteriorMapOver_ιMulti, ExteriorDifferentials.map_ιMulti, hD]
  · intro u v _ _ hu hv
    simp only [map_add, hu, hv]
  · intro a x _ hx
    rw [map_smul, LinearMap.map_smulₛₗ, hx, ← IsScalarTower.algebraMap_smul B,
      ← DFunLike.congr_fun hf a]

variable [Module.Finite A B] [Algebra.Etale A B]

private theorem projective_of_finite_etale : Module.Projective A B := by
  haveI : Module.FinitePresentation A B := .of_finite_of_finitePresentation A B
  exact Module.Flat.projective_of_finitePresentation

/-- A finite étale algebra has a trace defined using its projective module structure. -/
def finiteEtaleAlgebraTrace : B →ₗ[A] A :=
  letI := projective_of_finite_etale A B
  projectiveAlgebraTrace A B

theorem finiteEtaleAlgebraTrace_baseChange {S C : Type*} [CommRing S] [CommRing C]
    [Algebra A S] [Algebra S C] [Algebra B C] [Algebra A C] [IsScalarTower A S C]
    [IsScalarTower A B C] [Module.Finite S C] [Algebra.Etale S C] [Algebra.IsPushout A S B C]
    (b : B) :
    finiteEtaleAlgebraTrace S C (algebraMap B C b) =
      algebraMap A S (finiteEtaleAlgebraTrace A B b) := by
  letI := projective_of_finite_etale A B
  letI := projective_of_finite_etale S C
  exact projectiveAlgebraTrace_baseChange b

/-- Trace on forms is the algebra trace on the coefficients after étale base change. -/
def finiteEtaleFormTrace (n : ℕ) :
    ExteriorDifferentials k B n →ₗ[A] ExteriorDifferentials k A n :=
  (TensorProduct.lid A (ExteriorDifferentials k A n)).toLinearMap ∘ₗ
    (finiteEtaleAlgebraTrace A B).rTensor (ExteriorDifferentials k A n) ∘ₗ
      ((algebraFormPullback_isBaseChange k A B n).equiv.symm.toLinearMap.restrictScalars A)

theorem finiteEtaleFormTrace_smul_pullback (n : ℕ) (b : B) (ω : ExteriorDifferentials k A n) :
    finiteEtaleFormTrace k A B n (b • algebraFormPullback k A B n ω) =
      finiteEtaleAlgebraTrace A B b • ω := by
  have heq := (algebraFormPullback_isBaseChange k A B n).equiv_tmul b ω
  simp only [finiteEtaleFormTrace, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe, ← heq, LinearEquiv.symm_apply_apply, LinearMap.rTensor_tmul,
    TensorProduct.lid_tmul]

end GlobalTheory.SchemeCohomology
