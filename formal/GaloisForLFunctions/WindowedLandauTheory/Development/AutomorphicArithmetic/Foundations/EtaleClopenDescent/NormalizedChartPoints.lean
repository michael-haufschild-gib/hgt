import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveFiniteCover
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineRationalPoints
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.RelativeFormsPullback

/-! Rational points and evaluation homomorphisms on normalized charts. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open GaloisForLFunctions.HTGeometry GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

variable {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
  {s : X ⟶ Spec (CommRingCat.of K)} [Algebra K X.functionField]
  {ι : Type} {U : ι → X.Opens} {B : Finset ι → Subalgebra K X.functionField}

/-- Rational points of a normalized intersection correspond to
base-algebra evaluation homomorphisms on its normalization. -/
def IsAffCover.chartPointEquiv (h : IsAffCover s U B) (I : Finset ι) (hI : I.Nonempty) :
    {y : X.BaseFieldPointOver K s // y.hom default ∈ I.inf U} ≃ (B I →ₐ[K] K) := by
  let e := h.sectionEquiv I hI
  refine (affinePointEquiv (h.affine I hI)).trans
    { toFun := fun χ => χ.comp e.symm.toAlgHom
      invFun := fun χ => χ.comp e.toAlgHom
      left_inv := ?_
      right_inv := ?_ }
  · intro χ
    apply AlgHom.ext
    intro a
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
  · intro χ
    apply AlgHom.ext
    intro a
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]

theorem IsAffCover.chartPointEquiv_eval (h : IsAffCover s U B) (I : Finset ι) (hI : I.Nonempty)
    (y : {y : X.BaseFieldPointOver K s // y.hom default ∈ I.inf U})
    (a : SectionRing s (I.inf U)) :
    h.chartPointEquiv I hI y (h.sectionEquiv I hI a) = affinePointEval y.1 y.2 a := by
  change affinePointEval y.1 y.2 ((h.sectionEquiv I hI).symm (h.sectionEquiv I hI a)) = _
  rw [AlgEquiv.symm_apply_apply]

end GlobalTheory.PD

namespace GlobalTheory.SchemeCohomology

variable {K : Type} [Field K] {X Y : Scheme.{0}}
  {s : X ⟶ Spec (CommRingCat.of K)} {t : Y ⟶ Spec (CommRingCat.of K)} {f : Y ⟶ X}

/-- Map a rational point by a morphism over the base. -/
def mapBaseFieldPoint (hf : f ≫ s = t) (y : Y.BaseFieldPointOver K t) : X.BaseFieldPointOver K s :=
  ⟨y.hom ≫ f, by rw [Category.assoc, hf, y.commutes]⟩

theorem affinePointEval_pullback (hf : f ≫ s = t) (y : Y.BaseFieldPointOver K t)
    (U : X.Opens) (hU : (mapBaseFieldPoint hf y).hom default ∈ U) (a : SectionRing s U) :
    affinePointEval (mapBaseFieldPoint hf y) hU a =
      affinePointEval y (show y.hom default ∈ f ⁻¹ᵁ U from hU) (sectionPullback hf U a) :=
  pointEval_comp y.hom f U hU a

end GlobalTheory.SchemeCohomology
