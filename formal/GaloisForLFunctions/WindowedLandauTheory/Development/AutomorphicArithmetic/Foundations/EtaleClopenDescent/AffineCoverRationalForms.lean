import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverFunctionField
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GenericChartForms
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechDifferentialComplex

/-! Regular forms on the intersections of a normalized affine cover
realize the corresponding submodules of rational forms. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology

namespace GlobalTheory.SchemeCohomology.ExteriorDifferentials

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- Pullback of forms is linear over the common coefficient ring. -/
def mapOverBase (φ : A →ₐ[k] B) (n : ℕ) :
    ExteriorDifferentials k A n →ₗ[k] ExteriorDifferentials k B n where
  toFun := map φ n
  map_add' := (map φ n).map_add
  map_smul' c x := by
    change map φ n (algebraMap k A c • x) = algebraMap k B c • map φ n x
    rw [LinearMap.map_smulₛₗ]
    exact congrArg (· • map φ n x) (φ.commutes c)

/-- An algebra isomorphism gives an isomorphism on each degree of forms. -/
def equivOverBase (φ : A ≃ₐ[k] B) (n : ℕ) :
    ExteriorDifferentials k A n ≃ₗ[k] ExteriorDifferentials k B n :=
  LinearEquiv.ofLinear (mapOverBase φ.toAlgHom n) (mapOverBase φ.symm.toAlgHom n)
    (by
      apply LinearMap.ext
      intro x
      change map φ.toAlgHom n (map φ.symm.toAlgHom n x) = x
      rw [← map_comp, φ.comp_symm, map_id])
    (by
      apply LinearMap.ext
      intro x
      change map φ.symm.toAlgHom n (map φ.toAlgHom n x) = x
      rw [← map_comp, φ.symm_comp, map_id])

end GlobalTheory.SchemeCohomology.ExteriorDifferentials

namespace GlobalTheory.PD

variable {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
  {s : X ⟶ Spec (CommRingCat.of K)} [Algebra K X.functionField]
  {ι : Type} {U : ι → X.Opens} {B : Finset ι → Subalgebra K X.functionField}

local instance coverChartFormsModule (A : Subalgebra K X.functionField) (p : ℕ) :
    Module K (ExteriorDifferentials K A p) :=
  exteriorPowerModule (A := K) (B := A) p

/-- Affine forms identified with the forms in the function field having
regular chart coefficients. -/
def IsAffCover.rationalFormsEquiv (h : IsAffCover s U B) [Smooth s] (I : Finset ι)
    (hI : I.Nonempty) (p : ℕ) :
    FormsOn s (I.inf U) p ≃ₗ[K] omB K X.functionField (B I) p := by
  letI := h.isFractionRing I hI
  letI := h.smooth I hI
  exact (ExteriorDifferentials.equivOverBase (h.sectionEquiv I hI) p).trans (genericFormEquiv _ _ _ _)

theorem omB_mono {E : Type} [Field E] [Algebra K E] {A B : Subalgebra K E}
    (h : A ≤ B) (p : ℕ) : omB K E A p ≤ omB K E B p := by
  apply Submodule.span_mono
  rintro _ ⟨a, ha, v, hv, rfl⟩
  exact ⟨a, h ha, v, fun i => h (hv i), rfl⟩

/-- The regular rational forms on a cover give a Čech complex. -/
theorem IsAffCover.isCechComplex [LinearOrder ι] (h : IsAffCover s U B) (p : ℕ) :
    (cech (fun I => omB K X.functionField (B I) p)).IsCx :=
  cech_isCx_of_mono _ fun _ _ hI hIJ => omB_mono (h.algebra_le hI hIJ) p

end GlobalTheory.PD
