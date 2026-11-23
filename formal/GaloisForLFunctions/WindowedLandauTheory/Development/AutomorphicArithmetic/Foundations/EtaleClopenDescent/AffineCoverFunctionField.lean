import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveFiniteCover
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! Function fields and smooth section algebras of normalized affine covers. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

variable {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
  {s : X ⟶ Spec (CommRingCat.of K)} [Algebra K X.functionField]
  {ι : Type} {U : ι → X.Opens} {B : Finset ι → Subalgebra K X.functionField}

/-- Restricting sections to a smaller intersection includes its chart algebra
in the larger coordinate algebra in the function field. -/
theorem IsAffCover.algebra_le (h : IsAffCover s U B) {I J : Finset ι}
    (hI : I.Nonempty) (hIJ : I ⊆ J) : B I ≤ B J := by
  intro z hz
  obtain ⟨a, rfl⟩ := (h.ring I hI z).mp hz
  let r : J.inf U ⟶ I.inf U := homOfLE (Finset.inf_mono hIJ)
  exact (h.ring J (hI.mono hIJ) _).mpr
    ⟨(X.presheaf.map r.op).hom a, X.presheaf.germ_res_apply r (genericPoint X) (h.ne J) a⟩

/-- The function field is the fraction field of the algebra of any
nonempty chart intersection. -/
theorem IsAffCover.isFractionRing (h : IsAffCover s U B) (I : Finset ι) (hI : I.Nonempty) :
    IsFractionRing (B I) X.functionField := by
  let V := I.inf U
  let A := SectionRing s V
  letI : Nonempty V := ⟨⟨genericPoint X, h.ne I⟩⟩
  letI : Algebra A X.functionField := (X.germToFunctionField V).hom.toAlgebra
  letI : IsFractionRing A X.functionField := functionField_isFractionRing_of_isAffineOpen X V (h.affine I hI)
  letI : FaithfulSMul (B I) X.functionField :=
    (faithfulSMul_iff_algebraMap_injective (B I) X.functionField).mpr Subtype.val_injective
  apply IsFractionRing.of_field
  intro y
  obtain ⟨a, b, -, hy⟩ := IsFractionRing.div_surjective A y
  refine ⟨h.sectionEquiv I hI a, h.sectionEquiv I hI b, ?_⟩
  change y = (h.sectionEquiv I hI a : X.functionField) / (h.sectionEquiv I hI b : X.functionField)
  rw [h.sectionEquiv_apply_coe, h.sectionEquiv_apply_coe]
  exact hy.symm

/-- The algebra of an affine intersection is smooth when the scheme is smooth. -/
theorem IsAffCover.smooth (h : IsAffCover s U B) [Smooth s] (I : Finset ι) (hI : I.Nonempty) :
    Algebra.Smooth K (B I) := by
  let W := I.inf U
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have hs : (algebraMap K (SectionRing s W)).Smooth :=
    RingHom.Smooth.respectsIso.right _ e (s.smooth_appLE (isAffineOpen_top _) (h.affine I hI) le_top)
  letI : Algebra.Smooth K (SectionRing s W) := RingHom.smooth_algebraMap.mp hs
  exact Algebra.Smooth.of_equiv (h.sectionEquiv I hI)

end GlobalTheory.PD
