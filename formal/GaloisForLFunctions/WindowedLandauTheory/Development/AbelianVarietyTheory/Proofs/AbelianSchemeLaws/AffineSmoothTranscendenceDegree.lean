import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineSmoothDimension
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.RelativeForms
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! The transcendence degree of a smooth integral affine chart is its relative dimension. -/

noncomputable section

open AlgebraicGeometry CategoryTheory GaloisForLFunctions.HTGeometry NoetherNormalization

namespace GlobalTheory.SchemeCohomology

/-- For an integral affine algebra of finite type over a field, Noether
normalization computes the two dimensions by the same number of variables. -/
theorem trdeg_eq_of_ringKrullDim {K B : Type} [Field K] [CommRing B] [IsDomain B]
    [Algebra K B] [Algebra.FiniteType K B] {d : ℕ} (hd : ringKrullDim B = d) :
    Algebra.trdeg K B = d := by
  obtain ⟨n, φ, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K B
  let A := MvPolynomial (Fin n) K
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  haveI : Algebra.IsIntegral A B := ⟨hint⟩
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hinj
  have h : ringKrullDim A = ringKrullDim B :=
    ringKrullDim_eq_of_isIntegral A B ((RingHom.injective_iff_ker_eq_bot φ.toRingHom).mp hinj)
  have hn : ringKrullDim A = n := by
    simp [A, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  have hnd : n = d := by exact_mod_cast hn.symm.trans (h.trans hd)
  have htr := trdeg_add_eq K A (A := B)
  rw [trdeg_eq_zero (R := A) (A := B), add_zero] at htr
  simpa [A, MvPolynomial.trdeg_of_isDomain, hnd] using htr.symm

/-- A nonempty affine open of a smooth integral scheme over an algebraically
closed field has transcendence degree equal to the relative dimension. -/
theorem trdeg_sectionRing_of_smooth {K : Type} [Field K] [IsAlgClosed K]
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    [SmoothOfRelativeDimension d f] {U : X.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set X).Nonempty) :
    Algebra.trdeg K (SectionRing f U) = d := by
  letI : Nonempty U := hne.to_subtype
  haveI : IsDomain (SectionRing f U) := inferInstanceAs (IsDomain Γ(X, U))
  haveI : Smooth f := SmoothOfRelativeDimension.smooth (n := d) (f := f)
  have hf := HasRingHomProperty.appLE (@LocallyOfFiniteType) f inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  haveI : Algebra.FiniteType K (SectionRing f U) :=
    RingHom.finiteType_algebraMap.mp (RingHom.finiteType_respectsIso.right _ e hf)
  exact trdeg_eq_of_ringKrullDim (ringKrullDim_smooth_affineOpen f d hU hne)

end GlobalTheory.SchemeCohomology
