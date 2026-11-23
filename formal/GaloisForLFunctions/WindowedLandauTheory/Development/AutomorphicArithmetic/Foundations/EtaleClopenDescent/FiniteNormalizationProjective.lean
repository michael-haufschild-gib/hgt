import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveCoordinateAlgebras
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SmoothRegularRings
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SmoothStalkDomains
import GaloisForLFunctions.HTGeometry.IntegralRegularLocalFree
import GaloisForLFunctions.HTGeometry.RegularRingLocalization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.GoingDown

/-! Normalized smooth projective charts are finite projective modules over
the coordinate polynomial ring. -/

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace GlobalTheory.SchemeCohomology

variable {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [IsRegularRing A] [IsRegularRing B] [IsIntegrallyClosed A] [Algebra A B] [Module.Finite A B]

/-- Miracle freeness on the prime-local base gives projectivity for a finite
extension of regular domains. -/
theorem projective_of_finite_regular (h : Function.Injective (algebraMap A B)) :
    Module.Projective A B := by
  letI : Module.Flat A B := by
    apply Module.flat_of_isLocalized_maximal A B
      (fun p _ => Localization (Algebra.algebraMapSubmonoid B p.primeCompl))
      (fun _ _ => (IsScalarTower.toAlgHom A B _).toLinearMap)
    intro p hp
    let Ap := Localization.AtPrime p
    let S := Algebra.algebraMapSubmonoid B p.primeCompl
    let T := Localization S
    letI : Algebra Ap T := localizationAlgebra p.primeCompl B
    letI : IsScalarTower A Ap T := isScalarTower_localizationAlgebra _ _
    have hn : S ≤ nonZeroDivisors B := by
      rintro _ ⟨b, hb, rfl⟩
      apply mem_nonZeroDivisors_of_ne_zero
      intro hz
      exact hb (by rw [h (hz.trans (map_zero _).symm)]; exact p.zero_mem)
    letI : IsDomain Ap := IsLocalization.isDomain_of_le_nonZeroDivisors _ p.primeCompl_le_nonZeroDivisors
    letI : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors _ hn
    letI : IsIntegrallyClosed Ap :=
      isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors
    letI : FaithfulSMul Ap T := (faithfulSMul_iff_algebraMap_injective Ap T).mpr
      (localizationAlgebra_injective p.primeCompl B Ap T h)
    letI : Module.Finite Ap T := .of_isLocalization A B p.primeCompl
    letI : Module.Free Ap T := free_of_finite_integral_regular_of_goingDown
    exact (Module.flat_iff_of_isLocalization Ap p.primeCompl T).mp inferInstance
  letI : Module.FinitePresentation A B := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

end GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

open GlobalTheory.SchemeCohomology

variable {k F E : Type} [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E]
  [Algebra F E] [IsScalarTower k F E] {d : ℕ} {x : Fin (d + 1) → F}

/-- Smooth normalized chart algebras of a finite separable cover are
finite projective over their polynomial chart algebras. -/
theorem IsFinCover.finiteProjective_chart (h : IsFinCover k E x) (i : Fin (d + 1)) :
    Module.Finite (rA k x {i}) (integralClosure (rA k x {i}) E) ∧
      Module.Projective (rA k x {i}) (integralClosure (rA k x {i}) E) := by
  let A := rA k x {i}
  let B := integralClosure A E
  let e := h.pd.chartPolynomialEquiv i
  letI : IsRegularRing A := IsRegularRing.of_ringEquiv e.toRingEquiv
  letI : IsIntegrallyClosed (MvPolynomial (Fin d) k) :=
    UpperTheory.Cb.isIntegrallyClosed_fin_polynomialRing k d
  letI : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.toRingEquiv
  letI : IsFractionRing A F := h.pd.isFractionRing_rA i
  letI := h.fin
  letI := h.sep
  letI : Module.Finite A B := IsIntegralClosure.finite A F E B
  haveI : IsRegularRing (rB k E x {i}) := by
    letI : Algebra.Smooth k (rB k E x {i}) := h.smooth i
    exact isRegularRing_of_smooth k _
  letI : IsRegularRing B := inferInstanceAs (IsRegularRing (rB k E x {i}))
  refine ⟨inferInstance, projective_of_finite_regular ?_⟩
  intro a b hab
  apply Subtype.ext
  exact (algebraMap F E).injective (congrArg (fun y : B => (y : E)) hab)

end GlobalTheory.PD
