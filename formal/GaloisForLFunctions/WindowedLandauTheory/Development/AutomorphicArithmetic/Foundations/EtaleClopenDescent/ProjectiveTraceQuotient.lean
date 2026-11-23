import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveTrace
import Mathlib.RingTheory.Trace.Quotient
import Mathlib.RingTheory.Localization.BaseChange

/-! Multiplication trace on a finite projective algebra specializes to
the trace of the closed fibre. -/

noncomputable section

open IsLocalRing IsLocalization.AtPrime

namespace GlobalTheory.SchemeCohomology

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]

theorem trace_quotient_eq_projectiveAlgebraTrace (p : Ideal A) [p.IsMaximal] (b : B) :
    Algebra.trace (A ⧸ p) (B ⧸ p.map (algebraMap A B)) (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk p (projectiveAlgebraTrace A B b) := by
  let Ap := Localization.AtPrime p
  let Bp := Localization (Algebra.algebraMapSubmonoid B p.primeCompl)
  letI : Algebra Ap Bp := localizationAlgebra p.primeCompl B
  letI : IsScalarTower A Ap Bp := isScalarTower_localizationAlgebra _ _
  letI : Algebra.IsPushout A Ap B Bp := (Algebra.isPushout_of_isLocalization p.primeCompl Ap B Bp).symm
  letI : Module.Finite Ap Bp := .of_isLocalization A B p.primeCompl
  letI : Module.Flat Ap Bp := Module.Flat.of_isLocalizedModule Ap p.primeCompl
    (IsScalarTower.toAlgHom A B Bp).toLinearMap
  letI : Module.Free Ap Bp := Module.free_of_flat_of_isLocalRing
  let e := equivQuotMaximalIdeal p Ap
  have he (a : A) : e (Ideal.Quotient.mk p a) = Ideal.Quotient.mk (maximalIdeal Ap) (algebraMap A Ap a) := rfl
  apply e.injective
  rw [trace_quotient_eq_trace_localization_quotient B p Ap Bp, RingEquiv.apply_symm_apply,
    IsScalarTower.algebraMap_eq B Bp, RingHom.comp_apply, Ideal.Quotient.algebraMap_eq,
    Algebra.trace_quotient_mk, ← projectiveAlgebraTrace_eq_trace,
    projectiveAlgebraTrace_baseChange (R := A) (A := B) (S := Ap) (B := Bp) b, he]

end GlobalTheory.SchemeCohomology
