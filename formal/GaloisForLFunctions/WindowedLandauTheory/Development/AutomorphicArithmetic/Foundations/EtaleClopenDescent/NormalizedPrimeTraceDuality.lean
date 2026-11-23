import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TraceDualityAtPrime
import GaloisForLFunctions.HTGeometry.IntegralClosureLocalizationEquiv
import GaloisForLFunctions.HTGeometry.LocalNoetherianNormalDVR
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-! The top-form trace test at a prime divisor of a polynomial chart. -/

noncomputable section

open KaehlerDifferential GlobalTheory.SchemeCohomology GaloisForLFunctions.HTGeometry
open scoped GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]
  (A : Subalgebra k F) [IsNoetherianRing A] [IsIntegrallyClosed A] [IsFractionRing A F]

local notation "B" => integralClosure A E

variable [Algebra.Smooth k ((B).restrictScalars k)]

private theorem isDiscreteValuationRing_primeLocalization
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1) :
    IsDiscreteValuationRing (primeLocalizationInField F P) := by
  let R := primeLocalizationInField F P
  letI : IsLocalization.AtPrime R P :=
    inferInstanceAs (IsLocalization.AtPrime (primeLocalizationInField F P) P)
  letI : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R P
  letI : IsNoetherianRing R := IsLocalization.isNoetherianRing P.primeCompl R inferInstance
  letI : IsIntegrallyClosed R :=
    isIntegrallyClosed_of_isLocalization R P.primeCompl P.primeCompl_le_nonZeroDivisors
  exact isDiscreteValuationRing_of_ringKrullDim_eq_one
    ((IsLocalization.AtPrime.ringKrullDim_eq_height P R).trans (by exact_mod_cast hP))

/-- At a height-one prime of a polynomial chart, trace integrality
detects top-form regularity at exactly the primes lying over it. -/
theorem trace_pairing_at_chartPrime_iff_regular {d : ℕ}
    (e : MvPolynomial (Fin d) k ≃ₐ[k] A) (bE : Module.Basis (Fin d) E Ω[E⁄k])
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1) (z : E) :
    let R := primeLocalizationInField F P
    let w := z • exteriorPower.ιMulti E d (fun i => D k E (algebraMap A E (e (MvPolynomial.X i))))
    (∀ b : B, Algebra.trace F E (z * (b : E)) ∈ (algebraMap R F).range) ↔
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap A B) = P →
        ∃ s : B, s ∉ Q ∧ s • w ∈
          LinearMap.range (algebraFormPullback k ((B).restrictScalars k) E d) := by
  intro R w
  letI : Algebra k B := ((B).restrictScalars k).algebra
  letI : IsScalarTower k B E := .of_algebraMap_eq fun _ => rfl
  letI : Algebra k R := (R.restrictScalars k).algebra
  letI : Algebra R E := Algebra.compHom E R.val.toRingHom
  letI : IsScalarTower R F E := .of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower A R E := .of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower k A R := .of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower k R E := .of_algebraMap_eq fun r =>
    IsScalarTower.algebraMap_apply k F E r
  letI : IsLocalization.AtPrime R P := inferInstanceAs (IsLocalization.AtPrime (primeLocalizationInField F P) P)
  letI : IsFractionRing R F := inferInstanceAs (IsFractionRing (primeLocalizationInField F P) F)
  letI : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R P
  letI : IsDiscreteValuationRing R := isDiscreteValuationRing_primeLocalization A P hP
  letI : CharZero (IsLocalRing.ResidueField R) :=
    charZero_of_injective_algebraMap (algebraMap k (IsLocalRing.ResidueField R)).injective
  let T := integralClosure R E
  letI : Algebra A T := (T.restrictScalars A).algebra
  letI : Algebra k T := (T.restrictScalars k).algebra
  letI : IsScalarTower k T E := .of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower A R T := .of_algebraMap_eq fun r =>
    Subtype.ext (IsScalarTower.algebraMap_apply A R E r)
  letI : IsFractionRing T E := integralClosure.isFractionRing_of_finite_extension F E
  letI : IsDedekindDomain T := integralClosure.isDedekindDomain R F E
  letI : Module.Finite R T := IsIntegralClosure.finite R F E T
  letI : Module.IsTorsionFree R E := .trans_faithfulSMul R F E
  letI : Module.IsTorsionFree R T := IsIntegralClosure.isTorsionFree R E
  letI : Algebra B T := (integralClosureLocalizationMap (R := A) (Rf := R) (E := E)).toAlgebra
  letI : IsScalarTower B T E := .of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower A B T := .of_algebraMap_eq fun _ => rfl
  letI : IsLocalization (Algebra.algebraMapSubmonoid E P.primeCompl) E :=
    IsLocalization.of_le_isUnit <| by
      rintro _ ⟨m, hm, rfl⟩
      change IsUnit (algebraMap A E m)
      rw [IsScalarTower.algebraMap_apply A R E]
      exact (IsLocalization.map_units R ⟨m, hm⟩).map (algebraMap R E)
  letI : IsLocalization (Algebra.algebraMapSubmonoid B P.primeCompl) T :=
    IsLocalization.integralClosure P.primeCompl
  letI : Algebra.FormallyEtale B T := .of_isLocalization (Algebra.algebraMapSubmonoid B P.primeCompl)
  letI : Algebra.FormallyEtale A R := .of_isLocalization P.primeCompl
  obtain ⟨a, ha⟩ := exists_kaehler_basis_of_polynomial_chart (k := k) (A := A) (C := R) e
  have hω : z • exteriorPower.ιMulti E d (fun i =>
      D k E (algebraMap R E (algebraMap A R (e (MvPolynomial.X i))))) = w := by
    refine congrArg (fun v => z • exteriorPower.ιMulti E d v) (funext fun i => ?_)
    apply congrArg (D k E)
    show
      algebraMap R E (algebraMap A R (e (MvPolynomial.X i))) =
        algebraMap A E (e (MvPolynomial.X i))
    exact (IsScalarTower.algebraMap_apply A R E _).symm
  have h := trace_pairing_atPrime_iff_regular (k := k) (A := A) (B := B) (R := R)
    (T := T) (F := F) (E := E) P (fun i => algebraMap A R (e (MvPolynomial.X i))) a ha bE z
  rw [← hω]
  exact h

end GlobalTheory.PD
