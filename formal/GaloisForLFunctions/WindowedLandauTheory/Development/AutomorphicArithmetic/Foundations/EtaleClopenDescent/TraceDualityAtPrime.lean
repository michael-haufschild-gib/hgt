import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LocalizedTraceDuality
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TracePairingLocalization
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FormDenominatorLocalization
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! The trace-dual condition at a prime divisor of the base is the
regularity condition at the primes above it on the normalized chart. -/

noncomputable section

open KaehlerDifferential IsLocalRing GlobalTheory.SchemeCohomology
open scoped GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

variable {k A B R T F E : Type} [Field k] [CommRing A] [CommRing B]
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero (ResidueField R)]
  [CommRing T] [IsDedekindDomain T] [Field F] [Field E]
  [Algebra A B] [Algebra A R] [Algebra A T] [Algebra A F] [Algebra R F] [Algebra F E]
  [Algebra A E] [Algebra B E] [Algebra R E] [Algebra T E] [Algebra R T] [Algebra B T]
  [IsScalarTower A B T] [IsScalarTower A R T] [IsScalarTower A R F]
  [IsScalarTower A B E] [IsScalarTower A F E] [IsScalarTower B T E]
  [IsScalarTower R F E] [IsScalarTower R T E]
  [IsFractionRing R F] [IsFractionRing T E] [IsIntegralClosure T R E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E] [Module.Finite R T] [Module.IsTorsionFree R T]
  [Algebra k B] [Algebra k R] [Algebra k T] [Algebra k E]
  [IsScalarTower k B E] [IsScalarTower k R E] [IsScalarTower k T E]
  [Algebra.Smooth k B] [Algebra.FormallyEtale B T]

include T in
/-- For a base localization and its normalized order, trace integrality
is equivalent to regularity after inverting a denominator at each prime
of the original order above the base prime. -/
theorem trace_pairing_atPrime_iff_regular (P : Ideal A) [P.IsPrime]
    [IsLocalization.AtPrime R P] [IsLocalization (Algebra.algebraMapSubmonoid B P.primeCompl) T]
    {d : ℕ} (u : Fin d → R) (a : Module.Basis (Fin d) R Ω[R⁄k]) (ha : ∀ i, a i = D k R (u i))
    (bE : Module.Basis (Fin d) E Ω[E⁄k]) (z : E) :
    let w := z • exteriorPower.ιMulti E d (fun i => D k E (algebraMap R E (u i)))
    (∀ b : B, Algebra.trace F E (z * algebraMap B E b) ∈ (algebraMap R F).range) ↔
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap A B) = P →
        ∃ s : B, s ∉ Q ∧ s • w ∈ LinearMap.range (algebraFormPullback k B E d) := by
  intro w
  letI : Algebra.IsIntegral R T := IsIntegralClosure.isIntegral_algebra R E
  have hc : (algebraMap B T).comp (algebraMap A B) = (algebraMap R T).comp (algebraMap A R) :=
    (IsScalarTower.algebraMap_eq A B T).symm.trans (IsScalarTower.algebraMap_eq A R T)
  have hcomap (Q : Ideal T) :
      (Q.comap (algebraMap B T)).comap (algebraMap A B) =
        (Q.comap (algebraMap R T)).comap (algebraMap A R) := by
    simp only [Ideal.comap_comap, hc]
  have hreg (Q : Ideal T) [Q.IsMaximal] :
      w ∈ LinearMap.range
          (algebraFormPullback k ((primeLocalizationInField E Q).restrictScalars k) E d) ↔
        ∃ s : B, s ∉ Q.comap (algebraMap B T) ∧
          s • w ∈ LinearMap.range (algebraFormPullback k B E d) := by
    let C := primeLocalizationInField E Q
    letI : Algebra k C := (C.restrictScalars k).algebra
    letI : Algebra B C := (C.restrictScalars B).algebra
    letI : IsScalarTower k C E := .of_algebraMap_eq fun _ => rfl
    letI : IsScalarTower B C E := .of_algebraMap_eq fun _ => rfl
    letI : IsScalarTower B T C := .of_algebraMap_eq fun x =>
      Subtype.ext (IsScalarTower.algebraMap_apply B T E x)
    letI : IsScalarTower k B C := .of_algebraMap_eq fun x =>
      Subtype.ext (IsScalarTower.algebraMap_apply k B E x)
    letI : IsLocalization.AtPrime C Q := inferInstanceAs (IsLocalization.AtPrime (primeLocalizationInField E Q) Q)
    letI : IsLocalization.AtPrime C (Q.comap (algebraMap B T)) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Algebra.algebraMapSubmonoid B P.primeCompl) C Q
    refine (mem_formRange_localization_iff (C := C) (Q.comap (algebraMap B T)).primeCompl w).trans ⟨?_, ?_⟩
    · rintro ⟨s, hs⟩
      exact ⟨s, s.property, hs⟩
    · rintro ⟨s, hs, hw⟩
      exact ⟨⟨s, hs⟩, hw⟩
  rw [trace_pairing_localization (T := T) P.primeCompl z]
  rw [trace_dual_iff_topForm_regular_at_maximal (B := B) (T := T) u a ha bE z]
  constructor
  · intro h Q _ hQ
    letI : Q.LiesOver P := ⟨hQ.symm⟩
    let Q' := Q.map (algebraMap B T)
    letI : Q'.IsPrime := IsLocalization.AtPrime.isPrime_map_of_liesOver B P T Q
    have hQ' : Q'.comap (algebraMap B T) = Q :=
      IsLocalization.under_map_of_isPrime_disjoint (Algebra.algebraMapSubmonoid B P.primeCompl) T
        (inferInstance : Q.IsPrime) (Ideal.disjoint_primeCompl_of_liesOver Q P)
    have hp : (Q'.comap (algebraMap R T)).comap (algebraMap A R) = P :=
      (hcomap Q').symm.trans ((congrArg (Ideal.comap (algebraMap A B)) hQ').trans hQ)
    have he : Q'.comap (algebraMap R T) = maximalIdeal R :=
      (IsLocalization.map_under P.primeCompl R _).symm.trans
        ((congrArg (Ideal.map (algebraMap A R)) hp).trans (IsLocalization.AtPrime.map_eq_maximalIdeal P R))
    letI : Q'.IsMaximal := Ideal.IsIntegral.isMaximal_of_isMaximal_comap Q'
      (he.symm ▸ maximalIdeal.isMaximal R)
    simpa only [hQ'] using (hreg Q').mp (h Q')
  · intro h Q _
    have hmax : (Q.comap (algebraMap R T)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
    have hp : (Q.comap (algebraMap B T)).comap (algebraMap A B) = P :=
      (hcomap Q).trans ((congrArg (Ideal.comap (algebraMap A R)) (IsLocalRing.eq_maximalIdeal hmax)).trans
        (IsLocalization.AtPrime.under_maximalIdeal R P))
    letI : (Q.comap (algebraMap B T)).IsPrime := Ideal.comap_isPrime _ Q
    exact (hreg Q).mpr (h (Q.comap (algebraMap B T)) hp)

end GlobalTheory.PD
