import GaloisForLFunctions.HTGeometry.ValuationInertiaIntermediateResidueLift

/-!
# Realizing an intermediate normalization prime by a valuation

Every nonzero prime of the integral closure in an intermediate field is the centre of a proper
valuation subring of the normal closure.  This is the converse existence statement needed to turn
valuation-uniform inertia bounds into statements about every codimension-one normalization prime.
-/

namespace GaloisForLFunctions.HTGeometry
namespace ValuationInertia

noncomputable section

open IsLocalRing IsDedekindDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

variable {A L : Type*} [CommRing A] [IsDedekindDomain A]
variable {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
variable [Field L] [Algebra F L] [Algebra A L] [IsScalarTower A F L]
variable [FiniteDimensional F L] [IsGalois F L]

/-- Every nonzero prime of an intermediate normalization is realized as the centre of a proper
valuation subring of the normal closure. -/
theorem exists_valuationSubring_intermediateCentre_eq
    (M : IntermediateField F L)
    (q : Ideal (integralClosure A M)) [q.IsPrime] (hq : q ≠ ⊥) :
    ∃ (W : ValuationSubring L)
      (hAW : ∀ a : A, algebraMap A L a ∈ W),
      W ≠ ⊤ ∧ intermediateCentre M W hAW = q := by
  haveI : Algebra.IsSeparable F M := Algebra.isSeparable_tower_bot_of_isSeparable F M L
  haveI : IsScalarTower A M L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsDedekindDomain (integralClosure A M) :=
    IsIntegralClosure.isDedekindDomain A F M (integralClosure A M)
  haveI : IsFractionRing (integralClosure A M) M :=
    IsIntegralClosure.isFractionRing_of_finite_extension A F M (integralClosure A M)
  haveI : IsDedekindDomain (integralClosure A L) :=
    IsIntegralClosure.isDedekindDomain A F L (integralClosure A L)
  haveI : IsFractionRing (integralClosure A L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A F L (integralClosure A L)
  haveI : Algebra.IsIntegral (integralClosure A M) (integralClosure A L) :=
    IsIntegralClosure.isIntegral_algebra (integralClosure A M) L
  have hinj : Function.Injective
      (algebraMap (integralClosure A M) (integralClosure A L)) := by
    intro x y hxy
    apply Subtype.ext
    apply (algebraMap M L).injective
    have hL := congrArg Subtype.val hxy
    exact hL
  have hbot : Ideal.comap
      (algebraMap (integralClosure A M) (integralClosure A L))
      (⊥ : Ideal (integralClosure A L)) ≤ q := by
    rw [Ideal.comap_bot_of_injective _ hinj]
    exact bot_le
  obtain ⟨Q, -, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral q
      (⊥ : Ideal (integralClosure A L)) hbot
  letI : Q.IsPrime := hQprime
  have hQ : Q ≠ ⊥ := by
    intro h
    apply hq
    rw [← hQcomap, h]
    exact Ideal.comap_bot_of_injective _ hinj
  let v : IsDedekindDomain.HeightOneSpectrum (integralClosure A L) := ⟨Q, hQprime, hQ⟩
  letI hloc : IsLocalization v.asIdeal.primeCompl
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L v) := by
    exact IsDedekindDomain.HeightOneSpectrum.instIsLocalizationPrimeComplAsIdealSubtypeMemValuationSubringValuationSubringAtPrime v
  let W : ValuationSubring L :=
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L v
  letI : Algebra (integralClosure A L) W := by
    dsimp [W]
    infer_instance
  letI : IsScalarTower (integralClosure A L) W L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : IsLocalization.AtPrime W Q := by
    change IsLocalization v.asIdeal.primeCompl W
    exact hloc
  letI : IsLocalRing W := IsLocalization.AtPrime.isLocalRing W Q
  have hTW : ∀ x : integralClosure A L,
      algebraMap (integralClosure A L) L x ∈ W := by
    intro x
    exact (algebraMap (integralClosure A L) W x).property
  have hAW : ∀ a : A, algebraMap A L a ∈ W := by
    intro a
    have := hTW (algebraMap A (integralClosure A L) a)
    simpa only [IsScalarTower.algebraMap_apply A (integralClosure A L) L] using this
  refine ⟨W, hAW, ?_, ?_⟩
  · dsimp [W]
    rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    simp only [Valuation.valuationSubring_eq_top_iff, not_not]
    infer_instance
  · rw [← comap_centerPrime_eq_intermediateCentre M W hAW]
    suffices centerPrime W (integralClosureTop_mem W hAW) = Q by
      rw [this, hQcomap]
    apply Ideal.ext
    intro x
    change (toValuationSubring W (integralClosureTop_mem W hAW) x ∈
      IsLocalRing.maximalIdeal W) ↔ x ∈ Q
    have heq : toValuationSubring W (integralClosureTop_mem W hAW) x =
        algebraMap (integralClosure A L) W x := by
      apply Subtype.ext
      rfl
    rw [heq]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff W Q x

omit [IsFractionRing A F] [FiniteDimensional F L] [IsGalois F L] in
/-- If a proper intermediate-normalization prime is realized by a valuation, then the valuation is
centred at the maximal ideal of the DVR base. -/
theorem base_centre_of_intermediateCentre_eq
    [IsDiscreteValuationRing A]
    (M : IntermediateField F L)
    (q : Ideal (integralClosure A M)) [q.IsPrime] (hq0 : q ≠ ⊥)
    (W : ValuationSubring L) (hAW : ∀ a : A, algebraMap A L a ∈ W)
    (hqW : intermediateCentre M W hAW = q) :
    ∀ a : A, (¬ IsUnit (⟨algebraMap A L a, hAW a⟩ : W)) ↔
      a ∈ IsLocalRing.maximalIdeal A := by
  have hqunder0 : q.under A ≠ ⊥ := Ideal.under_ne_bot A hq0
  have hqunder : q.under A = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal ((inferInstance : (q.under A).IsPrime).isMaximal hqunder0)
  intro a
  have hcoe :
      (⟨algebraMap (integralClosure A M) L
          (algebraMap A (integralClosure A M) a),
          intermediateBase_mem M W hAW _⟩ : W) =
        (⟨algebraMap A L a, hAW a⟩ : W) := by
    apply Subtype.ext
    exact algebraMap_intermediateBase_apply M a
  constructor
  · intro hnon
    have hnon' : ¬ IsUnit
        (⟨algebraMap (integralClosure A M) L
          (algebraMap A (integralClosure A M) a),
          intermediateBase_mem M W hAW _⟩ : W) := by
      simpa only [hcoe] using hnon
    have hmem := (mem_intermediateCentre_iff M W hAW _).2 hnon'
    have hqa : algebraMap A (integralClosure A M) a ∈ q := by
      simpa only [hqW] using hmem
    have ha : a ∈ q.under A := hqa
    simpa only [hqunder] using ha
  · intro ha
    have hqa : a ∈ q.under A := by
      simpa only [hqunder] using ha
    have hqa' : algebraMap A (integralClosure A M) a ∈ q := hqa
    have hmem : algebraMap A (integralClosure A M) a ∈
        intermediateCentre M W hAW := by
      rw [hqW]
      exact hqa'
    have hnon' := (mem_intermediateCentre_iff M W hAW _).1 hmem
    simpa only [hcoe] using hnon'

end
end ValuationInertia
end GaloisForLFunctions.HTGeometry
