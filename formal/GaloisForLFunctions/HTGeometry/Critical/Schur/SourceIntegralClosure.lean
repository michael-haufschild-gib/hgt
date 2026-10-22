import GaloisForLFunctions.HTGeometry.Critical.Schur.IntegralClosurePlace
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.Critical.Schur.ObservationSourceAlgebra

/-!
# Integral-closure model of the source Schur place

The source Schur valuation ring contains the integral closure of the observation Schur DVR in the
source field, and is in fact its localization at the contracted Schur prime:

```text
CriticalSchurSourceIntegralClosure         integralClosure (observation Schur DVR) (source field)
criticalSchurSourceIntegralClosurePrime    the prime cut out by the source Schur valuation
criticalSchurSourceUpper_isLocalization
    ** the source Schur valuation ring IS that localization **
```

This is the Dedekind-domain model over which mathlib's different-ideal theory applies, and it is
the exact analogue for the source field of what `CriticalSchurIntegralClosurePlace` builds for the
normal closure.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)

/-- The observation Schur DVR acts on the actual source field through the observation field. -/
noncomputable instance criticalSchurObservationSourceFieldAlgebra :
    Algebra (criticalSchurObservationValuationSubring K hm hn) (criticalSourceField K m n) :=
  ((algebraMap (criticalObservationField K m n) (criticalSourceField K m n)).comp
    (criticalSchurObservationValuationSubring K hm hn).subtype).toAlgebra

instance criticalSchurObservationSourceFieldTower :
    IsScalarTower (criticalSchurObservationValuationSubring K hm hn)
      (criticalObservationField K m n) (criticalSourceField K m n) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance criticalSchurObservationSourceValuationTower :
    IsScalarTower (criticalSchurObservationValuationSubring K hm hn)
      (criticalSchurSourceValuationSubring K hm hn) (criticalSourceField K m n) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Integral closure of the observation Schur DVR in the actual source field. -/
abbrev CriticalSchurSourceIntegralClosure :=
  integralClosure (criticalSchurObservationValuationSubring K hm hn) (criticalSourceField K m n)

noncomputable instance criticalSchurSourceIntegralClosure_isDedekindDomain :
    IsDedekindDomain (CriticalSchurSourceIntegralClosure K hm hn) := by
  haveI : FiniteDimensional (criticalObservationField K m n) (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K hm hn
  haveI : Algebra.IsSeparable (criticalObservationField K m n)
      (criticalSourceField K m n) := inferInstance
  exact IsIntegralClosure.isDedekindDomain
    (criticalSchurObservationValuationSubring K hm hn)
    (criticalObservationField K m n)
    (criticalSourceField K m n)
    (CriticalSchurSourceIntegralClosure K hm hn)

noncomputable instance criticalSchurSourceIntegralClosure_finite :
    Module.Finite (criticalSchurObservationValuationSubring K hm hn)
      (CriticalSchurSourceIntegralClosure K hm hn) := by
  haveI : FiniteDimensional (criticalObservationField K m n) (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K hm hn
  haveI : Algebra.IsSeparable (criticalObservationField K m n)
      (criticalSourceField K m n) := inferInstance
  exact IsIntegralClosure.finite
    (criticalSchurObservationValuationSubring K hm hn)
    (criticalObservationField K m n)
    (criticalSourceField K m n)
    (CriticalSchurSourceIntegralClosure K hm hn)

noncomputable instance criticalSchurSourceIntegralClosure_scalarTower :
    IsScalarTower (criticalSchurObservationValuationSubring K hm hn)
      (CriticalSchurSourceIntegralClosure K hm hn)
      (criticalSourceField K m n) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

noncomputable instance criticalSchurSourceIntegralClosure_faithfulSMul :
    FaithfulSMul (criticalSchurObservationValuationSubring K hm hn)
      (CriticalSchurSourceIntegralClosure K hm hn) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 <| by
    have hRN : Function.Injective
        (algebraMap (criticalSchurObservationValuationSubring K hm hn)
          (criticalSourceField K m n)) :=
      (algebraMap (criticalObservationField K m n)
        (criticalSourceField K m n)).injective.comp
        (FaithfulSMul.algebraMap_injective
          (criticalSchurObservationValuationSubring K hm hn)
          (criticalObservationField K m n))
    intro x y hxy
    apply hRN
    simpa only [IsScalarTower.algebraMap_apply
      (criticalSchurObservationValuationSubring K hm hn)
      (CriticalSchurSourceIntegralClosure K hm hn)
      (criticalSourceField K m n)] using
      congrArg (algebraMap (CriticalSchurSourceIntegralClosure K hm hn)
        (criticalSourceField K m n)) hxy

noncomputable instance criticalSchurSourceIntegralClosure_isFractionRing :
    IsFractionRing (CriticalSchurSourceIntegralClosure K hm hn)
      (criticalSourceField K m n) := by
  haveI : FiniteDimensional (criticalObservationField K m n) (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K hm hn
  exact IsIntegralClosure.isFractionRing_of_finite_extension
    (criticalSchurObservationValuationSubring K hm hn)
    (criticalObservationField K m n)
    (criticalSourceField K m n)
    (CriticalSchurSourceIntegralClosure K hm hn)

/-- Every element integral over the observation Schur DVR belongs to the source Schur valuation
ring. -/
theorem criticalSchurSourceIntegralClosure_mem_upper
    (x : CriticalSchurSourceIntegralClosure K hm hn) :
    (x : criticalSourceField K m n) ∈ criticalSchurSourceValuationSubring K hm hn := by
  let O := criticalSchurObservationValuationSubring K hm hn
  let A := criticalSchurSourceValuationSubring K hm hn
  have hbase (a : O) : algebraMap O (criticalSourceField K m n) a ∈ A :=
    (mem_criticalSchurObservationValuationSubring_iff K hm hn a).mp a.property
  haveI : IsIntegrallyClosedIn A.toSubring (criticalSourceField K m n) := by
    rw [Subring.isIntegrallyClosedIn_iff]
    intro y hy
    exact Subring.isIntegrallyClosed_iff.mp (inferInstance : IsIntegrallyClosed A) hy
  exact (Subring.integralClosure_le_iff (T := A.toSubring)).mpr hbase x.property

/-- Inclusion of the source integral closure into the source Schur valuation ring. -/
noncomputable def criticalSchurSourceIntegralClosureToUpper :
    CriticalSchurSourceIntegralClosure K hm hn →+*
      criticalSchurSourceValuationSubring K hm hn where
  toFun x := ⟨x, criticalSchurSourceIntegralClosure_mem_upper K hm hn x⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Prime of the source integral closure cut out by the source Schur valuation. -/
noncomputable def criticalSchurSourceIntegralClosurePrime :
    Ideal (CriticalSchurSourceIntegralClosure K hm hn) :=
  (IsLocalRing.maximalIdeal (criticalSchurSourceValuationSubring K hm hn)).comap
    (criticalSchurSourceIntegralClosureToUpper K hm hn)

noncomputable instance criticalSchurSourceIntegralClosurePrime_isPrime :
    (criticalSchurSourceIntegralClosurePrime K hm hn).IsPrime :=
  Ideal.comap_isPrime (criticalSchurSourceIntegralClosureToUpper K hm hn)
    (IsLocalRing.maximalIdeal (criticalSchurSourceValuationSubring K hm hn))

/-- The contracted prime lies over the maximal ideal of the observation Schur DVR. -/
theorem criticalSchurSourceIntegralClosurePrime_liesOver :
    (criticalSchurSourceIntegralClosurePrime K hm hn).LiesOver
      (IsLocalRing.maximalIdeal (criticalSchurObservationValuationSubring K hm hn)) := by
  constructor
  change IsLocalRing.maximalIdeal (criticalSchurObservationValuationSubring K hm hn) =
    (IsLocalRing.maximalIdeal (criticalSchurSourceValuationSubring K hm hn)).comap
      ((criticalSchurSourceIntegralClosureToUpper K hm hn).comp
        (algebraMap (criticalSchurObservationValuationSubring K hm hn)
          (CriticalSchurSourceIntegralClosure K hm hn)))
  rw [show (criticalSchurSourceIntegralClosureToUpper K hm hn).comp
      (algebraMap (criticalSchurObservationValuationSubring K hm hn)
        (CriticalSchurSourceIntegralClosure K hm hn))
      = algebraMap (criticalSchurObservationValuationSubring K hm hn)
        (criticalSchurSourceValuationSubring K hm hn) by
        ext x
        rfl]
  exact (IsLocalRing.maximalIdeal_comap
    (algebraMap (criticalSchurObservationValuationSubring K hm hn)
      (criticalSchurSourceValuationSubring K hm hn))).symm

/-- The contracted integral-closure prime is nonzero. -/
theorem criticalSchurSourceIntegralClosurePrime_ne_bot :
    criticalSchurSourceIntegralClosurePrime K hm hn ≠ ⊥ := by
  intro hbot
  have hover := (criticalSchurSourceIntegralClosurePrime_liesOver K hm hn).over
  rw [hbot, Ideal.under, ← RingHom.ker_eq_comap_bot] at hover
  have hinj : Function.Injective
      (algebraMap (criticalSchurObservationValuationSubring K hm hn)
        (CriticalSchurSourceIntegralClosure K hm hn)) :=
    FaithfulSMul.algebraMap_injective _ _
  rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj] at hover
  exact IsDiscreteValuationRing.not_a_field
    (criticalSchurObservationValuationSubring K hm hn) hover

/-- Algebra structure on the source Schur valuation ring induced by the integral closure. -/
noncomputable instance criticalSchurSourceIntegralClosureUpperAlgebra :
    Algebra (CriticalSchurSourceIntegralClosure K hm hn)
      (criticalSchurSourceValuationSubring K hm hn) :=
  (criticalSchurSourceIntegralClosureToUpper K hm hn).toAlgebra

noncomputable instance criticalSchurSourceIntegralClosureUpperScalarTower :
    IsScalarTower (CriticalSchurSourceIntegralClosure K hm hn)
      (criticalSchurSourceValuationSubring K hm hn)
      (criticalSourceField K m n) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Localization of the source integral closure at the contracted Schur prime. -/
abbrev CriticalSchurSourceLocalization :=
  Localization.AtPrime (criticalSchurSourceIntegralClosurePrime K hm hn)

/-- Elements outside the contracted Schur prime map to units of the source Schur valuation
ring. -/
theorem criticalSchurSourceIntegralClosureToUpper_isUnit
    (y : (criticalSchurSourceIntegralClosurePrime K hm hn).primeCompl) :
    IsUnit (criticalSchurSourceIntegralClosureToUpper K hm hn
      (y : CriticalSchurSourceIntegralClosure K hm hn)) := by
  by_contra hy
  apply y.property
  change criticalSchurSourceIntegralClosureToUpper K hm hn
      (y : CriticalSchurSourceIntegralClosure K hm hn) ∈
    IsLocalRing.maximalIdeal (criticalSchurSourceValuationSubring K hm hn)
  rw [IsLocalRing.mem_maximalIdeal]
  exact hy

/-- Canonical local map from the prime localization to the source Schur valuation ring. -/
noncomputable def criticalSchurSourceLocalizationToUpper :
    CriticalSchurSourceLocalization K hm hn →+*
      criticalSchurSourceValuationSubring K hm hn :=
  IsLocalization.lift (criticalSchurSourceIntegralClosureToUpper_isUnit K hm hn)

@[simp] theorem criticalSchurSourceLocalizationToUpper_algebraMap
    (x : CriticalSchurSourceIntegralClosure K hm hn) :
    criticalSchurSourceLocalizationToUpper K hm hn
        (algebraMap (CriticalSchurSourceIntegralClosure K hm hn)
          (CriticalSchurSourceLocalization K hm hn) x) =
      criticalSchurSourceIntegralClosureToUpper K hm hn x :=
  IsLocalization.lift_eq (criticalSchurSourceIntegralClosureToUpper_isUnit K hm hn) x

noncomputable instance criticalSchurSourceLocalizationToUpper_isLocalHom :
    IsLocalHom (criticalSchurSourceLocalizationToUpper K hm hn) := by
  let S := CriticalSchurSourceIntegralClosure K hm hn
  let P := criticalSchurSourceIntegralClosurePrime K hm hn
  let R := CriticalSchurSourceLocalization K hm hn
  let A := criticalSchurSourceValuationSubring K hm hn
  let φ : R →+* A := criticalSchurSourceLocalizationToUpper K hm hn
  apply ((local_hom_TFAE φ).out 3 0).mp
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P]
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change φ (algebraMap S R x) ∈ IsLocalRing.maximalIdeal A
  rw [criticalSchurSourceLocalizationToUpper_algebraMap K hm hn]
  exact hx

/-- Fraction-field algebra structure induced through the source Schur valuation ring. -/
noncomputable instance criticalSchurSourceLocalizationFieldAlgebra :
    Algebra (CriticalSchurSourceLocalization K hm hn) (criticalSourceField K m n) :=
  ((criticalSchurSourceValuationSubring K hm hn).subtype.comp
    (criticalSchurSourceLocalizationToUpper K hm hn)).toAlgebra

noncomputable instance criticalSchurSourceLocalizationFieldScalarTower :
    IsScalarTower (CriticalSchurSourceIntegralClosure K hm hn)
      (CriticalSchurSourceLocalization K hm hn)
      (criticalSourceField K m n) :=
  IsScalarTower.of_algebraMap_eq (fun x => by
    change algebraMap (CriticalSchurSourceIntegralClosure K hm hn)
        (criticalSourceField K m n) x =
      (criticalSchurSourceValuationSubring K hm hn).subtype
        (criticalSchurSourceLocalizationToUpper K hm hn
          (algebraMap (CriticalSchurSourceIntegralClosure K hm hn)
            (CriticalSchurSourceLocalization K hm hn) x))
    rw [criticalSchurSourceLocalizationToUpper_algebraMap K hm hn]
    rfl)

noncomputable instance criticalSchurSourceLocalization_isFractionRing :
    IsFractionRing (CriticalSchurSourceLocalization K hm hn) (criticalSourceField K m n) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (criticalSchurSourceIntegralClosurePrime K hm hn).primeCompl
    (CriticalSchurSourceLocalization K hm hn)
    (criticalSourceField K m n)

theorem criticalSchurSourceLocalizationToUpper_comp_subtype :
    (criticalSchurSourceValuationSubring K hm hn).subtype.comp
        (criticalSchurSourceLocalizationToUpper K hm hn) =
      algebraMap (CriticalSchurSourceLocalization K hm hn) (criticalSourceField K m n) :=
  rfl

theorem criticalSchurSourceLocalizationToUpper_bijective :
    Function.Bijective (criticalSchurSourceLocalizationToUpper K hm hn) := by
  let A := criticalSchurSourceValuationSubring K hm hn
  let φ := criticalSchurSourceLocalizationToUpper K hm hn
  let g : A →+* criticalSourceField K m n := A.subtype
  have hcompbij : Function.Bijective (g.rangeRestrict.comp φ) :=
    bijective_rangeRestrict_comp_of_valuationRing
      (R := CriticalSchurSourceLocalization K hm hn) (S := A)
      (K := criticalSourceField K m n) φ g
      (criticalSchurSourceLocalizationToUpper_comp_subtype K hm hn)
  constructor
  · intro x y hxy
    apply hcompbij.1
    exact congrArg g.rangeRestrict hxy
  · intro a
    obtain ⟨x, hx⟩ := hcompbij.2 (g.rangeRestrict a)
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change g (φ x) = g a
    exact congrArg (fun z : g.range => (z : criticalSourceField K m n)) hx

/-- The source Schur valuation ring is the localization of the source integral closure at the
contracted Schur prime. -/
noncomputable instance criticalSchurSourceUpper_isLocalization :
    IsLocalization (criticalSchurSourceIntegralClosurePrime K hm hn).primeCompl
      (criticalSchurSourceValuationSubring K hm hn) :=
  IsLocalization.isLocalization_of_algEquiv _
    { RingEquiv.ofBijective (criticalSchurSourceLocalizationToUpper K hm hn)
        (criticalSchurSourceLocalizationToUpper_bijective K hm hn) with
      commutes' := criticalSchurSourceLocalizationToUpper_algebraMap K hm hn }

end

end GaloisForLFunctions.HTGeometry
