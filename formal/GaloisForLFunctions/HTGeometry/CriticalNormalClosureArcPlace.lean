import GaloisForLFunctions.HTGeometry.CriticalGenericArc
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# A discrete place of the actual critical normal closure

The common-scale Laurent arc cuts out a discrete valuation ring in the actual observation field.
This file takes the integral closure of that ring in the actual finite normal closure, chooses a
prime above its maximal ideal by going up, and localizes there.  The result is an actual DVR inside
the normal-closure field; no abstract valued extension or ramification premise is introduced.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

/-- Base DVR cut out on the observation field by the common-scale arc. -/
abbrev CriticalNormalClosureArcBaseRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :=
  CriticalObservationArcValuationRing K hm hn

/-- Actual observation field, named for the normal-closure arc tower. -/
abbrev CriticalNormalClosureArcBaseField
    (K : Type*) [Field K] (m n : ℕ) :=
  criticalObservationField K m n

/-- The base DVR acts on the actual normal closure through the actual observation field. -/
noncomputable instance criticalNormalClosureArcAlgebra
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Algebra (CriticalNormalClosureArcBaseRing K m n hm hn)
      (criticalNormalClosure K m n) :=
  ((algebraMap (CriticalNormalClosureArcBaseField K m n)
      (criticalNormalClosure K m n)).comp
    (algebraMap (CriticalNormalClosureArcBaseRing K m n hm hn)
      (CriticalNormalClosureArcBaseField K m n))).toAlgebra

noncomputable instance criticalNormalClosureArc_scalarTower
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    IsScalarTower (CriticalNormalClosureArcBaseRing K m n hm hn)
      (CriticalNormalClosureArcBaseField K m n)
      (criticalNormalClosure K m n) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Integral closure of the actual common-scale arc DVR in the actual normal closure. -/
abbrev CriticalNormalClosureArcIntegralClosure
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :=
  integralClosure (CriticalNormalClosureArcBaseRing K m n hm hn)
    (criticalNormalClosure K m n)

noncomputable instance criticalNormalClosureArcIntegralClosure_isDedekindDomain
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    IsDedekindDomain (CriticalNormalClosureArcIntegralClosure K m n hm hn) := by
  letI : FiniteDimensional (CriticalNormalClosureArcBaseField K m n)
      (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K hm hn
  letI : Algebra.IsSeparable (CriticalNormalClosureArcBaseField K m n)
      (criticalNormalClosure K m n) := inferInstance
  exact IsIntegralClosure.isDedekindDomain
    (CriticalNormalClosureArcBaseRing K m n hm hn)
    (CriticalNormalClosureArcBaseField K m n)
    (criticalNormalClosure K m n)
    (CriticalNormalClosureArcIntegralClosure K m n hm hn)

noncomputable instance criticalNormalClosureArcIntegralClosure_faithfulSMul
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    FaithfulSMul (CriticalNormalClosureArcBaseRing K m n hm hn)
      (CriticalNormalClosureArcIntegralClosure K m n hm hn) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 <| by
    have hRN : Function.Injective
        (algebraMap (CriticalNormalClosureArcBaseRing K m n hm hn)
          (criticalNormalClosure K m n)) :=
      (algebraMap (CriticalNormalClosureArcBaseField K m n)
        (criticalNormalClosure K m n)).injective.comp
        (FaithfulSMul.algebraMap_injective
          (CriticalNormalClosureArcBaseRing K m n hm hn)
          (CriticalNormalClosureArcBaseField K m n))
    intro x y hxy
    apply hRN
    simpa only [IsScalarTower.algebraMap_apply
      (CriticalNormalClosureArcBaseRing K m n hm hn)
      (CriticalNormalClosureArcIntegralClosure K m n hm hn)
      (criticalNormalClosure K m n)] using
      congrArg (algebraMap (CriticalNormalClosureArcIntegralClosure K m n hm hn)
        (criticalNormalClosure K m n)) hxy

noncomputable instance criticalNormalClosureArcIntegralClosure_scalarTower
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    IsScalarTower (CriticalNormalClosureArcBaseRing K m n hm hn)
      (CriticalNormalClosureArcIntegralClosure K m n hm hn)
      (criticalNormalClosure K m n) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The direct action of the base DVR on the normal closure is the observation-field inclusion. -/
theorem criticalNormalClosureArcBase_algebraMap_apply
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (r : CriticalNormalClosureArcBaseRing K m n hm hn) :
    algebraMap (CriticalNormalClosureArcBaseRing K m n hm hn)
      (criticalNormalClosure K m n) r =
    algebraMap (CriticalNormalClosureArcBaseField K m n)
      (criticalNormalClosure K m n)
      (r : CriticalNormalClosureArcBaseField K m n) := rfl

/-- Chosen prime of the integral closure above the common-scale arc maximal ideal. -/
noncomputable def criticalNormalClosureArcPrime
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Ideal (CriticalNormalClosureArcIntegralClosure K m n hm hn) :=
  Classical.choose (Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := CriticalNormalClosureArcIntegralClosure K m n hm hn)
    (IsLocalRing.maximalIdeal (CriticalNormalClosureArcBaseRing K m n hm hn)))

theorem criticalNormalClosureArcPrime_isMaximal
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (criticalNormalClosureArcPrime K m n hm hn).IsMaximal :=
  (Classical.choose_spec (Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := CriticalNormalClosureArcIntegralClosure K m n hm hn)
    (IsLocalRing.maximalIdeal (CriticalNormalClosureArcBaseRing K m n hm hn)))).1

noncomputable instance criticalNormalClosureArcPrime_isPrime
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (criticalNormalClosureArcPrime K m n hm hn).IsPrime :=
  (criticalNormalClosureArcPrime_isMaximal K m n hm hn).isPrime

theorem criticalNormalClosureArcPrime_liesOver
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (criticalNormalClosureArcPrime K m n hm hn).LiesOver
      (IsLocalRing.maximalIdeal (CriticalNormalClosureArcBaseRing K m n hm hn)) :=
  (Classical.choose_spec (Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := CriticalNormalClosureArcIntegralClosure K m n hm hn)
    (IsLocalRing.maximalIdeal (CriticalNormalClosureArcBaseRing K m n hm hn)))).2

/-- Height-one prime determined by the chosen extension of the common-scale place. -/
noncomputable def criticalNormalClosureArcHeightOne
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    IsDedekindDomain.HeightOneSpectrum
      (CriticalNormalClosureArcIntegralClosure K m n hm hn) where
  asIdeal := criticalNormalClosureArcPrime K m n hm hn
  isPrime := (criticalNormalClosureArcPrime_isMaximal K m n hm hn).isPrime
  ne_bot := by
    intro hbot
    have hover := (criticalNormalClosureArcPrime_liesOver K m n hm hn).over
    rw [hbot, Ideal.under, ← RingHom.ker_eq_comap_bot] at hover
    have hinj : Function.Injective
        (algebraMap (CriticalNormalClosureArcBaseRing K m n hm hn)
          (CriticalNormalClosureArcIntegralClosure K m n hm hn)) :=
      FaithfulSMul.algebraMap_injective _ _
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj] at hover
    exact IsDiscreteValuationRing.not_a_field
      (CriticalNormalClosureArcBaseRing K m n hm hn) hover

noncomputable instance criticalNormalClosureArcIntegralClosure_isFractionRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    IsFractionRing (CriticalNormalClosureArcIntegralClosure K m n hm hn)
      (criticalNormalClosure K m n) := by
  letI : FiniteDimensional (CriticalNormalClosureArcBaseField K m n)
      (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K hm hn
  exact IsIntegralClosure.isFractionRing_of_finite_extension
    (CriticalNormalClosureArcBaseRing K m n hm hn)
    (CriticalNormalClosureArcBaseField K m n)
    (criticalNormalClosure K m n)
    (CriticalNormalClosureArcIntegralClosure K m n hm hn)

/-- Actual DVR in the normal closure extending the common-scale place. -/
noncomputable def CriticalNormalClosureArcValuationRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ValuationSubring (criticalNormalClosure K m n) :=
  IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
    (criticalNormalClosure K m n)
    (criticalNormalClosureArcHeightOne K m n hm hn)

noncomputable instance criticalNormalClosureArcValuationRing_algebraIntegralClosure
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Algebra (CriticalNormalClosureArcIntegralClosure K m n hm hn)
      (CriticalNormalClosureArcValuationRing K m n hm hn) := by
  change Algebra (CriticalNormalClosureArcIntegralClosure K m n hm hn)
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
      (criticalNormalClosure K m n)
      (criticalNormalClosureArcHeightOne K m n hm hn))
  infer_instance

noncomputable instance criticalNormalClosureArcValuationRing_scalarTower
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    IsScalarTower (CriticalNormalClosureArcIntegralClosure K m n hm hn)
      (CriticalNormalClosureArcValuationRing K m n hm hn)
      (criticalNormalClosure K m n) := by
  change IsScalarTower (CriticalNormalClosureArcIntegralClosure K m n hm hn)
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
      (criticalNormalClosure K m n)
      (criticalNormalClosureArcHeightOne K m n hm hn))
    (criticalNormalClosure K m n)
  infer_instance

noncomputable instance criticalNormalClosureArcValuationRing_isLocalization
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    IsLocalization
      (criticalNormalClosureArcPrime K m n hm hn).primeCompl
      (CriticalNormalClosureArcValuationRing K m n hm hn) := by
  change IsLocalization
    (criticalNormalClosureArcHeightOne K m n hm hn).asIdeal.primeCompl
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime
      (criticalNormalClosure K m n)
      (criticalNormalClosureArcHeightOne K m n hm hn))
  infer_instance

/-- The canonical lift of a base-DVR element to the localized integral closure has its expected
value in the normal-closure field.  This cached tower identity keeps downstream coordinate proofs
independent of the implementation of the two localization algebra maps. -/
theorem criticalNormalClosureArcBase_toValuationRing_coe
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (r : CriticalNormalClosureArcBaseRing K m n hm hn) :
    (((algebraMap (CriticalNormalClosureArcIntegralClosure K m n hm hn)
        (CriticalNormalClosureArcValuationRing K m n hm hn)
        (algebraMap (CriticalNormalClosureArcBaseRing K m n hm hn)
          (CriticalNormalClosureArcIntegralClosure K m n hm hn) r)) :
      CriticalNormalClosureArcValuationRing K m n hm hn) :
      criticalNormalClosure K m n) =
    algebraMap (CriticalNormalClosureArcBaseField K m n)
      (criticalNormalClosure K m n)
      (r : CriticalNormalClosureArcBaseField K m n) := by
  calc
    _ = algebraMap (CriticalNormalClosureArcIntegralClosure K m n hm hn)
        (criticalNormalClosure K m n)
        (algebraMap (CriticalNormalClosureArcBaseRing K m n hm hn)
          (CriticalNormalClosureArcIntegralClosure K m n hm hn) r) := by
      change algebraMap (CriticalNormalClosureArcValuationRing K m n hm hn)
        (criticalNormalClosure K m n)
        (algebraMap (CriticalNormalClosureArcIntegralClosure K m n hm hn)
          (CriticalNormalClosureArcValuationRing K m n hm hn)
          (algebraMap (CriticalNormalClosureArcBaseRing K m n hm hn)
            (CriticalNormalClosureArcIntegralClosure K m n hm hn) r)) = _
      rw [← IsScalarTower.algebraMap_apply
        (CriticalNormalClosureArcIntegralClosure K m n hm hn)
        (CriticalNormalClosureArcValuationRing K m n hm hn)
        (criticalNormalClosure K m n)]
    _ = algebraMap (CriticalNormalClosureArcBaseRing K m n hm hn)
        (criticalNormalClosure K m n) r := by
      rw [IsScalarTower.algebraMap_apply
        (CriticalNormalClosureArcBaseRing K m n hm hn)
        (CriticalNormalClosureArcIntegralClosure K m n hm hn)
        (criticalNormalClosure K m n)]
    _ = _ := criticalNormalClosureArcBase_algebraMap_apply K m n hm hn r

noncomputable instance criticalNormalClosureArcValuationRing_isDiscreteValuationRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    IsDiscreteValuationRing (CriticalNormalClosureArcValuationRing K m n hm hn) := by
  rw [CriticalNormalClosureArcValuationRing,
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  infer_instance

end

end GaloisForLFunctions.HTGeometry
