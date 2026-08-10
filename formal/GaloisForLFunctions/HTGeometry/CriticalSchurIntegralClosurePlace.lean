import GaloisForLFunctions.HTGeometry.CriticalSchurNormalFibreReduction
import GaloisForLFunctions.HTGeometry.CriticalSchurValuationDVR
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Integral-closure model of the actual Schur place

The chosen valuation ring in the actual critical normal closure contains the integral closure of
the observation Schur DVR.  Contracting its maximal ideal therefore gives a canonical prime of
that integral closure.  This module supplies the global Dedekind-domain model needed to apply
ideal-theoretic ramification and inertia theorems to the already-constructed valuation place.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing
open scoped Pointwise

set_option synthInstance.maxHeartbeats 3000000
set_option maxHeartbeats 4000000

/-- Observation Schur DVR, named as base ring of the normal-closure integral model. -/
abbrev CriticalSchurNormalBaseRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :=
  criticalSchurObservationValuationSubring K hm hn

/-- The observation Schur DVR acts on the actual normal closure through the observation field. -/
noncomputable instance criticalSchurNormalBaseAlgebra
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Algebra (CriticalSchurNormalBaseRing K hm hn)
      (criticalNormalClosure K m n) :=
  ((algebraMap (criticalObservationField K m n)
      (criticalNormalClosure K m n)).comp
    (CriticalSchurNormalBaseRing K hm hn).subtype).toAlgebra

noncomputable instance criticalSchurNormalBaseScalarTower
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsScalarTower (CriticalSchurNormalBaseRing K hm hn)
      (criticalObservationField K m n) (criticalNormalClosure K m n) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Integral closure of the observation Schur DVR in the actual normal closure. -/
abbrev CriticalSchurNormalIntegralClosure
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :=
  integralClosure (CriticalSchurNormalBaseRing K hm hn)
    (criticalNormalClosure K m n)

noncomputable instance criticalSchurNormalIntegralClosure_isDedekindDomain
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsDedekindDomain (CriticalSchurNormalIntegralClosure K hm hn) := by
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K hm hn
  letI : Algebra.IsSeparable (criticalObservationField K m n)
      (criticalNormalClosure K m n) := inferInstance
  exact IsIntegralClosure.isDedekindDomain
    (CriticalSchurNormalBaseRing K hm hn)
    (criticalObservationField K m n)
    (criticalNormalClosure K m n)
    (CriticalSchurNormalIntegralClosure K hm hn)

noncomputable instance criticalSchurNormalIntegralClosure_finite
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Module.Finite (CriticalSchurNormalBaseRing K hm hn)
      (CriticalSchurNormalIntegralClosure K hm hn) := by
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K hm hn
  letI : Algebra.IsSeparable (criticalObservationField K m n)
      (criticalNormalClosure K m n) := inferInstance
  exact IsIntegralClosure.finite
    (CriticalSchurNormalBaseRing K hm hn)
    (criticalObservationField K m n)
    (criticalNormalClosure K m n)
    (CriticalSchurNormalIntegralClosure K hm hn)

noncomputable instance criticalSchurNormalIntegralClosure_faithfulSMul
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    FaithfulSMul (CriticalSchurNormalBaseRing K hm hn)
      (CriticalSchurNormalIntegralClosure K hm hn) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 <| by
    have hRN : Function.Injective
        (algebraMap (CriticalSchurNormalBaseRing K hm hn)
          (criticalNormalClosure K m n)) :=
      (algebraMap (criticalObservationField K m n)
        (criticalNormalClosure K m n)).injective.comp
        (FaithfulSMul.algebraMap_injective
          (CriticalSchurNormalBaseRing K hm hn)
          (criticalObservationField K m n))
    intro x y hxy
    apply hRN
    simpa only [IsScalarTower.algebraMap_apply
      (CriticalSchurNormalBaseRing K hm hn)
      (CriticalSchurNormalIntegralClosure K hm hn)
      (criticalNormalClosure K m n)] using
      congrArg (algebraMap (CriticalSchurNormalIntegralClosure K hm hn)
        (criticalNormalClosure K m n)) hxy

noncomputable instance criticalSchurNormalIntegralClosure_scalarTower
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsScalarTower (CriticalSchurNormalBaseRing K hm hn)
      (CriticalSchurNormalIntegralClosure K hm hn)
      (criticalNormalClosure K m n) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

noncomputable instance criticalSchurNormalIntegralClosure_isFractionRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsFractionRing (CriticalSchurNormalIntegralClosure K hm hn)
      (criticalNormalClosure K m n) := by
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K hm hn
  exact IsIntegralClosure.isFractionRing_of_finite_extension
    (CriticalSchurNormalBaseRing K hm hn)
    (criticalObservationField K m n)
    (criticalNormalClosure K m n)
    (CriticalSchurNormalIntegralClosure K hm hn)

/-- Every element integral over the observation Schur DVR belongs to the chosen upper valuation
ring. -/
theorem criticalSchurNormalIntegralClosure_mem_upper
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (x : CriticalSchurNormalIntegralClosure K hm hn) :
    (x : criticalNormalClosure K m n) ∈
      criticalNormalClosureSchurValuationSubring K hm hn := by
  let O := CriticalSchurNormalBaseRing K hm hn
  let A := criticalNormalClosureSchurValuationSubring K hm hn
  have hbase (a : O) : algebraMap O (criticalNormalClosure K m n) a ∈ A := by
    exact criticalNormalClosureSchurValuationSubring_observation_mem K hm hn a
  letI : IsIntegrallyClosedIn A.toSubring (criticalNormalClosure K m n) := by
    rw [Subring.isIntegrallyClosedIn_iff]
    intro y hy
    exact Subring.isIntegrallyClosed_iff.mp
      (inferInstance : IsIntegrallyClosed A) hy
  exact (Subring.integralClosure_le_iff (T := A.toSubring)).mpr hbase x.property

/-- Inclusion of the normal integral closure into the chosen Schur valuation ring. -/
noncomputable def criticalSchurNormalIntegralClosureToUpper
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    CriticalSchurNormalIntegralClosure K hm hn →+*
      criticalNormalClosureSchurValuationSubring K hm hn where
  toFun x := ⟨x, criticalSchurNormalIntegralClosure_mem_upper K hm hn x⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The observation-DVR embedding into the chosen upper valuation ring is local. -/
noncomputable instance criticalSchurObservationValuationToNormalClosure_isLocalHom
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsLocalHom (criticalSchurObservationValuationToNormalClosure K hm hn) where
  map_nonunit a ha := by
    let A := criticalNormalClosureSchurValuationSubring K hm hn
    have ha0 : (a : criticalObservationField K m n) ≠ 0 := by
      intro ha0
      have : criticalSchurObservationValuationToNormalClosure K hm hn a = 0 := by
        apply Subtype.ext
        simp [ha0, criticalSchurObservationValuationToNormalClosure]
      rw [this] at ha
      exact not_isUnit_zero ha
    have hval : A.valuation
        (criticalObservationNormalClosureMap K m n (a : criticalObservationField K m n)) = 1 :=
      (A.valuation_eq_one_iff
        (criticalSchurObservationValuationToNormalClosure K hm hn a)).mp ha
    have hinvA : criticalObservationNormalClosureMap K m n
        ((a : criticalObservationField K m n)⁻¹) ∈ A := by
      rw [← A.valuation_le_one_iff, map_inv₀, map_inv₀, hval, inv_one]
    have hinvComap : (a : criticalObservationField K m n)⁻¹ ∈
        A.comap (algebraMap (criticalObservationField K m n)
          (criticalNormalClosure K m n)) := hinvA
    have hinvO : (a : criticalObservationField K m n)⁻¹ ∈
        criticalSchurObservationValuationSubring K hm hn := by
      rw [criticalNormalClosureSchurValuationSubring_comap_observation K hm hn]
        at hinvComap
      exact hinvComap
    rw [isUnit_iff_exists_inv]
    refine ⟨⟨(a : criticalObservationField K m n)⁻¹, hinvO⟩, Subtype.ext ?_⟩
    exact mul_inv_cancel₀ ha0

/-- Prime of the normal integral closure cut out by the chosen upper Schur valuation. -/
noncomputable def criticalSchurNormalIntegralClosurePrime
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Ideal (CriticalSchurNormalIntegralClosure K hm hn) :=
  (IsLocalRing.maximalIdeal
    (criticalNormalClosureSchurValuationSubring K hm hn)).comap
      (criticalSchurNormalIntegralClosureToUpper K hm hn)

noncomputable instance criticalSchurNormalIntegralClosurePrime_isPrime
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalSchurNormalIntegralClosurePrime K hm hn).IsPrime :=
  Ideal.comap_isPrime (criticalSchurNormalIntegralClosureToUpper K hm hn)
    (IsLocalRing.maximalIdeal
      (criticalNormalClosureSchurValuationSubring K hm hn))

/-- The contracted prime lies over the maximal ideal of the observation Schur DVR. -/
theorem criticalSchurNormalIntegralClosurePrime_liesOver
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalSchurNormalIntegralClosurePrime K hm hn).LiesOver
      (IsLocalRing.maximalIdeal (CriticalSchurNormalBaseRing K hm hn)) := by
  constructor
  change IsLocalRing.maximalIdeal (CriticalSchurNormalBaseRing K hm hn) =
    (IsLocalRing.maximalIdeal
      (criticalNormalClosureSchurValuationSubring K hm hn)).comap
        ((criticalSchurNormalIntegralClosureToUpper K hm hn).comp
          (algebraMap (CriticalSchurNormalBaseRing K hm hn)
            (CriticalSchurNormalIntegralClosure K hm hn)))
  rw [show (criticalSchurNormalIntegralClosureToUpper K hm hn).comp
      (algebraMap (CriticalSchurNormalBaseRing K hm hn)
        (CriticalSchurNormalIntegralClosure K hm hn)) =
      criticalSchurObservationValuationToNormalClosure K hm hn by
        ext x
        rfl]
  exact (IsLocalRing.maximalIdeal_comap
    (criticalSchurObservationValuationToNormalClosure K hm hn)).symm

/-- The contracted integral-closure prime is nonzero. -/
theorem criticalSchurNormalIntegralClosurePrime_ne_bot
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSchurNormalIntegralClosurePrime K hm hn ≠ ⊥ := by
  intro hbot
  have hover := (criticalSchurNormalIntegralClosurePrime_liesOver K hm hn).over
  rw [hbot, Ideal.under, ← RingHom.ker_eq_comap_bot] at hover
  have hinj : Function.Injective
      (algebraMap (CriticalSchurNormalBaseRing K hm hn)
        (CriticalSchurNormalIntegralClosure K hm hn)) :=
    FaithfulSMul.algebraMap_injective _ _
  rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj] at hover
  exact IsDiscreteValuationRing.not_a_field
    (CriticalSchurNormalBaseRing K hm hn) hover

/-- The contracted prime is maximal because the normal integral closure is Dedekind. -/
theorem criticalSchurNormalIntegralClosurePrime_isMaximal
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalSchurNormalIntegralClosurePrime K hm hn).IsMaximal :=
  Ideal.IsPrime.isMaximal inferInstance
    (criticalSchurNormalIntegralClosurePrime_ne_bot K hm hn)

/-- Algebra structure on the chosen upper valuation ring induced by the normal integral closure. -/
noncomputable instance criticalSchurNormalIntegralClosureUpperAlgebra
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Algebra (CriticalSchurNormalIntegralClosure K hm hn)
      (criticalNormalClosureSchurValuationSubring K hm hn) :=
  (criticalSchurNormalIntegralClosureToUpper K hm hn).toAlgebra

noncomputable instance criticalSchurNormalIntegralClosureUpperScalarTower
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsScalarTower (CriticalSchurNormalIntegralClosure K hm hn)
      (criticalNormalClosureSchurValuationSubring K hm hn)
      (criticalNormalClosure K m n) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Localization of the normal integral closure at the contracted Schur prime. -/
abbrev CriticalSchurNormalLocalization
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :=
  Localization.AtPrime (criticalSchurNormalIntegralClosurePrime K hm hn)

/-- Elements outside the contracted Schur prime map to units of the chosen upper ring. -/
theorem criticalSchurNormalIntegralClosureToUpper_isUnit
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (y : (criticalSchurNormalIntegralClosurePrime K hm hn).primeCompl) :
    IsUnit (criticalSchurNormalIntegralClosureToUpper K hm hn
      (y : CriticalSchurNormalIntegralClosure K hm hn)) := by
  by_contra hy
  apply y.property
  change criticalSchurNormalIntegralClosureToUpper K hm hn
      (y : CriticalSchurNormalIntegralClosure K hm hn) ∈
    IsLocalRing.maximalIdeal
      (criticalNormalClosureSchurValuationSubring K hm hn)
  rw [IsLocalRing.mem_maximalIdeal]
  exact hy

/-- Canonical local map from the prime localization to the chosen upper valuation ring. -/
noncomputable def criticalSchurNormalLocalizationToUpper
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    CriticalSchurNormalLocalization K hm hn →+*
      criticalNormalClosureSchurValuationSubring K hm hn :=
  IsLocalization.lift
    (criticalSchurNormalIntegralClosureToUpper_isUnit K hm hn)

@[simp] theorem criticalSchurNormalLocalizationToUpper_algebraMap
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (x : CriticalSchurNormalIntegralClosure K hm hn) :
    criticalSchurNormalLocalizationToUpper K hm hn
        (algebraMap (CriticalSchurNormalIntegralClosure K hm hn)
          (CriticalSchurNormalLocalization K hm hn) x) =
      criticalSchurNormalIntegralClosureToUpper K hm hn x :=
  IsLocalization.lift_eq
    (criticalSchurNormalIntegralClosureToUpper_isUnit K hm hn) x

noncomputable instance criticalSchurNormalLocalizationToUpper_isLocalHom
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsLocalHom (criticalSchurNormalLocalizationToUpper K hm hn) := by
  let S := CriticalSchurNormalIntegralClosure K hm hn
  let P := criticalSchurNormalIntegralClosurePrime K hm hn
  let R := CriticalSchurNormalLocalization K hm hn
  let A := criticalNormalClosureSchurValuationSubring K hm hn
  let φ : R →+* A := criticalSchurNormalLocalizationToUpper K hm hn
  apply ((local_hom_TFAE φ).out 3 0).mp
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P]
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change φ (algebraMap S R x) ∈ IsLocalRing.maximalIdeal A
  rw [criticalSchurNormalLocalizationToUpper_algebraMap K hm hn]
  exact hx

/-- Fraction-field algebra structure induced through the chosen upper valuation ring. -/
noncomputable instance criticalSchurNormalLocalizationFieldAlgebra
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Algebra (CriticalSchurNormalLocalization K hm hn)
      (criticalNormalClosure K m n) :=
  ((criticalNormalClosureSchurValuationSubring K hm hn).subtype.comp
    (criticalSchurNormalLocalizationToUpper K hm hn)).toAlgebra

noncomputable instance criticalSchurNormalLocalizationFieldScalarTower
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsScalarTower (CriticalSchurNormalIntegralClosure K hm hn)
      (CriticalSchurNormalLocalization K hm hn)
      (criticalNormalClosure K m n) :=
  IsScalarTower.of_algebraMap_eq (fun x => by
    change algebraMap (CriticalSchurNormalIntegralClosure K hm hn)
        (criticalNormalClosure K m n) x =
      (criticalNormalClosureSchurValuationSubring K hm hn).subtype
        (criticalSchurNormalLocalizationToUpper K hm hn
          (algebraMap (CriticalSchurNormalIntegralClosure K hm hn)
            (CriticalSchurNormalLocalization K hm hn) x))
    rw [criticalSchurNormalLocalizationToUpper_algebraMap K hm hn]
    rfl)

noncomputable instance criticalSchurNormalLocalization_isFractionRing
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsFractionRing (CriticalSchurNormalLocalization K hm hn)
      (criticalNormalClosure K m n) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (criticalSchurNormalIntegralClosurePrime K hm hn).primeCompl
    (CriticalSchurNormalLocalization K hm hn)
    (criticalNormalClosure K m n)

theorem criticalSchurNormalLocalizationToUpper_comp_subtype
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (criticalNormalClosureSchurValuationSubring K hm hn).subtype.comp
        (criticalSchurNormalLocalizationToUpper K hm hn) =
      algebraMap (CriticalSchurNormalLocalization K hm hn)
        (criticalNormalClosure K m n) :=
  rfl

theorem criticalSchurNormalLocalizationToUpper_rangeRestrict_bijective
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Function.Bijective
      ((criticalNormalClosureSchurValuationSubring K hm hn).subtype.rangeRestrict.comp
        (criticalSchurNormalLocalizationToUpper K hm hn)) :=
  bijective_rangeRestrict_comp_of_valuationRing
    (R := CriticalSchurNormalLocalization K hm hn)
    (S := criticalNormalClosureSchurValuationSubring K hm hn)
    (K := criticalNormalClosure K m n)
    (criticalSchurNormalLocalizationToUpper K hm hn)
    (criticalNormalClosureSchurValuationSubring K hm hn).subtype
    (criticalSchurNormalLocalizationToUpper_comp_subtype K hm hn)

theorem criticalSchurNormalLocalizationToUpper_bijective
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Function.Bijective (criticalSchurNormalLocalizationToUpper K hm hn) := by
  let A := criticalNormalClosureSchurValuationSubring K hm hn
  let φ := criticalSchurNormalLocalizationToUpper K hm hn
  let g : A →+* criticalNormalClosure K m n := A.subtype
  have hcompbij :=
    criticalSchurNormalLocalizationToUpper_rangeRestrict_bijective K hm hn
  constructor
  · intro x y hxy
    apply hcompbij.1
    exact congrArg g.rangeRestrict hxy
  · intro a
    obtain ⟨x, hx⟩ := hcompbij.2 (g.rangeRestrict a)
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change g (φ x) = g a
    exact congrArg (fun z : g.range => (z : criticalNormalClosure K m n)) hx

/-- The localization of the normal integral closure at the contracted Schur prime is canonically
the already-chosen upper valuation ring. -/
noncomputable def criticalSchurNormalLocalizationEquivUpper
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    CriticalSchurNormalLocalization K hm hn ≃ₐ[
      CriticalSchurNormalIntegralClosure K hm hn]
      criticalNormalClosureSchurValuationSubring K hm hn :=
  { RingEquiv.ofBijective (criticalSchurNormalLocalizationToUpper K hm hn)
      (criticalSchurNormalLocalizationToUpper_bijective K hm hn) with
    commutes' := criticalSchurNormalLocalizationToUpper_algebraMap K hm hn }

/-- The chosen upper Schur valuation ring is the localization at its contracted integral-closure
prime. -/
noncomputable instance criticalSchurNormalUpper_isLocalization
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    IsLocalization (criticalSchurNormalIntegralClosurePrime K hm hn).primeCompl
      (criticalNormalClosureSchurValuationSubring K hm hn) :=
  IsLocalization.isLocalization_of_algEquiv _
    (criticalSchurNormalLocalizationEquivUpper K hm hn)

/-- The actual normal-closure Galois group acts on the Schur integral closure. -/
noncomputable instance criticalSchurNormalIntegralClosure_galoisAction
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    MulSemiringAction
      (criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
        criticalNormalClosure K m n)
      (CriticalSchurNormalIntegralClosure K hm hn) := by
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K hm hn
  exact IsIntegralClosure.MulSemiringAction
    (CriticalSchurNormalBaseRing K hm hn)
    (criticalObservationField K m n)
    (criticalNormalClosure K m n)
    (CriticalSchurNormalIntegralClosure K hm hn)

/-- Ideal-theoretic inertia group of the integral-closure prime corresponding to the chosen Schur
valuation. -/
abbrev criticalSchurIdealInertiaGroup
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :=
  (criticalSchurNormalIntegralClosurePrime K hm hn).inertia
    (criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
      criticalNormalClosure K m n)

/-- Ring automorphism induced by an ideal-inertia element on the normal integral closure. -/
noncomputable def criticalSchurIdealInertiaIntegralClosureEquiv
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalSchurIdealInertiaGroup K hm hn) :
    CriticalSchurNormalIntegralClosure K hm hn ≃+*
      CriticalSchurNormalIntegralClosure K hm hn :=
  MulSemiringAction.toRingAut
    (criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
      criticalNormalClosure K m n)
    (CriticalSchurNormalIntegralClosure K hm hn) σ

@[simp] theorem criticalSchurIdealInertiaIntegralClosureEquiv_coe
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalSchurIdealInertiaGroup K hm hn)
    (x : CriticalSchurNormalIntegralClosure K hm hn) :
    ((criticalSchurIdealInertiaIntegralClosureEquiv K hm hn σ x :
        CriticalSchurNormalIntegralClosure K hm hn) :
      criticalNormalClosure K m n) =
      (σ : criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
        criticalNormalClosure K m n) • (x : criticalNormalClosure K m n) :=
  rfl

/-- Ideal inertia preserves the complement of the contracted prime. -/
theorem criticalSchurIdealInertiaIntegralClosureEquiv_map_primeCompl
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalSchurIdealInertiaGroup K hm hn) :
    (criticalSchurNormalIntegralClosurePrime K hm hn).primeCompl.map
        (criticalSchurIdealInertiaIntegralClosureEquiv K hm hn σ).toMonoidHom =
      (criticalSchurNormalIntegralClosurePrime K hm hn).primeCompl := by
  let S := CriticalSchurNormalIntegralClosure K hm hn
  let P := criticalSchurNormalIntegralClosurePrime K hm hn
  let τ := criticalSchurIdealInertiaIntegralClosureEquiv K hm hn σ
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change τ x ∉ P
    intro hτx
    apply hx
    have hdiff : τ x - x ∈ P := by
      exact σ.property x
    have hmem := P.sub_mem hτx hdiff
    simpa using hmem
  · intro y hy
    refine ⟨τ.symm y, ?_, τ.apply_symm_apply y⟩
    change τ.symm y ∉ P
    intro hpre
    apply hy
    have hdiff : τ (τ.symm y) - τ.symm y ∈ P := by
      exact σ.property (τ.symm y)
    have hmem := P.add_mem hdiff hpre
    simpa using hmem

/-- Localized automorphism of the chosen upper valuation ring attached to ideal inertia. -/
noncomputable def criticalSchurIdealInertiaUpperEquiv
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalSchurIdealInertiaGroup K hm hn) :
    criticalNormalClosureSchurValuationSubring K hm hn ≃+*
      criticalNormalClosureSchurValuationSubring K hm hn :=
  IsLocalization.ringEquivOfRingEquiv
    (criticalNormalClosureSchurValuationSubring K hm hn)
    (criticalNormalClosureSchurValuationSubring K hm hn)
    (criticalSchurIdealInertiaIntegralClosureEquiv K hm hn σ)
    (criticalSchurIdealInertiaIntegralClosureEquiv_map_primeCompl K hm hn σ)

@[simp] theorem criticalSchurIdealInertiaUpperEquiv_algebraMap
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalSchurIdealInertiaGroup K hm hn)
    (x : CriticalSchurNormalIntegralClosure K hm hn) :
    criticalSchurIdealInertiaUpperEquiv K hm hn σ
        (algebraMap (CriticalSchurNormalIntegralClosure K hm hn)
          (criticalNormalClosureSchurValuationSubring K hm hn) x) =
      algebraMap (CriticalSchurNormalIntegralClosure K hm hn)
        (criticalNormalClosureSchurValuationSubring K hm hn)
        (criticalSchurIdealInertiaIntegralClosureEquiv K hm hn σ x) :=
  IsLocalization.ringEquivOfRingEquiv_eq
    (criticalNormalClosureSchurValuationSubring K hm hn)
    (criticalNormalClosureSchurValuationSubring K hm hn)
    (criticalSchurIdealInertiaIntegralClosureEquiv_map_primeCompl K hm hn σ) x

/-- The localized automorphism is the restriction of the original normal-closure automorphism. -/
theorem criticalSchurIdealInertiaUpperEquiv_coe
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalSchurIdealInertiaGroup K hm hn)
    (a : criticalNormalClosureSchurValuationSubring K hm hn) :
    ((criticalSchurIdealInertiaUpperEquiv K hm hn σ a :
        criticalNormalClosureSchurValuationSubring K hm hn) :
      criticalNormalClosure K m n) =
      (σ : criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
        criticalNormalClosure K m n) • (a : criticalNormalClosure K m n) := by
  let S := CriticalSchurNormalIntegralClosure K hm hn
  let P := criticalSchurNormalIntegralClosurePrime K hm hn
  let A := criticalNormalClosureSchurValuationSubring K hm hn
  let E := criticalNormalClosure K m n
  let G := E ≃ₐ[criticalObservationField K m n] E
  let e := criticalSchurIdealInertiaUpperEquiv K hm hn σ
  have hhom : A.subtype.comp e.toRingHom =
      (σ : G).toRingHom.comp A.subtype := by
    apply IsLocalization.ringHom_ext P.primeCompl
    apply RingHom.ext
    intro x
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      criticalSchurIdealInertiaUpperEquiv_algebraMap K hm hn,
      RingHom.comp_apply]
    change
      ((criticalSchurIdealInertiaIntegralClosureEquiv K hm hn σ x : S) : E) =
        (σ : G) • (x : E)
    exact criticalSchurIdealInertiaIntegralClosureEquiv_coe K hm hn σ x
  exact RingHom.congr_fun hhom a

/-- Every ideal-inertia automorphism stabilizes the chosen upper valuation ring. -/
theorem criticalSchurIdealInertia_mem_decompositionGroup
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalSchurIdealInertiaGroup K hm hn) :
    (σ : criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
      criticalNormalClosure K m n) ∈ criticalSchurDecompositionGroup K hm hn := by
  let A := criticalNormalClosureSchurValuationSubring K hm hn
  let E := criticalNormalClosure K m n
  let G := E ≃ₐ[criticalObservationField K m n] E
  let e := criticalSchurIdealInertiaUpperEquiv K hm hn σ
  change (σ : G) • A = A
  apply SetLike.ext
  intro x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨a, ha, rfl⟩
    let aA : A := ⟨a, ha⟩
    have he := criticalSchurIdealInertiaUpperEquiv_coe K hm hn σ aA
    rw [← he]
    exact (e aA).property
  · intro hx
    let xA : A := ⟨x, hx⟩
    let aA : A := e.symm xA
    refine ⟨(aA : E), aA.property, ?_⟩
    calc
      (σ : G) • (aA : E) = (e aA : A) :=
        (criticalSchurIdealInertiaUpperEquiv_coe K hm hn σ aA).symm
      _ = x := congrArg Subtype.val (e.apply_symm_apply xA)

/-- Identity-on-automorphisms homomorphism from ideal inertia to place decomposition. -/
noncomputable def criticalSchurIdealInertiaToDecomposition
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSchurIdealInertiaGroup K hm hn →*
      criticalSchurDecompositionGroup K hm hn where
  toFun σ := ⟨σ, criticalSchurIdealInertia_mem_decompositionGroup K hm hn σ⟩
  map_one' := by apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; rfl

@[simp] theorem criticalSchurIdealInertiaToDecomposition_smul_upper
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalSchurIdealInertiaGroup K hm hn)
    (a : criticalNormalClosureSchurValuationSubring K hm hn) :
    criticalSchurIdealInertiaToDecomposition K hm hn σ • a =
      criticalSchurIdealInertiaUpperEquiv K hm hn σ a := by
  apply Subtype.ext
  exact (criticalSchurIdealInertiaUpperEquiv_coe K hm hn σ a).symm

/-- Ideal inertia acts trivially on the residue field of the localized upper ring. -/
theorem criticalSchurIdealInertiaUpperEquiv_residue
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalSchurIdealInertiaGroup K hm hn)
    (a : criticalNormalClosureSchurValuationSubring K hm hn) :
    IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K hm hn)
        (criticalSchurIdealInertiaUpperEquiv K hm hn σ a) =
      IsLocalRing.residue (criticalNormalClosureSchurValuationSubring K hm hn) a := by
  let S := CriticalSchurNormalIntegralClosure K hm hn
  let P := criticalSchurNormalIntegralClosurePrime K hm hn
  let A := criticalNormalClosureSchurValuationSubring K hm hn
  let e := criticalSchurIdealInertiaUpperEquiv K hm hn σ
  have hhom : (IsLocalRing.residue A).comp e.toRingHom =
      IsLocalRing.residue A := by
    apply IsLocalization.ringHom_ext P.primeCompl
    apply RingHom.ext
    intro x
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      criticalSchurIdealInertiaUpperEquiv_algebraMap K hm hn]
    rw [← sub_eq_zero, ← map_sub, ← map_sub]
    apply (IsLocalRing.residue_eq_zero_iff _).2
    change criticalSchurNormalIntegralClosureToUpper K hm hn
        (criticalSchurIdealInertiaIntegralClosureEquiv K hm hn σ x - x) ∈
      IsLocalRing.maximalIdeal A
    exact σ.property x
  exact RingHom.congr_fun hhom a

/-- The decomposition element underlying ideal inertia lies in valuation-theoretic inertia. -/
theorem criticalSchurIdealInertiaToDecomposition_mem_inertia
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (σ : criticalSchurIdealInertiaGroup K hm hn) :
    criticalSchurIdealInertiaToDecomposition K hm hn σ ∈
      criticalSchurInertiaGroup K hm hn := by
  let A := criticalNormalClosureSchurValuationSubring K hm hn
  let D := criticalSchurDecompositionGroup K hm hn
  change MulSemiringAction.toRingAut D (IsLocalRing.ResidueField A)
      (criticalSchurIdealInertiaToDecomposition K hm hn σ) = 1
  apply DFunLike.ext _ _
  intro z
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective z
  change criticalSchurIdealInertiaToDecomposition K hm hn σ •
      IsLocalRing.residue A a = IsLocalRing.residue A a
  rw [← IsLocalRing.ResidueField.residue_smul]
  rw [criticalSchurIdealInertiaToDecomposition_smul_upper K hm hn]
  exact criticalSchurIdealInertiaUpperEquiv_residue K hm hn σ a

/-- Canonical injective homomorphism from ideal-theoretic inertia to the chosen-place inertia. -/
noncomputable def criticalSchurIdealInertiaToInertia
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalSchurIdealInertiaGroup K hm hn →*
      criticalSchurInertiaGroup K hm hn :=
  MonoidHom.codRestrict (criticalSchurIdealInertiaToDecomposition K hm hn)
    (criticalSchurInertiaGroup K hm hn)
    (criticalSchurIdealInertiaToDecomposition_mem_inertia K hm hn)

theorem criticalSchurIdealInertiaToInertia_injective
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Function.Injective (criticalSchurIdealInertiaToInertia K hm hn) := by
  intro σ τ hστ
  apply Subtype.ext
  exact congrArg
    (fun g : criticalSchurInertiaGroup K hm hn =>
      ((g : criticalSchurDecompositionGroup K hm hn) :
        criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
          criticalNormalClosure K m n)) hστ

/-- Ground-field constants are integral at the observation Schur place. -/
theorem criticalObservationSchur_algebraMap_mem
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (x : K) :
    algebraMap K (criticalObservationField K m n) x ∈
      CriticalSchurNormalBaseRing K hm hn := by
  rw [mem_criticalSchurObservationValuationSubring_iff]
  rw [mem_criticalSchurSourceValuationSubring_iff]
  have hmem := criticalSchurCoordinateValuationSubring_algebraMap_mem K hm hn
    (MvPolynomial.C x : criticalSchurSourceRing K m n)
  convert hmem using 1
  apply (criticalSourceSchurFieldEquiv K hm hn).injective
  rw [(criticalSourceSchurFieldEquiv K hm hn).apply_symm_apply]
  rw [criticalSourceSchurFieldEquiv_algebraMap_apply K hm hn]
  simp only [MvPolynomial.aeval_C]
  rw [IsScalarTower.algebraMap_apply K (criticalObservationField K m n)
    (criticalSourceField K m n)]

/-- Ground-field constants as elements of the observation Schur DVR. -/
noncomputable def criticalObservationSchurConstantBaseMap
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    K →+* CriticalSchurNormalBaseRing K hm hn :=
  RingHom.codRestrict (algebraMap K (criticalObservationField K m n))
    (CriticalSchurNormalBaseRing K hm hn)
    (criticalObservationSchur_algebraMap_mem K hm hn)

/-- Composite embedding of ground-field constants into the observation Schur residue field. -/
noncomputable def criticalObservationSchurConstantResidueMap
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    K →+* IsLocalRing.ResidueField (CriticalSchurNormalBaseRing K hm hn) :=
  (IsLocalRing.residue (CriticalSchurNormalBaseRing K hm hn)).comp
    (criticalObservationSchurConstantBaseMap K hm hn)

/-- The observation Schur residue field has characteristic zero. -/
noncomputable instance criticalObservationSchurResidue_charZero
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    CharZero (IsLocalRing.ResidueField (CriticalSchurNormalBaseRing K hm hn)) :=
  (RingHom.charZero_iff
    (criticalObservationSchurConstantResidueMap K hm hn).injective).mp inferInstance

/-- Ground-field constants in the ideal-theoretic residue field of the maximal Schur ideal. -/
noncomputable def criticalObservationSchurPrimeConstantResidueMap
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    K →+* (IsLocalRing.maximalIdeal
      (CriticalSchurNormalBaseRing K hm hn)).ResidueField :=
  (algebraMap
      ((CriticalSchurNormalBaseRing K hm hn) ⧸
        IsLocalRing.maximalIdeal (CriticalSchurNormalBaseRing K hm hn))
      (IsLocalRing.maximalIdeal
        (CriticalSchurNormalBaseRing K hm hn)).ResidueField).comp
    ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      (CriticalSchurNormalBaseRing K hm hn))).comp
        (criticalObservationSchurConstantBaseMap K hm hn))

/-- The ideal-theoretic residue field at the observation Schur prime has characteristic zero. -/
noncomputable instance criticalObservationSchurPrimeResidue_charZero
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    CharZero ((IsLocalRing.maximalIdeal
      (CriticalSchurNormalBaseRing K hm hn)).ResidueField) :=
  (RingHom.charZero_iff
    (criticalObservationSchurPrimeConstantResidueMap K hm hn).injective).mp inferInstance

/-- Cardinality of ideal-theoretic Schur inertia is exactly the ramification index in the normal
integral closure. -/
theorem natCard_criticalSchurIdealInertiaGroup_eq_ramificationIdxIn
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Nat.card (criticalSchurIdealInertiaGroup K hm hn) =
      Ideal.ramificationIdxIn
        (IsLocalRing.maximalIdeal (CriticalSchurNormalBaseRing K hm hn))
        (CriticalSchurNormalIntegralClosure K hm hn) := by
  let F := criticalObservationField K m n
  let E := criticalSourceField K m n
  let L := criticalNormalClosure K m n
  let O := CriticalSchurNormalBaseRing K hm hn
  let S := CriticalSchurNormalIntegralClosure K hm hn
  let p := IsLocalRing.maximalIdeal O
  let P := criticalSchurNormalIntegralClosurePrime K hm hn
  let G := L ≃ₐ[F] L
  letI : FiniteDimensional F E :=
    criticalSourceField_finiteDimensional_criticalObservationField K hm hn
  letI : Algebra.IsSeparable F E := inferInstance
  letI : IsScalarTower F E (criticalSourceAlgebraicClosure K m n) :=
    AlgebraicClosure.instIsScalarTower E
  letI : Algebra.IsAlgebraic F (criticalSourceAlgebraicClosure K m n) :=
    Algebra.IsAlgebraic.trans F E (criticalSourceAlgebraicClosure K m n)
  letI : Normal F (criticalSourceAlgebraicClosure K m n) :=
    { splits' _ := IsAlgClosed.splits _ }
  letI : FiniteDimensional F L := criticalNormalClosure_finiteDimensional K hm hn
  letI : Normal F L :=
    normalClosure.normal F E (criticalSourceAlgebraicClosure K m n)
  letI : IsGalois F L := inferInstance
  letI : IsGaloisGroup G O S :=
    IsGaloisGroup.of_isFractionRing G O S F L
  letI : Finite G := IsGaloisGroup.finite G O S
  letI : Module.Flat O S := inferInstance
  letI : P.LiesOver p := criticalSchurNormalIntegralClosurePrime_liesOver K hm hn
  simpa [F, L, O, S, p, P, G] using
    (Ideal.card_inertia_eq_ramificationIdxIn (G := G) p P)

end

end GaloisForLFunctions.HTGeometry
