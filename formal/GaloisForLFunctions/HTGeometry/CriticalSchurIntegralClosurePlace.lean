import GaloisForLFunctions.HTGeometry.CriticalSchurNormalFibreReduction
import GaloisForLFunctions.HTGeometry.CriticalSchurValuationDVR
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Integral-closure model of the actual Schur place

The chosen valuation ring in the actual critical normal closure contains the integral closure of
the observation Schur DVR.  Contracting its maximal ideal therefore gives a canonical prime of
that integral closure.  This module supplies the global Dedekind-domain model needed to apply
ideal-theoretic ramification and inertia theorems to the already-constructed valuation place.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 500000
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
    intro x y hxy
    apply (algebraMap (CriticalSchurNormalBaseRing K hm hn)
      (criticalNormalClosure K m n)).injective
    simpa using congrArg
      (algebraMap (CriticalSchurNormalIntegralClosure K hm hn)
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
      criticalNormalClosureSchurValuationSubring K hm hn :=
  Subring.inclusion (fun x => criticalSchurNormalIntegralClosure_mem_upper K hm hn x)

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

end

end GaloisForLFunctions.HTGeometry
