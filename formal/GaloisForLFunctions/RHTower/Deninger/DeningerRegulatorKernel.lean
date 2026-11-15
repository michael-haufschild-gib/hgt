import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeLogRegulator
import GaloisForLFunctions.RHTower.Deninger.DeningerPositiveSteinbergCyclicComparison

/-!
# Complete algebra structure of the scalar regulator kernel

In the actual positive Steinberg quotient, the regulator reads only the
logarithm-weighted ordinary prime moment. Its vanishing locus is a subalgebra,
isomorphic to the product of a square-zero algebra on the log-relation kernel
and the unrestricted signed prime-moment algebra. This classifies all scalar
invisibility in the quotient, including both scalar coordinates.
-/

noncomputable section
namespace RHTower
open GaloisForLFunctions.RHTower
open PositiveSteinbergCyclic

/-- Evaluation of the first isomorphism theorem survives transport of its kernel ideal. -/
private theorem pairedFirstJetQuotient_cast_mk (I : Ideal Source)
    (h : RingHom.ker deningerPairedFirstJet.toRingHom = I) (a : Source) :
    (Eq.mp (congrArg (fun J : Ideal Source => (Source ⧸ J) ≃ₐ[ℂ]
      (TrivSqZeroExt ℂ DeningerMomentSpace × TrivSqZeroExt ℂ DeningerMomentSpace)) h)
      (Ideal.quotientKerAlgEquivOfSurjective deningerPairedFirstJet_surjective))
        (Ideal.Quotient.mk I a) = deningerPairedFirstJet a := by
  subst I
  rfl

theorem deningerSteinbergPrimeEquiv_quotientMap (a : Source) :
    deningerSteinbergPrimeEquiv (quotientMap a) =
      (deningerPrimeJetEquiv (deningerFirstJet a), deningerPrimeJetEquiv (deningerSignedFirstJet a)) := by
  have h : deningerSteinbergFirstJetEquiv (quotientMap a) = deningerPairedFirstJet a := by
    unfold deningerSteinbergFirstJetEquiv quotientMap
    exact pairedFirstJetQuotient_cast_mk deningerKummerSteinbergIdeal
      deningerPairedFirstJet_kernel a
  change (deningerPrimeJetEquiv.prodCongr deningerPrimeJetEquiv)
    (deningerSteinbergFirstJetEquiv (quotientMap a)) = _
  rw [h]
  rfl

/-- Prime-coordinate formula for the descended scalar regulator. -/
theorem deningerQuotientRegulator_eq (q : Quotient) :
    regulator q = deningerPrimeLog (deningerSteinbergPrimeEquiv q).1.snd := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  change deningerKummerRegulator a = _
  rw [deningerKummerRegulator_eq_primeLog]
  change deningerPrimeLog (deningerPrimeMoment a) =
    deningerPrimeLog (deningerSteinbergPrimeEquiv (quotientMap a)).1.snd
  rw [deningerSteinbergPrimeEquiv_quotientMap]
  exact congrArg deningerPrimeLog
    (TrivSqZeroExt.snd_map deningerPrimeMomentEquiv.toLinearMap (deningerFirstJet a)).symm

/-- The scalar regulator's vanishing locus is an algebra, by the Leibniz rule. -/
def deningerRegulatorKernel : Subalgebra ℂ Quotient where
  carrier := {q | regulator q = 0}
  zero_mem' := map_zero _
  one_mem' := regulator_one
  add_mem' := by intro x y hx hy; rw [Set.mem_setOf_eq, map_add, hx, hy, add_zero]
  mul_mem' := by intro x y hx hy; rw [Set.mem_setOf_eq, regulator_mul, hx, hy, mul_zero, zero_mul, add_zero]
  algebraMap_mem' z := by
    change regulator (algebraMap ℂ Quotient z) = 0
    rw [Algebra.algebraMap_eq_smul_one, map_smul, regulator_one, smul_zero]

abbrev DeningerRegulatorKernelCoordinates :=
  TrivSqZeroExt ℂ deningerPrimeLog.ker × TrivSqZeroExt ℂ (Nat.Primes →₀ ℂ)

/-- Inclusion of the log-relation prime sector and the unrestricted signed sector. -/
def deningerRegulatorKernelInclusion : DeningerRegulatorKernelCoordinates →ₐ[ℂ]
    (TrivSqZeroExt ℂ (Nat.Primes →₀ ℂ) × TrivSqZeroExt ℂ (Nat.Primes →₀ ℂ)) :=
  (TrivSqZeroExt.map deningerPrimeLog.ker.subtype).prodMap (AlgHom.id ℂ _)

@[simp] theorem deningerRegulatorKernelInclusion_fst_fst
    (x : DeningerRegulatorKernelCoordinates) :
    (deningerRegulatorKernelInclusion x).1.fst = x.1.fst := by
  change (TrivSqZeroExt.map deningerPrimeLog.ker.subtype x.1).fst = x.1.fst
  exact TrivSqZeroExt.fst_map _ _

@[simp] theorem deningerRegulatorKernelInclusion_fst_snd
    (x : DeningerRegulatorKernelCoordinates) :
    (deningerRegulatorKernelInclusion x).1.snd = x.1.snd.val := by
  change (TrivSqZeroExt.map deningerPrimeLog.ker.subtype x.1).snd = x.1.snd.val
  exact TrivSqZeroExt.snd_map _ _

@[simp] theorem deningerRegulatorKernelInclusion_snd
    (x : DeningerRegulatorKernelCoordinates) :
    (deningerRegulatorKernelInclusion x).2 = x.2 := rfl

def deningerRegulatorKernelMap : DeningerRegulatorKernelCoordinates →ₐ[ℂ]
    deningerRegulatorKernel :=
  ((deningerSteinbergPrimeEquiv.symm.toAlgHom).comp deningerRegulatorKernelInclusion).codRestrict
    deningerRegulatorKernel (by
      intro x
      change regulator (deningerSteinbergPrimeEquiv.symm (deningerRegulatorKernelInclusion x)) = 0
      rw [deningerQuotientRegulator_eq, AlgEquiv.apply_symm_apply,
        deningerRegulatorKernelInclusion_fst_snd]
      exact x.1.snd.property)

theorem deningerRegulatorKernelMap_bijective : Function.Bijective deningerRegulatorKernelMap := by
  constructor
  · intro x y h
    have hc := congrArg (fun q : deningerRegulatorKernel => deningerSteinbergPrimeEquiv q.val) h
    change deningerSteinbergPrimeEquiv
      (deningerSteinbergPrimeEquiv.symm (deningerRegulatorKernelInclusion x)) =
      deningerSteinbergPrimeEquiv
        (deningerSteinbergPrimeEquiv.symm (deningerRegulatorKernelInclusion y)) at hc
    simp only [AlgEquiv.apply_symm_apply] at hc
    apply Prod.ext
    · apply TrivSqZeroExt.ext
      · have he := congrArg (fun z => z.1.fst) hc
        simpa only [deningerRegulatorKernelInclusion_fst_fst] using he
      · apply Subtype.ext
        have he := congrArg (fun z => z.1.snd) hc
        simpa only [deningerRegulatorKernelInclusion_fst_snd] using he
    · have he := congrArg Prod.snd hc
      simpa only [deningerRegulatorKernelInclusion_snd] using he
  · intro q
    let c := deningerSteinbergPrimeEquiv q.val
    have hc : deningerPrimeLog c.1.snd = 0 := by
      rw [← deningerQuotientRegulator_eq]
      exact q.property
    refine ⟨(⟨c.1.fst, ⟨c.1.snd, hc⟩⟩, c.2), ?_⟩
    apply Subtype.ext
    change deningerSteinbergPrimeEquiv.symm
      (deningerRegulatorKernelInclusion (⟨c.1.fst, ⟨c.1.snd, hc⟩⟩, c.2)) = q.val
    apply deningerSteinbergPrimeEquiv.injective
    rw [AlgEquiv.apply_symm_apply]
    change deningerRegulatorKernelInclusion (⟨c.1.fst, ⟨c.1.snd, hc⟩⟩, c.2) = c
    apply Prod.ext
    · apply TrivSqZeroExt.ext
      · exact deningerRegulatorKernelInclusion_fst_fst _
      · exact deningerRegulatorKernelInclusion_fst_snd _
    · exact deningerRegulatorKernelInclusion_snd _

/-- Complete algebra structure of the actual quotient regulator's kernel. -/
def deningerRegulatorKernelEquiv : DeningerRegulatorKernelCoordinates ≃ₐ[ℂ]
    deningerRegulatorKernel :=
  AlgEquiv.ofBijective deningerRegulatorKernelMap deningerRegulatorKernelMap_bijective

#print axioms deningerQuotientRegulator_eq
#print axioms deningerRegulatorKernelEquiv
end RHTower
