import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeLogRegulator
import GaloisForLFunctions.RHTower.Deninger.DeningerPositiveSteinbergCyclicComparison

/-!
# Explicit prime tangents invisible to the scalar regulator

Positive prime basis differences realize arbitrary finite prime moments in the
original rational-scaling group algebra. Applying this section to the complete
log-relation basis gives explicit complex-coefficient tangents with zero scalar
regulator. Each has nonzero prime moment and therefore survives the actual
positive Steinberg quotient.
-/

open scoped TensorProduct
noncomputable section
namespace RHTower
open GaloisForLFunctions.RHTower GaloisForLFunctions.HTGeometry
open PositiveSteinbergCyclic

/-- Positive rational prime tangents in the original source group algebra. -/
def deningerPrimeTangentSection : (Nat.Primes →₀ ℂ) →ₗ[ℂ] Source :=
  Finsupp.lsum ℂ (fun p => LinearMap.toSpanSingleton ℂ Source
    (deningerSteinbergBasis ⟨deningerPrimeUnit p⟩ - 1))

theorem deningerPrimeTangentSection_single (p : Nat.Primes) (z : ℂ) :
    deningerPrimeTangentSection (Finsupp.single p z) =
      z • (deningerSteinbergBasis ⟨deningerPrimeUnit p⟩ - 1) := by
  simp [deningerPrimeTangentSection]

theorem deningerPrimeMoment_one : deningerPrimeMoment 1 = 0 := by
  change deningerPrimeMomentEquiv (GroupAlgebraFirstJet.jet ℂ CCMRationalAdelicScaling 1).snd = 0
  rw [map_one]
  exact map_zero _

theorem deningerPrimeMoment_prime (p : Nat.Primes) :
    deningerPrimeMoment (deningerSteinbergBasis ⟨deningerPrimeUnit p⟩) = Finsupp.single p 1 := by
  change deningerPrimeMomentEquiv (GroupAlgebraFirstJet.jet ℂ CCMRationalAdelicScaling
    (MonoidAlgebra.of ℂ _ ⟨deningerPrimeUnit p⟩)).snd = _
  rw [GroupAlgebraFirstJet.jet_of]
  exact deningerPrimeMomentEquiv_prime p

/-- Prime tangents realize arbitrary finitely supported prime moments. -/
theorem deningerPrimeTangentSection_right_inverse (x : Nat.Primes →₀ ℂ) :
    deningerPrimeMoment (deningerPrimeTangentSection x) = x := by
  have h : deningerPrimeMoment.comp deningerPrimeTangentSection = LinearMap.id := by
    apply (Finsupp.basisSingleOne : Module.Basis Nat.Primes ℂ (Nat.Primes →₀ ℂ)).ext
    intro p
    change deningerPrimeMoment (deningerPrimeTangentSection (Finsupp.single p 1)) = _
    rw [deningerPrimeTangentSection_single, one_smul, map_sub,
      deningerPrimeMoment_prime, deningerPrimeMoment_one, sub_zero]
    rfl
  exact LinearMap.congr_fun h x

/-- Every weighted prime relation gives a scalar-invisible source tangent. -/
def deningerHiddenPrimeTangent (p : DeningerPrimeLogAway) : Source :=
  deningerPrimeTangentSection (deningerPrimeLogKernelBasis p).val

theorem deningerHiddenPrimeTangent_eq (p : DeningerPrimeLogAway) :
    deningerHiddenPrimeTangent p =
      (deningerSteinbergBasis ⟨deningerPrimeUnit p.val⟩ - 1) -
      ((Real.log (p.val : ℝ) : ℂ) / (Real.log (2 : ℝ) : ℂ)) •
        (deningerSteinbergBasis ⟨deningerPrimeUnit deningerPrimeLogPivot⟩ - 1) := by
  rw [deningerHiddenPrimeTangent, deningerPrimeLogKernelBasis_apply, map_sub,
    deningerPrimeTangentSection_single, deningerPrimeTangentSection_single, one_smul]

theorem deningerHiddenPrimeTangent_augmentation (p : DeningerPrimeLogAway) :
    deningerKummerAugmentation (deningerHiddenPrimeTangent p) = 0 := by
  simp only [deningerHiddenPrimeTangent_eq, map_sub, map_smul,
    deningerKummerAugmentation_basis, map_one, sub_self, smul_zero]

theorem deningerHiddenPrimeTangent_regulator (p : DeningerPrimeLogAway) :
    deningerKummerRegulator (deningerHiddenPrimeTangent p) = 0 := by
  rw [deningerKummerRegulator_eq_primeLog]
  change deningerPrimeLog (deningerPrimeMoment (deningerPrimeTangentSection _)) = 0
  rw [deningerPrimeTangentSection_right_inverse]
  exact (deningerPrimeLogKernelBasis p).property

/-- These invisible directions survive the actual positive Steinberg quotient. -/
theorem deningerHiddenPrimeTangent_not_mem (p : DeningerPrimeLogAway) :
    deningerHiddenPrimeTangent p ∉ deningerKummerSteinbergIdeal := by
  intro h
  have hm := (deningerSteinberg_mem_iff_prime_moments _).mp h
  have hz : deningerPrimeMoment (deningerHiddenPrimeTangent p) = 0 := Finsupp.ext hm.2.1
  change deningerPrimeMoment (deningerPrimeTangentSection _) = 0 at hz
  rw [deningerPrimeTangentSection_right_inverse] at hz
  exact (deningerPrimeLogKernelBasis.ne_zero p) (Subtype.ext hz)

#print axioms deningerPrimeTangentSection_right_inverse
#print axioms deningerHiddenPrimeTangent_augmentation
#print axioms deningerHiddenPrimeTangent_regulator
#print axioms deningerHiddenPrimeTangent_not_mem
end RHTower
