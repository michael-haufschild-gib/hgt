import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeHochschild
import GaloisForLFunctions.RHTower.Deninger.DeningerHiddenPrimeTangents

/-!
# Scalar-invisible source tangents in Hochschild homology

The original positive prime section occupies the diagonal of the ordinary and
signed first-order sectors. Its full logarithmic relation space injects into
Hochschild degree one. The associated square-zero unit cycles are non-boundaries
with zero scalar detector, yet vanish after imposing ordinary cyclic relations.
-/

noncomputable section
namespace RHTower
open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.SquareZeroCyclic
open PositiveSteinbergCyclic

theorem deningerPrimeTangentSection_augmentation (x : Nat.Primes →₀ ℂ) :
    deningerKummerAugmentation (deningerPrimeTangentSection x) = 0 := by
  have h : deningerKummerAugmentation.toLinearMap.comp deningerPrimeTangentSection = 0 := by
    apply (Finsupp.basisSingleOne : Module.Basis Nat.Primes ℂ (Nat.Primes →₀ ℂ)).ext
    intro p
    change deningerKummerAugmentation (deningerPrimeTangentSection (Finsupp.single p 1)) = 0
    rw [deningerPrimeTangentSection_single, one_smul, map_sub,
      deningerKummerAugmentation_basis, map_one, sub_self]
  exact LinearMap.congr_fun h x

private theorem signAugmentation_prime (p : Nat.Primes) :
    deningerKummerSignAugmentation (deningerSteinbergBasis ⟨deningerPrimeUnit p⟩) = 1 := by
  have hp : 0 < (p : ℚ) := by exact_mod_cast p.property.pos
  simpa only [deningerPrimeUnit, deningerScalingOfPositiveRational] using
    deningerKummerSignAugmentation_positive (p : ℚ) hp

theorem deningerPrimeTangentSection_signAugmentation (x : Nat.Primes →₀ ℂ) :
    deningerKummerSignAugmentation (deningerPrimeTangentSection x) = 0 := by
  have h : deningerKummerSignAugmentation.toLinearMap.comp deningerPrimeTangentSection = 0 := by
    apply (Finsupp.basisSingleOne : Module.Basis Nat.Primes ℂ (Nat.Primes →₀ ℂ)).ext
    intro p
    change deningerKummerSignAugmentation (deningerPrimeTangentSection (Finsupp.single p 1)) = 0
    rw [deningerPrimeTangentSection_single, one_smul, map_sub,
      signAugmentation_prime, map_one, sub_self]
  exact LinearMap.congr_fun h x

private theorem signedPrimeMoment_prime (p : Nat.Primes) :
    deningerSignedPrimeMoment (deningerSteinbergBasis ⟨deningerPrimeUnit p⟩) =
      Finsupp.single p 1 := by
  rw [← deningerPrimeMoment_prime p]
  ext r
  rw [deningerSignedPrimeMoment_basis, signAugmentation_prime, one_mul,
    deningerPrimeMoment_basis]

private theorem signedPrimeMoment_one : deningerSignedPrimeMoment 1 = 0 := by
  change deningerPrimeMomentEquiv (deningerSignedFirstJet 1).snd = 0
  rw [map_one]
  exact map_zero _

theorem deningerPrimeTangentSection_signedMoment (x : Nat.Primes →₀ ℂ) :
    deningerSignedPrimeMoment (deningerPrimeTangentSection x) = x := by
  have h : deningerSignedPrimeMoment.comp deningerPrimeTangentSection = LinearMap.id := by
    apply (Finsupp.basisSingleOne : Module.Basis Nat.Primes ℂ (Nat.Primes →₀ ℂ)).ext
    intro p
    change deningerSignedPrimeMoment (deningerPrimeTangentSection (Finsupp.single p 1)) = _
    rw [deningerPrimeTangentSection_single, one_smul, map_sub,
      signedPrimeMoment_prime, signedPrimeMoment_one, sub_zero]
    rfl
  exact LinearMap.congr_fun h x

/-- Positive prime source tangents occupy the diagonal of the two sign sectors. -/
theorem deningerPrimeTangentSection_quotient (x : Nat.Primes →₀ ℂ) :
    quotientMap (deningerPrimeTangentSection x) = deningerPairedPrimeTangent (x, x) := by
  apply deningerSteinbergPrimeEquiv.injective
  rw [deningerPairedPrimeTangent_coordinates]
  apply Prod.ext
  · apply TrivSqZeroExt.ext
    · change deningerPrimeAugmentation (quotientMap (deningerPrimeTangentSection x)) = 0
      rw [deningerPrimeAugmentation_quotientMap, deningerPrimeTangentSection_augmentation]
    · change deningerQuotientPrimeMoment (quotientMap (deningerPrimeTangentSection x)) = x
      rw [deningerQuotientPrimeMoment_quotientMap, deningerPrimeTangentSection_right_inverse]
  · apply TrivSqZeroExt.ext
    · change deningerSignedPrimeAugmentation (quotientMap (deningerPrimeTangentSection x)) = 0
      rw [deningerSignedPrimeAugmentation_quotientMap, deningerPrimeTangentSection_signAugmentation]
    · change deningerQuotientSignedPrimeMoment (quotientMap (deningerPrimeTangentSection x)) = x
      rw [deningerQuotientSignedPrimeMoment_quotientMap, deningerPrimeTangentSection_signedMoment]

/-- The original positive prime tangents inject into Hochschild degree one. -/
def deningerSourcePrimeHochschild : (Nat.Primes →₀ ℂ) →ₗ[ℂ] HochschildOne Quotient :=
  (tangentClass (A := Quotient)).comp
    (quotientMap.toLinearMap.comp deningerPrimeTangentSection)

theorem deningerSourcePrimeHochschild_eq (x : Nat.Primes →₀ ℂ) :
    deningerSourcePrimeHochschild x = deningerPrimeHochschildClass (x, x) := by
  change tangentClass (A := Quotient) (quotientMap (deningerPrimeTangentSection x)) = _
  rw [deningerPrimeTangentSection_quotient]
  rfl

theorem deningerSourcePrimeHochschild_injective : Function.Injective deningerSourcePrimeHochschild := by
  intro x y h
  rw [deningerSourcePrimeHochschild_eq, deningerSourcePrimeHochschild_eq] at h
  exact congrArg Prod.fst (deningerPrimeHochschildClass_injective h)

/-- All scalar-invisible prime relations survive as a linear family in actual homology. -/
def deningerHiddenPrimeHochschild : deningerPrimeLog.ker →ₗ[ℂ] HochschildOne Quotient :=
  deningerSourcePrimeHochschild.comp deningerPrimeLog.ker.subtype

theorem deningerHiddenPrimeHochschild_injective : Function.Injective deningerHiddenPrimeHochschild := by
  intro x y h
  exact Subtype.ext (deningerSourcePrimeHochschild_injective h)

/-- The complete log-relation basis remains linearly independent in homology. -/
theorem deningerHiddenPrimeHochschild_linearIndependent :
    LinearIndependent ℂ (fun p : DeningerPrimeLogAway =>
      deningerHiddenPrimeHochschild (deningerPrimeLogKernelBasis p)) := by
  have hk : deningerHiddenPrimeHochschild.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr deningerHiddenPrimeHochschild_injective
  have hi := deningerPrimeLogKernelBasis.linearIndependent.map' deningerHiddenPrimeHochschild hk
  exact hi

/-- The explicit logarithmic prime-relation basis gives nonzero Hochschild classes. -/
theorem deningerHiddenPrimeHochschild_ne_zero (p : DeningerPrimeLogAway) :
    deningerHiddenPrimeHochschild (deningerPrimeLogKernelBasis p) ≠ 0 := by
  intro h
  apply deningerPrimeLogKernelBasis.ne_zero p
  apply deningerHiddenPrimeHochschild_injective
  rw [map_zero]
  exact h

/-- Each original scalar-invisible tangent has square zero in the actual quotient. -/
theorem deningerHiddenPrimeTangent_quotient_square (p : DeningerPrimeLogAway) :
    quotientMap (deningerHiddenPrimeTangent p) * quotientMap (deningerHiddenPrimeTangent p) = 0 := by
  simp only [deningerHiddenPrimeTangent, deningerPrimeTangentSection_quotient]
  exact deningerPairedPrimeTangent_mul _ _

/-- The unit cycle of the original hidden tangent represents its nonzero class. -/
theorem deningerHiddenPrimeUnit_class (p : DeningerPrimeLogAway) :
    (LinearMap.range (boundaryTwo (A := Quotient))).mkQ
      (pair (1-quotientMap (deningerHiddenPrimeTangent p))
        (1+quotientMap (deningerHiddenPrimeTangent p))) =
      deningerHiddenPrimeHochschild (deningerPrimeLogKernelBasis p) :=
  squareZeroUnit_class _ (deningerHiddenPrimeTangent_quotient_square p)

theorem deningerHiddenPrimeUnit_not_boundary (p : DeningerPrimeLogAway) :
    pair (1-quotientMap (deningerHiddenPrimeTangent p))
      (1+quotientMap (deningerHiddenPrimeTangent p)) ∉ LinearMap.range boundaryTwo := by
  intro h
  apply deningerHiddenPrimeHochschild_ne_zero p
  rw [← deningerHiddenPrimeUnit_class p]
  exact (Submodule.Quotient.mk_eq_zero _).mpr h

theorem deningerHiddenPrimeUnit_cyclic (p : DeningerPrimeLogAway) :
    pair (1-quotientMap (deningerHiddenPrimeTangent p))
      (1+quotientMap (deningerHiddenPrimeTangent p)) ∈ cyclicRelations :=
  unit_mem_cyclicRelations _ (deningerHiddenPrimeTangent_quotient_square p)

/-- The ordinary scalar detector vanishes on these genuine non-boundaries. -/
theorem deningerHiddenPrimeUnit_scalarDetector (p : DeningerPrimeLogAway) :
    augmentationDetector augmentation regulator
      (pair (1-quotientMap (deningerHiddenPrimeTangent p))
        (1+quotientMap (deningerHiddenPrimeTangent p))) = 0 := by
  rw [augmentationDetector_unit augmentation regulator regulator_one _ (by
    rw [augmentation_quotientMap, deningerHiddenPrimeTangent_augmentation]),
    regulator_quotientMap, deningerHiddenPrimeTangent_regulator]

#print axioms deningerHiddenPrimeHochschild_linearIndependent
#print axioms deningerHiddenPrimeHochschild_injective
#print axioms deningerHiddenPrimeUnit_not_boundary
#print axioms deningerHiddenPrimeUnit_cyclic
#print axioms deningerHiddenPrimeUnit_scalarDetector
end RHTower
