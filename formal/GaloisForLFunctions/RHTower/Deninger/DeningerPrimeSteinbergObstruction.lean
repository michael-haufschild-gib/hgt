import GaloisForLFunctions.RHTower.Deninger.DeningerFirstJetClassification
import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeMomentCoordinates

/-!
# Exact prime-moment obstructions to rational Steinberg relations

A rational basis label `[q]` has prime moments `vₚ(q)`, and its sign-twisted
moments are `sign(q) vₚ(q)`. The positive Steinberg ideal is precisely the
simultaneous kernel of ordinary and sign augmentations and both moment families.

The complete quotient algebra is a product of two square-zero extensions of `ℂ`
by finitely supported complex prime coordinates. Chinese remaindering makes the
two components independent.
-/

open scoped TensorProduct
noncomputable section
namespace RHTower
open GaloisForLFunctions.RHTower GaloisForLFunctions.HTGeometry.GroupAlgebraFirstJet

theorem deningerPrimeMomentEquiv_label (g : CCMRationalAdelicScaling) (p : Nat.Primes) :
    deningerPrimeMomentEquiv ((1 : ℂ) ⊗ₜ[ℤ] Additive.ofMul g) p =
      (padicValRat (p : ℕ) (g.val : ℚ) : ℂ) := by
  change TensorProduct.finsuppScalarRight ℤ ℂ ℂ Nat.Primes
    ((1 : ℂ) ⊗ₜ[ℤ] deningerDivisor g.val) p = _
  rw [TensorProduct.finsuppScalarRight_apply_tmul_apply]
  simp only [deningerDivisor_apply, zsmul_eq_mul, mul_one]

/-- All prime-valuation moments, with finite support. -/
def deningerPrimeMoment : RouteRMultiplierKOne.KummerGroupRing →ₗ[ℂ] (Nat.Primes →₀ ℂ) :=
  deningerPrimeMomentEquiv.toLinearMap.comp
    ((TrivSqZeroExt.sndHom ℂ DeningerMomentSpace).comp deningerFirstJet.toLinearMap)

/-- Prime-valuation moments weighted by rational sign. -/
def deningerSignedPrimeMoment : RouteRMultiplierKOne.KummerGroupRing →ₗ[ℂ]
    (Nat.Primes →₀ ℂ) :=
  deningerPrimeMomentEquiv.toLinearMap.comp
    ((TrivSqZeroExt.sndHom ℂ DeningerMomentSpace).comp deningerSignedFirstJet.toLinearMap)

theorem deningerPrimeMoment_basis (g : CCMRationalAdelicScaling) (p : Nat.Primes) :
    deningerPrimeMoment (deningerSteinbergBasis g) p =
      (padicValRat (p : ℕ) (g.val : ℚ) : ℂ) := by
  change deningerPrimeMomentEquiv (jet ℂ CCMRationalAdelicScaling
    (MonoidAlgebra.of ℂ CCMRationalAdelicScaling g)).snd p = _
  rw [jet_of]
  exact deningerPrimeMomentEquiv_label g p

theorem deningerSignedPrimeMoment_basis (g : CCMRationalAdelicScaling) (p : Nat.Primes) :
    deningerSignedPrimeMoment (deningerSteinbergBasis g) p =
      deningerKummerSignAugmentation (deningerSteinbergBasis g) *
        (padicValRat (p : ℕ) (g.val : ℚ) : ℂ) := by
  change deningerPrimeMomentEquiv (jet ℂ CCMRationalAdelicScaling
    (twist deningerSignCharacter (MonoidAlgebra.of ℂ CCMRationalAdelicScaling g))).snd p = _
  rw [twist_of, map_smul, jet_of]
  change deningerPrimeMomentEquiv (deningerSignCharacter g •
    ((1 : ℂ) ⊗ₜ[ℤ] Additive.ofMul g)) p = _
  rw [map_smul, Finsupp.smul_apply, deningerPrimeMomentEquiv_label]
  rfl

private theorem jet_zero_iff_prime_coordinates (x : TrivSqZeroExt ℂ DeningerMomentSpace) :
    x = 0 ↔ x.fst = 0 ∧ ∀ p, deningerPrimeMomentEquiv x.snd p = 0 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨hf, hm⟩
    apply TrivSqZeroExt.ext
    · exact hf
    · apply deningerPrimeMomentEquiv.injective
      change deningerPrimeMomentEquiv x.snd = deningerPrimeMomentEquiv 0
      rw [map_zero]
      exact Finsupp.ext hm

/-- The positive Steinberg ideal is exactly the common kernel of both augmentations
and both families of prime-valuation moments. -/
theorem deningerSteinberg_mem_iff_prime_moments (v : RouteRMultiplierKOne.KummerGroupRing) :
    v ∈ deningerKummerSteinbergIdeal ↔
      deningerKummerAugmentation v = 0 ∧ (∀ p, deningerPrimeMoment v p = 0) ∧
      deningerKummerSignAugmentation v = 0 ∧ (∀ p, deningerSignedPrimeMoment v p = 0) := by
  rw [deningerSteinberg_mem_iff_first_jets, jet_zero_iff_prime_coordinates,
    jet_zero_iff_prime_coordinates, deningerFirstJet_fst, deningerSignedFirstJet_fst]
  exact and_assoc

/-- A first-order rational-scaling sector in prime coordinates. -/
def deningerPrimeJetEquiv : TrivSqZeroExt ℂ DeningerMomentSpace ≃ₐ[ℂ]
    TrivSqZeroExt ℂ (Nat.Primes →₀ ℂ) :=
  { TrivSqZeroExt.map deningerPrimeMomentEquiv.toLinearMap with
    invFun := TrivSqZeroExt.map deningerPrimeMomentEquiv.symm.toLinearMap
    left_inv := by
      intro x
      change TrivSqZeroExt.map deningerPrimeMomentEquiv.symm.toLinearMap
        (TrivSqZeroExt.map deningerPrimeMomentEquiv.toLinearMap x) = x
      apply TrivSqZeroExt.ext <;> simp
    right_inv := by
      intro x
      change TrivSqZeroExt.map deningerPrimeMomentEquiv.toLinearMap
        (TrivSqZeroExt.map deningerPrimeMomentEquiv.symm.toLinearMap x) = x
      apply TrivSqZeroExt.ext <;> simp }

/-- The source Steinberg quotient has two independent square-zero prime-moment sectors. -/
def deningerSteinbergPrimeEquiv :
    (RouteRMultiplierKOne.KummerGroupRing ⧸ deningerKummerSteinbergIdeal) ≃ₐ[ℂ]
      (TrivSqZeroExt ℂ (Nat.Primes →₀ ℂ) × TrivSqZeroExt ℂ (Nat.Primes →₀ ℂ)) :=
  deningerSteinbergFirstJetEquiv.trans (deningerPrimeJetEquiv.prodCongr deningerPrimeJetEquiv)

#print axioms deningerSteinberg_mem_iff_prime_moments
#print axioms deningerSignedPrimeMoment_basis
#print axioms deningerSteinbergPrimeEquiv
end RHTower
