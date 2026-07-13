import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Extending derivations to fraction fields

A derivation `D : A → F` determines the graph homomorphism

`a ↦ (a, D a) : A → F ⊕ εF`.

Every non-zero-divisor of `A` maps to a unit because the first coordinate is
nonzero in the fraction field.  The localization universal property therefore
extends the graph homomorphism to the fraction field.  Its second coordinate
is the quotient-rule extension of `D`.

This construction is used to prove that a transcendental element has a
nonzero universal differential.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The square-zero graph algebra homomorphism attached to a derivation. -/
def derivationGraphAlgHom
    {K A F : Type*} [CommRing K] [CommRing A] [Field F]
    [Algebra K A] [Algebra A F] [Algebra K F] [IsScalarTower K A F]
    (D : Derivation K A F) : A →ₐ[K] TrivSqZeroExt F F where
  toFun a := (algebraMap A F a, D a)
  map_one' := by
    apply TrivSqZeroExt.ext <;> simp
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · simp
    · simp [Derivation.leibniz, Algebra.smul_def, mul_comm]
  map_zero' := by
    apply TrivSqZeroExt.ext <;> simp
  map_add' a b := by
    apply TrivSqZeroExt.ext <;> simp
  commutes' k := by
    rw [TrivSqZeroExt.algebraMap_eq_inl']
    apply TrivSqZeroExt.ext
    · simp [IsScalarTower.algebraMap_apply K A F]
    · simp

@[simp] theorem derivationGraphAlgHom_fst
    {K A F : Type*} [CommRing K] [CommRing A] [Field F]
    [Algebra K A] [Algebra A F] [Algebra K F] [IsScalarTower K A F]
    (D : Derivation K A F) (a : A) :
    (derivationGraphAlgHom D a).fst = algebraMap A F a := rfl

@[simp] theorem derivationGraphAlgHom_snd
    {K A F : Type*} [CommRing K] [CommRing A] [Field F]
    [Algebra K A] [Algebra A F] [Algebra K F] [IsScalarTower K A F]
    (D : Derivation K A F) (a : A) :
    (derivationGraphAlgHom D a).snd = D a := rfl

/-- Non-zero-divisors map to units under the derivation graph. -/
theorem derivationGraphAlgHom_isUnit_nonZeroDivisor
    {K A F : Type*} [CommRing K] [CommRing A] [IsDomain A] [Field F]
    [Algebra K A] [Algebra A F] [Algebra K F] [IsScalarTower K A F]
    [IsFractionRing A F]
    (D : Derivation K A F) (s : nonZeroDivisors A) :
    IsUnit (derivationGraphAlgHom D s.1) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  rw [derivationGraphAlgHom_fst, isUnit_iff_ne_zero]
  exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2

/-- The graph homomorphism extended through the fraction-field
localization. -/
def fractionRingDerivationGraphLift
    {K A F : Type*} [CommRing K] [CommRing A] [IsDomain A] [Field F]
    [Algebra K A] [Algebra A F] [Algebra K F] [IsScalarTower K A F]
    [IsFractionRing A F]
    (D : Derivation K A F) : F →+* TrivSqZeroExt F F :=
  IsLocalization.lift (derivationGraphAlgHom_isUnit_nonZeroDivisor D)

/-- The graph lift agrees with the original derivation graph on `A`. -/
theorem fractionRingDerivationGraphLift_algebraMap
    {K A F : Type*} [CommRing K] [CommRing A] [IsDomain A] [Field F]
    [Algebra K A] [Algebra A F] [Algebra K F] [IsScalarTower K A F]
    [IsFractionRing A F]
    (D : Derivation K A F) (a : A) :
    fractionRingDerivationGraphLift D (algebraMap A F a) =
      derivationGraphAlgHom D a := by
  exact RingHom.congr_fun
    (IsLocalization.lift_comp
      (derivationGraphAlgHom_isUnit_nonZeroDivisor D)) a

/-- The first coordinate of the graph lift is the identity of the fraction
field. -/
theorem fractionRingDerivationGraphLift_fst
    {K A F : Type*} [CommRing K] [CommRing A] [IsDomain A] [Field F]
    [Algebra K A] [Algebra A F] [Algebra K F] [IsScalarTower K A F]
    [IsFractionRing A F]
    (D : Derivation K A F) (z : F) :
    (fractionRingDerivationGraphLift D z).fst = z := by
  let f : F →+* F :=
    (TrivSqZeroExt.fstHom K F F).toRingHom.comp
      (fractionRingDerivationGraphLift D)
  have hf : f.comp (algebraMap A F) =
      (RingHom.id F).comp (algebraMap A F) := by
    ext a
    simp [f, fractionRingDerivationGraphLift_algebraMap]
  have heq : f = RingHom.id F :=
    IsLocalization.ringHom_ext (nonZeroDivisors A) hf
  exact RingHom.congr_fun heq z

/-- The second coordinate of the graph lift is the extension of the
derivation to the fraction field. -/
def fractionRingDerivation
    {K A F : Type*} [CommRing K] [CommRing A] [IsDomain A] [Field F]
    [Algebra K A] [Algebra A F] [Algebra K F] [IsScalarTower K A F]
    [IsFractionRing A F]
    (D : Derivation K A F) : Derivation K F F :=
  Derivation.mk'
    { toFun := fun z ↦ (fractionRingDerivationGraphLift D z).snd
      map_add' := by
        intro x y
        exact congrArg TrivSqZeroExt.snd
          (map_add (fractionRingDerivationGraphLift D) x y)
      map_smul' := by
        intro k z
        simp only [Algebra.smul_def]
        rw [map_mul (fractionRingDerivationGraphLift D)]
        rw [TrivSqZeroExt.snd_mul,
          fractionRingDerivationGraphLift_fst]
        have hbase :
            fractionRingDerivationGraphLift D (algebraMap K F k) =
              derivationGraphAlgHom D (algebraMap K A k) := by
          rw [IsScalarTower.algebraMap_apply K A F]
          exact fractionRingDerivationGraphLift_algebraMap D _
        rw [hbase]
        simp only [derivationGraphAlgHom_snd, Derivation.map_algebraMap,
          smul_zero, add_zero, Algebra.smul_def]
        simp }
    (by
      intro x y
      change (fractionRingDerivationGraphLift D (x * y)).snd =
        x • (fractionRingDerivationGraphLift D y).snd +
          y • (fractionRingDerivationGraphLift D x).snd
      rw [map_mul (fractionRingDerivationGraphLift D)]
      rw [TrivSqZeroExt.snd_mul,
        fractionRingDerivationGraphLift_fst,
        fractionRingDerivationGraphLift_fst]
      simp [smul_eq_mul, mul_comm])

@[simp] theorem fractionRingDerivation_apply
    {K A F : Type*} [CommRing K] [CommRing A] [IsDomain A] [Field F]
    [Algebra K A] [Algebra A F] [Algebra K F] [IsScalarTower K A F]
    [IsFractionRing A F]
    (D : Derivation K A F) (z : F) :
    fractionRingDerivation D z =
      (fractionRingDerivationGraphLift D z).snd := rfl

/-- The fraction-field extension restricts to the original derivation. -/
theorem fractionRingDerivation_algebraMap
    {K A F : Type*} [CommRing K] [CommRing A] [IsDomain A] [Field F]
    [Algebra K A] [Algebra A F] [Algebra K F] [IsScalarTower K A F]
    [IsFractionRing A F]
    (D : Derivation K A F) (a : A) :
    fractionRingDerivation D (algebraMap A F a) = D a := by
  rw [fractionRingDerivation_apply,
    fractionRingDerivationGraphLift_algebraMap,
    derivationGraphAlgHom_snd]

end

end GaloisForLFunctions

namespace GaloisForLFunctions

/-- Two derivations on a fraction field are equal when they agree on the
source domain. -/
theorem fractionRing_derivation_ext
    {K A F : Type*} [CommRing K] [CommRing A] [IsDomain A] [Field F]
    [Algebra K A] [Algebra A F] [Algebra K F] [IsScalarTower K A F]
    [IsFractionRing A F]
    (D₁ D₂ : Derivation K F F)
    (h : ∀ a : A, D₁ (algebraMap A F a) = D₂ (algebraMap A F a)) :
    D₁ = D₂ := by
  ext z
  obtain ⟨⟨a, s⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors A) z
  have h₁ := congrArg D₁ hz
  have h₂ := congrArg D₂ hz
  simp only [Derivation.leibniz, smul_eq_mul] at h₁ h₂
  have hs : algebraMap A F s.1 ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hd : algebraMap A F s.1 * (D₁ z - D₂ z) = 0 := by
    rw [h a, h s.1] at h₁
    calc
      algebraMap A F s.1 * (D₁ z - D₂ z) =
          (z * D₂ (algebraMap A F s.1) + algebraMap A F s.1 * D₁ z) -
            (z * D₂ (algebraMap A F s.1) + algebraMap A F s.1 * D₂ z) := by ring
      _ = D₂ (algebraMap A F a) - D₂ (algebraMap A F a) := by rw [h₁, h₂]
      _ = 0 := sub_self _
  have hz' : D₁ z - D₂ z = 0 := (mul_eq_zero.mp hd).resolve_left hs
  exact sub_eq_zero.mp hz'

end GaloisForLFunctions
