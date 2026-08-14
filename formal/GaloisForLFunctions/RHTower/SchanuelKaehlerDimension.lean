import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import GaloisForLFunctions.HTGeometry.AlgebraAdjoinAlgebraic

namespace GaloisForLFunctions.RHTower

universe u v

open Polynomial
open scoped IntermediateField TensorProduct

noncomputable section

/-- A separable algebraic extension does not change the dimension of absolute Kähler
differentials. -/
theorem finrank_kaehlerDifferential_eq_of_isSeparable
    {A E K : Type*} [Field A] [Field E] [Field K]
    [Algebra A E] [Algebra E K] [Algebra A K] [IsScalarTower A E K]
    [Algebra.IsSeparable E K] :
    Module.finrank K (KaehlerDifferential A K) =
      Module.finrank E (KaehlerDifferential A E) := by
  letI : Algebra.FormallyEtale E K := Algebra.FormallyEtale.of_isSeparable E K
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A E K
  rw [← e.finrank_eq, Module.finrank_baseChange]

/-- The rational function field in one variable has one-dimensional absolute differentials. -/
theorem finrank_kaehlerDifferential_ratFunc (A : Type*) [Field A] :
    Module.finrank (RatFunc A) (KaehlerDifferential A (RatFunc A)) = 1 := by
  letI : Algebra.FormallyEtale A[X] (RatFunc A) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := RatFunc A) (nonZeroDivisors A[X])
  let e₀ := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
    A A[X] (RatFunc A)
  let e₁ := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl (RatFunc A) (RatFunc A))
    (KaehlerDifferential.polynomialEquiv A)
  let e₂ := TensorProduct.AlgebraTensorModule.rid A[X] (RatFunc A) (RatFunc A)
  let e : KaehlerDifferential A (RatFunc A) ≃ₗ[RatFunc A] RatFunc A :=
    e₀.symm.trans (e₁.trans e₂)
  rw [e.finrank_eq, Module.finrank_self]

/-- A simple transcendental field has one-dimensional absolute differentials. -/
theorem finrank_kaehlerDifferential_adjoin_transcendental
    {A K : Type*} [Field A] [Field K] [Algebra A K]
    (u : K) (hu : Transcendental A u) :
    Module.finrank A⟮u⟯ (KaehlerDifferential A A⟮u⟯) = 1 := by
  let e : RatFunc A ≃ₐ[A] A⟮u⟯ := RatFunc.algEquivOfTranscendental u hu
  letI algRU : Algebra (RatFunc A) A⟮u⟯ := e.toAlgHom.toAlgebra
  haveI towerRU : IsScalarTower A (RatFunc A) A⟮u⟯ := IsScalarTower.of_algHom e.toAlgHom
  haveI algebraicRU : Algebra.IsAlgebraic (RatFunc A) A⟮u⟯ := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨r, hr⟩ := e.surjective x
    rw [← hr]
    change IsAlgebraic (RatFunc A) (algebraMap (RatFunc A) A⟮u⟯ r)
    exact isAlgebraic_algebraMap r
  letI separableRU : Algebra.IsSeparable (RatFunc A) A⟮u⟯ := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (RingEquiv.refl (RatFunc A)) e.toRingEquiv ?_
    ext r
    simp [RingHom.algebraMap_toAlgebra]
  calc
    Module.finrank A⟮u⟯ (KaehlerDifferential A A⟮u⟯) =
        Module.finrank (RatFunc A) (KaehlerDifferential A (RatFunc A)) :=
      finrank_kaehlerDifferential_eq_of_isSeparable
        (A := A) (E := RatFunc A) (K := A⟮u⟯)
    _ = 1 := finrank_kaehlerDifferential_ratFunc A

/-- Over a characteristic-zero field, transcendence degree one is equivalent to having a
one-dimensional module of absolute Kähler differentials in the direction needed by the Schanuel
defect argument. -/
theorem finrank_kaehlerDifferential_eq_one_of_trdeg_eq_one
    {A : Type u} {K : Type v} [Field A] [Field K] [Algebra A K] [CharZero A]
    (htrdeg : Algebra.trdeg A K = 1) :
    Module.finrank K (KaehlerDifferential A K) = 1 := by
  have hne : Algebra.trdeg A K ≠ 0 := by simp [htrdeg]
  haveI : Algebra.Transcendental A K := trdeg_ne_zero_iff.mp hne
  obtain ⟨u, hu⟩ := Algebra.Transcendental.transcendental (R := A) (A := K)
  let basisVec : PUnit.{v + 1} → K := fun _ ↦ u
  have hvAI : AlgebraicIndependent A basisVec := by
    rw [algebraicIndependent_unique_type_iff]
    exact hu
  have hvTB : IsTranscendenceBasis A basisVec :=
    AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite
      (R := A) (A := K) (ι := PUnit.{v + 1}) hvAI (by rw [htrdeg, Cardinal.mk_punit])
  have hrange : Set.range basisVec = {u} := by
    ext x
    simp [basisVec]
  have hAlgRing : Algebra.IsAlgebraic (Algebra.adjoin A ({u} : Set K)) K := by
    have h := hvTB.isAlgebraic
    rw [hrange] at h
    exact h
  let E : IntermediateField A K := A⟮u⟯
  letI : Algebra E K := E.val.toAlgebra
  haveI : IsScalarTower A E K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : Algebra.IsAlgebraic E K := by
    refine ⟨fun x ↦ ?_⟩
    exact GaloisForLFunctions.isAlgebraic_intermediateField_of_isAlgebraic_algebraAdjoin
      ({u} : Set K) (hAlgRing.isAlgebraic x)
  letI : Algebra.IsSeparable E K := inferInstance
  calc
    Module.finrank K (KaehlerDifferential A K) =
        Module.finrank E (KaehlerDifferential A E) :=
      finrank_kaehlerDifferential_eq_of_isSeparable
    _ = 1 := finrank_kaehlerDifferential_adjoin_transcendental u hu

end

end GaloisForLFunctions.RHTower
