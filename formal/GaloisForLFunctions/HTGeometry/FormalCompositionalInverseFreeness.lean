import GaloisForLFunctions.HTGeometry.AlgebraicallyIndependentCoefficientFormalGerm
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Algebraic independence under formal compositional inversion

Compositional inversion is a nonlinear operation on the coefficients of a formal
diffeomorphism.  This module proves that it cannot create an algebraic relation among a
countably free coefficient family.

The proof uses the universal tangent-to-identity series

`T + X₀ T² + X₁ T³ + ⋯`.

Its compositional inverse defines an endomorphism of the universal coefficient algebra by
sending `Xⱼ` to the coefficient of `Tⁿ⁺²` in the inverse.  Naturality and uniqueness of
compositional inverses show that this endomorphism is involutive.  It is therefore injective,
so the complete inverse-coefficient family is algebraically independent.  Specialization
along any algebraically independent coefficient family preserves the conclusion.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions

noncomputable section

theorem powerSeries_subst_rightInverse_unique
    {A : Type*} [CommRing A] {P Q R : A⟦X⟧}
    (hQ0 : Q.constantCoeff = 0) (hR0 : R.constantCoeff = 0)
    (hPQ : P.subst Q = (PowerSeries.X : A⟦X⟧))
    (hQR : Q.subst R = (PowerSeries.X : A⟦X⟧)) :
    R = P := by
  let hQ : PowerSeries.HasSubst Q :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hQ0
  let hR : PowerSeries.HasSubst R :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hR0
  calc
    R = PowerSeries.subst R (PowerSeries.X : A⟦X⟧) := by
      exact (PowerSeries.subst_X hR).symm
    _ = PowerSeries.subst R (PowerSeries.subst Q P) := by rw [hPQ]
    _ = PowerSeries.subst (PowerSeries.subst R Q) P := by
      exact PowerSeries.subst_comp_subst_apply hQ hR P
    _ = PowerSeries.subst (PowerSeries.X : A⟦X⟧) P := by rw [hQR]
    _ = P := PowerSeries.X_subst P

abbrev UniversalTangentCoefficientRing := MvPolynomial ℕ ℂ

/-- The universal formal diffeomorphism tangent to the identity. -/
def universalTangentPowerSeries : UniversalTangentCoefficientRing⟦X⟧ :=
  PowerSeries.mk fun n =>
    if n = 0 then 0 else if n = 1 then 1 else MvPolynomial.X (n - 2)

@[simp] theorem universalTangentPowerSeries_coeff_zero :
    PowerSeries.coeff 0 universalTangentPowerSeries = 0 := by
  simp [universalTangentPowerSeries]

@[simp] theorem universalTangentPowerSeries_constantCoeff :
    universalTangentPowerSeries.constantCoeff = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  exact universalTangentPowerSeries_coeff_zero

@[simp] theorem universalTangentPowerSeries_coeff_one :
    PowerSeries.coeff 1 universalTangentPowerSeries = 1 := by
  simp [universalTangentPowerSeries]

@[simp] theorem universalTangentPowerSeries_coeff_add_two (n : ℕ) :
    PowerSeries.coeff (n + 2) universalTangentPowerSeries = MvPolynomial.X n := by
  simp [universalTangentPowerSeries]

local instance universalTangentCoeffOneInvertible :
    Invertible (PowerSeries.coeff 1 universalTangentPowerSeries) where
  invOf := 1
  invOf_mul_self := by rw [universalTangentPowerSeries_coeff_one]; simp
  mul_invOf_self := by rw [universalTangentPowerSeries_coeff_one]; simp

def universalTangentInversePowerSeries : UniversalTangentCoefficientRing⟦X⟧ :=
  universalTangentPowerSeries.substInv

@[simp] theorem universalTangentInversePowerSeries_constantCoeff :
    universalTangentInversePowerSeries.constantCoeff = 0 := by
  simp [universalTangentInversePowerSeries]

@[simp] theorem universalTangentInversePowerSeries_coeff_one :
    PowerSeries.coeff 1 universalTangentInversePowerSeries = 1 := by
  rw [universalTangentInversePowerSeries,
    PowerSeries.coeff_one_substInv]
  rfl

theorem universalTangent_subst_inverse :
    universalTangentPowerSeries.subst universalTangentInversePowerSeries =
      PowerSeries.X := by
  simpa only [universalTangentInversePowerSeries] using
    PowerSeries.subst_substInv_right universalTangentPowerSeries
      universalTangentPowerSeries_constantCoeff

theorem universalTangent_inverse_subst :
    universalTangentInversePowerSeries.subst universalTangentPowerSeries =
      PowerSeries.X := by
  simpa only [universalTangentInversePowerSeries] using
    PowerSeries.subst_substInv_left universalTangentPowerSeries
      universalTangentPowerSeries_constantCoeff

/-- The nontrivial coefficients of the inverse universal diffeomorphism. -/
def universalTangentInverseCoefficient (n : ℕ) : UniversalTangentCoefficientRing :=
  PowerSeries.coeff (n + 2) universalTangentInversePowerSeries

/-- Compositional inversion as an endomorphism of the universal coefficient ring. -/
def universalTangentInverseCoefficientMap :
    UniversalTangentCoefficientRing →ₐ[ℂ] UniversalTangentCoefficientRing :=
  MvPolynomial.aeval universalTangentInverseCoefficient

theorem map_universalTangentPowerSeries_inverse :
    PowerSeries.map universalTangentInverseCoefficientMap.toRingHom
      universalTangentPowerSeries = universalTangentInversePowerSeries := by
  apply PowerSeries.ext
  intro n
  obtain (_ | _ | n) := n
  · rw [PowerSeries.coeff_map, universalTangentPowerSeries_coeff_zero]
    simp
  · rw [PowerSeries.coeff_map, universalTangentPowerSeries_coeff_one,
      universalTangentInversePowerSeries_coeff_one]
    exact map_one _
  · rw [PowerSeries.coeff_map,
      universalTangentPowerSeries_coeff_add_two]
    change universalTangentInverseCoefficientMap (MvPolynomial.X n) =
      universalTangentInverseCoefficient n
    rw [show universalTangentInverseCoefficientMap (MvPolynomial.X n) =
      universalTangentInverseCoefficient n by
      simp [universalTangentInverseCoefficientMap]]

theorem map_universalTangentInversePowerSeries :
    PowerSeries.map universalTangentInverseCoefficientMap.toRingHom
      universalTangentInversePowerSeries = universalTangentPowerSeries := by
  let R : UniversalTangentCoefficientRing⟦X⟧ :=
    PowerSeries.map universalTangentInverseCoefficientMap.toRingHom
      universalTangentInversePowerSeries
  have hR0 : R.constantCoeff = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    simp [R]
  have hright : universalTangentInversePowerSeries.subst R = PowerSeries.X := by
    have hnat := PowerSeries.map_subst
      (h := universalTangentInverseCoefficientMap.toRingHom)
      (PowerSeries.HasSubst.of_constantCoeff_zero'
        universalTangentInversePowerSeries_constantCoeff)
      universalTangentPowerSeries
    calc
      universalTangentInversePowerSeries.subst R =
          (PowerSeries.map universalTangentInverseCoefficientMap.toRingHom
            universalTangentPowerSeries).subst R := by
        rw [map_universalTangentPowerSeries_inverse]
      _ = PowerSeries.map universalTangentInverseCoefficientMap.toRingHom
          (universalTangentPowerSeries.subst
            universalTangentInversePowerSeries) := by
        symm
        simpa only [R] using! hnat
      _ = PowerSeries.X := by
        rw [universalTangent_subst_inverse, PowerSeries.map_X]
  exact powerSeries_subst_rightInverse_unique
    universalTangentInversePowerSeries_constantCoeff hR0
    universalTangent_subst_inverse hright

theorem universalTangentInverseCoefficientMap_involutive :
    universalTangentInverseCoefficientMap.comp
      universalTangentInverseCoefficientMap = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro n
  change universalTangentInverseCoefficientMap
      (universalTangentInverseCoefficientMap (MvPolynomial.X n)) =
    MvPolynomial.X n
  rw [show universalTangentInverseCoefficientMap (MvPolynomial.X n) =
      universalTangentInverseCoefficient n by
    simp [universalTangentInverseCoefficientMap]]
  change universalTangentInverseCoefficientMap
      (PowerSeries.coeff (n + 2) universalTangentInversePowerSeries) =
    MvPolynomial.X n
  have hc := congrArg (PowerSeries.coeff (n + 2))
    map_universalTangentInversePowerSeries
  simpa only [PowerSeries.coeff_map,
    universalTangentPowerSeries_coeff_add_two] using! hc

theorem universalTangentInverseCoefficientMap_injective :
    Function.Injective universalTangentInverseCoefficientMap := by
  apply Function.LeftInverse.injective
  intro P
  change universalTangentInverseCoefficientMap
      (universalTangentInverseCoefficientMap P) = P
  exact AlgHom.congr_fun universalTangentInverseCoefficientMap_involutive P

/-- Compositional inversion preserves the free countable coefficient family. -/
theorem algebraicIndependent_universalTangentInverseCoefficient :
    AlgebraicIndependent ℂ universalTangentInverseCoefficient := by
  rw [algebraicIndependent_iff_injective_aeval]
  exact universalTangentInverseCoefficientMap_injective

/-- A tangent-to-identity series with prescribed nonlinear coefficients. -/
def tangentPowerSeriesOfCoefficients
    {A : Type*} [CommRing A] (a : ℕ → A) : A⟦X⟧ :=
  PowerSeries.mk fun n =>
    if n = 0 then 0 else if n = 1 then 1 else a (n - 2)

@[simp] theorem tangentPowerSeriesOfCoefficients_coeff_zero
    {A : Type*} [CommRing A] (a : ℕ → A) :
    PowerSeries.coeff 0 (tangentPowerSeriesOfCoefficients a) = 0 := by
  simp [tangentPowerSeriesOfCoefficients]

@[simp] theorem tangentPowerSeriesOfCoefficients_constantCoeff
    {A : Type*} [CommRing A] (a : ℕ → A) :
    (tangentPowerSeriesOfCoefficients a).constantCoeff = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  exact tangentPowerSeriesOfCoefficients_coeff_zero a

@[simp] theorem tangentPowerSeriesOfCoefficients_coeff_one
    {A : Type*} [CommRing A] (a : ℕ → A) :
    PowerSeries.coeff 1 (tangentPowerSeriesOfCoefficients a) = 1 := by
  simp [tangentPowerSeriesOfCoefficients]

@[simp] theorem tangentPowerSeriesOfCoefficients_coeff_add_two
    {A : Type*} [CommRing A] (a : ℕ → A) (n : ℕ) :
    PowerSeries.coeff (n + 2) (tangentPowerSeriesOfCoefficients a) = a n := by
  simp [tangentPowerSeriesOfCoefficients]

theorem map_universalTangentPowerSeries
    {A : Type*} [CommRing A] [Algebra ℂ A] (a : ℕ → A) :
    PowerSeries.map (MvPolynomial.aeval a).toRingHom
      universalTangentPowerSeries = tangentPowerSeriesOfCoefficients a := by
  apply PowerSeries.ext
  intro n
  obtain (_ | _ | n) := n
  · simp
  · simp
  · rw [PowerSeries.coeff_map,
      universalTangentPowerSeries_coeff_add_two,
      tangentPowerSeriesOfCoefficients_coeff_add_two]
    simp

/-- Specialize the inverse universal diffeomorphism along a coefficient family. -/
def tangentInversePowerSeriesOfCoefficients
    {A : Type*} [CommRing A] [Algebra ℂ A] (a : ℕ → A) : A⟦X⟧ :=
  PowerSeries.map (MvPolynomial.aeval a).toRingHom
    universalTangentInversePowerSeries

@[simp] theorem tangentInversePowerSeriesOfCoefficients_constantCoeff
    {A : Type*} [CommRing A] [Algebra ℂ A] (a : ℕ → A) :
    (tangentInversePowerSeriesOfCoefficients a).constantCoeff = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [tangentInversePowerSeriesOfCoefficients]

theorem tangentPowerSeries_subst_tangentInverse
    {A : Type*} [CommRing A] [Algebra ℂ A] (a : ℕ → A) :
    (tangentPowerSeriesOfCoefficients a).subst
      (tangentInversePowerSeriesOfCoefficients a) = PowerSeries.X := by
  let f : UniversalTangentCoefficientRing →+* A :=
    (MvPolynomial.aeval a).toRingHom
  have hnat := PowerSeries.map_subst
    (h := f)
    (PowerSeries.HasSubst.of_constantCoeff_zero'
      universalTangentInversePowerSeries_constantCoeff)
    universalTangentPowerSeries
  calc
    (tangentPowerSeriesOfCoefficients a).subst
        (tangentInversePowerSeriesOfCoefficients a) =
      (PowerSeries.map f universalTangentPowerSeries).subst
        (PowerSeries.map f universalTangentInversePowerSeries) := by
          rw [map_universalTangentPowerSeries]
          rfl
    _ = PowerSeries.map f
        (universalTangentPowerSeries.subst
          universalTangentInversePowerSeries) := by
          exact hnat.symm
    _ = PowerSeries.X := by
      rw [universalTangent_subst_inverse, PowerSeries.map_X]

theorem tangentInverse_subst_tangentPowerSeries
    {A : Type*} [CommRing A] [Algebra ℂ A] (a : ℕ → A) :
    (tangentInversePowerSeriesOfCoefficients a).subst
      (tangentPowerSeriesOfCoefficients a) = PowerSeries.X := by
  let f : UniversalTangentCoefficientRing →+* A :=
    (MvPolynomial.aeval a).toRingHom
  have hnat := PowerSeries.map_subst
    (h := f)
    (PowerSeries.HasSubst.of_constantCoeff_zero'
      universalTangentPowerSeries_constantCoeff)
    universalTangentInversePowerSeries
  calc
    (tangentInversePowerSeriesOfCoefficients a).subst
        (tangentPowerSeriesOfCoefficients a) =
      (PowerSeries.map f universalTangentInversePowerSeries).subst
        (PowerSeries.map f universalTangentPowerSeries) := by
          rw [map_universalTangentPowerSeries]
          rfl
    _ = PowerSeries.map f
        (universalTangentInversePowerSeries.subst
          universalTangentPowerSeries) := by
          exact hnat.symm
    _ = PowerSeries.X := by
      rw [universalTangent_inverse_subst, PowerSeries.map_X]

/-- The nonlinear coefficients of the specialized inverse series. -/
def tangentInverseCoefficientOfCoefficients
    {A : Type*} [CommRing A] [Algebra ℂ A] (a : ℕ → A) (n : ℕ) : A :=
  PowerSeries.coeff (n + 2) (tangentInversePowerSeriesOfCoefficients a)

theorem tangentInverseCoefficientOfCoefficients_eq_aeval
    {A : Type*} [CommRing A] [Algebra ℂ A] (a : ℕ → A) (n : ℕ) :
    tangentInverseCoefficientOfCoefficients a n =
      MvPolynomial.aeval a (universalTangentInverseCoefficient n) := by
  simp [tangentInverseCoefficientOfCoefficients,
    tangentInversePowerSeriesOfCoefficients,
    universalTangentInverseCoefficient]

/-- Algebraic independence of nonlinear coefficients survives compositional inversion. -/
theorem AlgebraicIndependent.tangentInverseCoefficientOfCoefficients
    {A : Type*} [CommRing A] [Algebra ℂ A]
    {a : ℕ → A} (ha : AlgebraicIndependent ℂ a) :
    AlgebraicIndependent ℂ
      (GaloisForLFunctions.tangentInverseCoefficientOfCoefficients a) := by
  have h := ha.aeval_of_algebraicIndependent
    algebraicIndependent_universalTangentInverseCoefficient
  have heq : GaloisForLFunctions.tangentInverseCoefficientOfCoefficients a =
      fun n => MvPolynomial.aeval a (universalTangentInverseCoefficient n) := by
    funext n
    exact tangentInverseCoefficientOfCoefficients_eq_aeval a n
  rw [heq]
  exact h

end

end GaloisForLFunctions
