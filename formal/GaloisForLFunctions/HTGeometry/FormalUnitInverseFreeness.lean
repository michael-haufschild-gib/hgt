import GaloisForLFunctions.HTGeometry.AlgebraicallyIndependentCoefficientFormalGerm
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Algebraic independence under multiplicative inversion of formal units

For the universal formal unit

`1 + X₀ T + X₁ T² + ⋯`,

take the nonconstant coefficients of its multiplicative inverse.  Substitution by those
coefficients defines an involution of the universal coefficient algebra: applying the operation
twice recovers the original unit.  The involution is injective, so the entire inverse-coefficient
family is algebraically independent.  Specializing the universal variables proves the same result
for every algebraically independent coefficient family in a commutative `ℂ`-algebra.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions

noncomputable section

abbrev UniversalUnitCoefficientRing := MvPolynomial ℕ ℂ

/-- The universal formal unit with one variable in each positive coefficient. -/
def universalUnitPowerSeries : UniversalUnitCoefficientRing⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 1 else MvPolynomial.X (n - 1)

@[simp] theorem universalUnitPowerSeries_constantCoeff :
    universalUnitPowerSeries.constantCoeff = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [universalUnitPowerSeries]

@[simp] theorem universalUnitPowerSeries_coeff_add_one (n : ℕ) :
    PowerSeries.coeff (n + 1) universalUnitPowerSeries = MvPolynomial.X n := by
  simp [universalUnitPowerSeries]

/-- The multiplicative inverse of the universal unit. -/
def universalUnitInversePowerSeries : UniversalUnitCoefficientRing⟦X⟧ :=
  PowerSeries.invOfUnit universalUnitPowerSeries 1

@[simp] theorem universalUnitInversePowerSeries_constantCoeff :
    universalUnitInversePowerSeries.constantCoeff = 1 := by
  simp [universalUnitInversePowerSeries]

theorem universalUnit_mul_inverse :
    universalUnitPowerSeries * universalUnitInversePowerSeries = 1 := by
  exact PowerSeries.mul_invOfUnit universalUnitPowerSeries 1
    universalUnitPowerSeries_constantCoeff

theorem universalUnit_inverse_mul :
    universalUnitInversePowerSeries * universalUnitPowerSeries = 1 := by
  exact PowerSeries.invOfUnit_mul universalUnitPowerSeries 1
    universalUnitPowerSeries_constantCoeff

/-- Positive-degree coefficient `n + 1` of the inverse universal unit. -/
def universalUnitInverseCoefficient (n : ℕ) : UniversalUnitCoefficientRing :=
  PowerSeries.coeff (n + 1) universalUnitInversePowerSeries

/-- Unit inversion as an endomorphism of the universal coefficient algebra. -/
def universalUnitInverseCoefficientMap :
    UniversalUnitCoefficientRing →ₐ[ℂ] UniversalUnitCoefficientRing :=
  MvPolynomial.aeval universalUnitInverseCoefficient

theorem map_universalUnitPowerSeries_inverse :
    PowerSeries.map universalUnitInverseCoefficientMap.toRingHom
      universalUnitPowerSeries = universalUnitInversePowerSeries := by
  apply PowerSeries.ext
  intro n
  obtain (_ | n) := n
  · simp
  · rw [PowerSeries.coeff_map, universalUnitPowerSeries_coeff_add_one]
    change universalUnitInverseCoefficientMap (MvPolynomial.X n) =
      universalUnitInverseCoefficient n
    rw [show universalUnitInverseCoefficientMap (MvPolynomial.X n) =
      universalUnitInverseCoefficient n by
      simp [universalUnitInverseCoefficientMap]]

theorem map_universalUnitInversePowerSeries :
    PowerSeries.map universalUnitInverseCoefficientMap.toRingHom
      universalUnitInversePowerSeries = universalUnitPowerSeries := by
  let R : UniversalUnitCoefficientRing⟦X⟧ :=
    PowerSeries.map universalUnitInverseCoefficientMap.toRingHom
      universalUnitInversePowerSeries
  have hVR : universalUnitInversePowerSeries * R = 1 := by
    have hmap := congrArg
      (PowerSeries.map universalUnitInverseCoefficientMap.toRingHom)
      universalUnit_mul_inverse
    simp only [map_mul, map_one] at hmap
    rw [map_universalUnitPowerSeries_inverse] at hmap
    exact hmap
  calc
    R = 1 * R := by rw [one_mul]
    _ = (universalUnitPowerSeries * universalUnitInversePowerSeries) * R := by
      rw [universalUnit_mul_inverse]
    _ = universalUnitPowerSeries * (universalUnitInversePowerSeries * R) := by
      rw [mul_assoc]
    _ = universalUnitPowerSeries := by rw [hVR, mul_one]

theorem universalUnitInverseCoefficientMap_involutive :
    universalUnitInverseCoefficientMap.comp
      universalUnitInverseCoefficientMap = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro n
  change universalUnitInverseCoefficientMap
      (universalUnitInverseCoefficientMap (MvPolynomial.X n)) =
    MvPolynomial.X n
  rw [show universalUnitInverseCoefficientMap (MvPolynomial.X n) =
      universalUnitInverseCoefficient n by
    simp [universalUnitInverseCoefficientMap]]
  change universalUnitInverseCoefficientMap
      (PowerSeries.coeff (n + 1) universalUnitInversePowerSeries) =
    MvPolynomial.X n
  have hc := congrArg (PowerSeries.coeff (n + 1))
    map_universalUnitInversePowerSeries
  change universalUnitInverseCoefficientMap.toRingHom
      (PowerSeries.coeff (n + 1) universalUnitInversePowerSeries) =
    MvPolynomial.X n
  simpa only [PowerSeries.coeff_map,
    universalUnitPowerSeries_coeff_add_one] using hc

theorem universalUnitInverseCoefficientMap_injective :
    Function.Injective universalUnitInverseCoefficientMap := by
  apply Function.LeftInverse.injective
  intro P
  change universalUnitInverseCoefficientMap
      (universalUnitInverseCoefficientMap P) = P
  exact AlgHom.congr_fun universalUnitInverseCoefficientMap_involutive P

/-- Multiplicative inversion preserves the free universal coefficient family. -/
theorem algebraicIndependent_universalUnitInverseCoefficient :
    AlgebraicIndependent ℂ universalUnitInverseCoefficient := by
  rw [algebraicIndependent_iff_injective_aeval]
  exact universalUnitInverseCoefficientMap_injective

/-- A formal unit with prescribed positive-degree coefficients. -/
def unitPowerSeriesOfCoefficients
    {A : Type*} [CommRing A] (a : ℕ → A) : A⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 1 else a (n - 1)

@[simp] theorem unitPowerSeriesOfCoefficients_constantCoeff
    {A : Type*} [CommRing A] (a : ℕ → A) :
    (unitPowerSeriesOfCoefficients a).constantCoeff = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [unitPowerSeriesOfCoefficients]

@[simp] theorem unitPowerSeriesOfCoefficients_coeff_add_one
    {A : Type*} [CommRing A] (a : ℕ → A) (n : ℕ) :
    PowerSeries.coeff (n + 1) (unitPowerSeriesOfCoefficients a) = a n := by
  simp [unitPowerSeriesOfCoefficients]

theorem map_universalUnitPowerSeries
    {A : Type*} [CommRing A] [Algebra ℂ A] (a : ℕ → A) :
    PowerSeries.map (MvPolynomial.aeval a).toRingHom universalUnitPowerSeries =
      unitPowerSeriesOfCoefficients a := by
  apply PowerSeries.ext
  intro n
  obtain (_ | n) := n
  · simp
  · rw [PowerSeries.coeff_map, universalUnitPowerSeries_coeff_add_one,
      unitPowerSeriesOfCoefficients_coeff_add_one]
    simp

/-- Specialize the inverse universal unit along a coefficient family. -/
def unitInversePowerSeriesOfCoefficients
    {A : Type*} [CommRing A] [Algebra ℂ A] (a : ℕ → A) : A⟦X⟧ :=
  PowerSeries.map (MvPolynomial.aeval a).toRingHom universalUnitInversePowerSeries

@[simp] theorem unitInversePowerSeriesOfCoefficients_constantCoeff
    {A : Type*} [CommRing A] [Algebra ℂ A] (a : ℕ → A) :
    (unitInversePowerSeriesOfCoefficients a).constantCoeff = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [unitInversePowerSeriesOfCoefficients]

theorem unitPowerSeries_mul_unitInverse
    {A : Type*} [CommRing A] [Algebra ℂ A] (a : ℕ → A) :
    unitPowerSeriesOfCoefficients a * unitInversePowerSeriesOfCoefficients a = 1 := by
  have hmap := congrArg (PowerSeries.map (MvPolynomial.aeval a).toRingHom)
    universalUnit_mul_inverse
  have hmap' :
      PowerSeries.map (MvPolynomial.aeval a).toRingHom universalUnitPowerSeries *
        PowerSeries.map (MvPolynomial.aeval a).toRingHom
          universalUnitInversePowerSeries = 1 := by
    simpa only [map_mul, map_one] using hmap
  calc
    unitPowerSeriesOfCoefficients a * unitInversePowerSeriesOfCoefficients a =
        PowerSeries.map (MvPolynomial.aeval a).toRingHom universalUnitPowerSeries *
          PowerSeries.map (MvPolynomial.aeval a).toRingHom
            universalUnitInversePowerSeries := by
      rw [map_universalUnitPowerSeries]
      rfl
    _ = 1 := hmap'

theorem unitInverse_mul_unitPowerSeries
    {A : Type*} [CommRing A] [Algebra ℂ A] (a : ℕ → A) :
    unitInversePowerSeriesOfCoefficients a * unitPowerSeriesOfCoefficients a = 1 := by
  have hmap := congrArg (PowerSeries.map (MvPolynomial.aeval a).toRingHom)
    universalUnit_inverse_mul
  have hmap' :
      PowerSeries.map (MvPolynomial.aeval a).toRingHom
          universalUnitInversePowerSeries *
        PowerSeries.map (MvPolynomial.aeval a).toRingHom universalUnitPowerSeries = 1 := by
    simpa only [map_mul, map_one] using hmap
  calc
    unitInversePowerSeriesOfCoefficients a * unitPowerSeriesOfCoefficients a =
        PowerSeries.map (MvPolynomial.aeval a).toRingHom
            universalUnitInversePowerSeries *
          PowerSeries.map (MvPolynomial.aeval a).toRingHom universalUnitPowerSeries := by
      rw [map_universalUnitPowerSeries]
      rfl
    _ = 1 := hmap'

/-- Positive-degree coefficients of the inverse specialized unit. -/
def unitInverseCoefficientOfCoefficients
    {A : Type*} [CommRing A] [Algebra ℂ A] (a : ℕ → A) (n : ℕ) : A :=
  PowerSeries.coeff (n + 1) (unitInversePowerSeriesOfCoefficients a)

theorem unitInverseCoefficientOfCoefficients_eq_aeval
    {A : Type*} [CommRing A] [Algebra ℂ A] (a : ℕ → A) (n : ℕ) :
    unitInverseCoefficientOfCoefficients a n =
      MvPolynomial.aeval a (universalUnitInverseCoefficient n) := by
  simp [unitInverseCoefficientOfCoefficients, unitInversePowerSeriesOfCoefficients,
    universalUnitInverseCoefficient]

/-- Multiplicative unit inversion preserves algebraic independence after specialization. -/
theorem AlgebraicIndependent.unitInverseCoefficientOfCoefficients
    {A : Type*} [CommRing A] [Algebra ℂ A]
    {a : ℕ → A} (ha : AlgebraicIndependent ℂ a) :
    AlgebraicIndependent ℂ
      (GaloisForLFunctions.unitInverseCoefficientOfCoefficients a) := by
  have h := ha.aeval_of_algebraicIndependent
    algebraicIndependent_universalUnitInverseCoefficient
  have heq : GaloisForLFunctions.unitInverseCoefficientOfCoefficients a =
      fun n => MvPolynomial.aeval a (universalUnitInverseCoefficient n) := by
    funext n
    exact unitInverseCoefficientOfCoefficients_eq_aeval a n
  rw [heq]
  exact h

/-- Negating every member of a family preserves algebraic independence. -/
def negCoordinateMap (ι R : Type*) [CommRing R] :
    MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
  MvPolynomial.aeval fun i => -MvPolynomial.X i

theorem negCoordinateMap_involutive (ι R : Type*) [CommRing R] :
    (negCoordinateMap ι R).comp (negCoordinateMap ι R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [negCoordinateMap]

theorem negCoordinateMap_injective (ι R : Type*) [CommRing R] :
    Function.Injective (negCoordinateMap ι R) := by
  apply Function.LeftInverse.injective
  intro P
  change negCoordinateMap ι R (negCoordinateMap ι R P) = P
  exact AlgHom.congr_fun (negCoordinateMap_involutive ι R) P

theorem algebraicIndependent_neg_X (ι R : Type*) [CommRing R] :
    AlgebraicIndependent R (fun i : ι => -(MvPolynomial.X i : MvPolynomial ι R)) := by
  rw [algebraicIndependent_iff_injective_aeval]
  exact negCoordinateMap_injective ι R

theorem AlgebraicIndependent.neg
    {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {a : ι → A} (ha : AlgebraicIndependent R a) :
    AlgebraicIndependent R (fun i => -a i) := by
  have h := ha.aeval_of_algebraicIndependent (algebraicIndependent_neg_X ι R)
  simpa using h

end

end GaloisForLFunctions
