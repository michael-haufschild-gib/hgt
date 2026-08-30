import GaloisForLFunctions.RHTower.DeningerQ8ActualMaximalAbelianField
import GaloisForLFunctions.HTGeometry.UnramifiedRadicalCriterion
import GaloisForLFunctions.HTGeometry.TameEisensteinDifferentExponent
import GaloisForLFunctions.HTGeometry.LocalRamificationOrderLaw
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Two-adic ramification of the literal SST quaternion field

For the explicit nested-radical field used by Shinoda--Suzuki--Takada, put
`u = (1 + sqrt 5) / 2`, `v = (1 + sqrt 41) / 2`, and let `z` be the top
radical.  The identities

* `u^2 = u + 1`,
* `v^2 = v + 10`,
* `z^2 = 2 (u + 2) (35 + 12 v)`, and
* `(u + 2)(35 + 12v)(3-u)(47-12v) = 1025`

show that the second factor in the radical is a two-adic unit.  If a prime
above two were unramified, two would have additive valuation one there; the
square relation would then force `2 | 1`.  Thus every prime above two is
ramified, rational two is not unramified in the field, and two divides its
absolute discriminant.

This closes a genuine hypothesis audit for the root-number route: a theorem
requiring the literal field to be tame cannot supply its global sign.  The
remaining root-number proof must calculate the local epsilon factor at two or
invoke a theorem that includes this ramified two-adic case.
-/

open IsDiscreteValuationRing

namespace RHTower

open scoped NumberField
open Polynomial

noncomputable section

local notation "K3" => deningerQ8RootNumberNegOneTopField

local instance q8LiteralTwoAdicCharZero : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective

def q8LiteralTwoAdicUField : K3 :=
  (1 + deningerQ8RootNumberNegOneTopX) / 2

def q8LiteralTwoAdicVField : K3 :=
  (1 + deningerQ8RootNumberNegOneTopY) / 2

theorem q8LiteralTwoAdicUField_sq :
    q8LiteralTwoAdicUField ^ 2 = q8LiteralTwoAdicUField + 1 := by
  have hx := deningerQ8RootNumberNegOne_topX_sq
  unfold q8LiteralTwoAdicUField
  field_simp
  linear_combination hx

theorem q8LiteralTwoAdicVField_sq :
    q8LiteralTwoAdicVField ^ 2 = q8LiteralTwoAdicVField + 10 := by
  have hy := deningerQ8RootNumberNegOne_topY_sq
  unfold q8LiteralTwoAdicVField
  field_simp
  linear_combination hy

theorem q8LiteralTopRoot_two_adic_relation :
    deningerQ8RootNumberNegOneTopRoot ^ 2 =
      2 * (q8LiteralTwoAdicUField + 2) * (35 + 12 * q8LiteralTwoAdicVField) := by
  rw [q8TopRoot_radical_relation]
  unfold deningerQ8RootNumberNegOneR deningerQ8RootNumberNegOneS
  unfold q8LiteralTwoAdicUField q8LiteralTwoAdicVField
  field_simp
  ring

theorem q8LiteralTwoAdicUField_isIntegral : IsIntegral ℤ q8LiteralTwoAdicUField := by
  let p : ℤ[X] := X ^ 2 - X - 1
  refine ⟨p, ?_, ?_⟩
  · dsimp [p]
    (monicity; norm_num)
  · have h : (q8LiteralTwoAdicUField ^ 2 - q8LiteralTwoAdicUField - 1 : K3) = 0 := by
      rw [q8LiteralTwoAdicUField_sq]
      ring
    simpa [p] using h

theorem q8LiteralTwoAdicVField_isIntegral : IsIntegral ℤ q8LiteralTwoAdicVField := by
  let p : ℤ[X] := X ^ 2 - X - 10
  refine ⟨p, ?_, ?_⟩
  · dsimp [p]
    (monicity; norm_num)
  · have h : (q8LiteralTwoAdicVField ^ 2 - q8LiteralTwoAdicVField - 10 : K3) = 0 := by
      rw [q8LiteralTwoAdicVField_sq]
      ring
    simpa [p] using h

theorem q8LiteralTopRoot_isIntegral :
    IsIntegral ℤ deningerQ8RootNumberNegOneTopRoot := by
  refine ⟨deningerQ8RootNumberNegOneRadicalPolynomial, ?_, ?_⟩
  · unfold deningerQ8RootNumberNegOneRadicalPolynomial
    monicity <;> norm_num
  · change deningerQ8RootNumberNegOneRadicalPolynomial.eval₂
      (Int.castRingHom K3) deningerQ8RootNumberNegOneTopRoot = 0
    exact deningerQ8RootNumberNegOneRadicalPolynomial_eval₂_eq_zero
      deningerQ8RootNumberNegOneTopX deningerQ8RootNumberNegOneTopY
      deningerQ8RootNumberNegOneTopRoot
      deningerQ8RootNumberNegOne_topX_sq deningerQ8RootNumberNegOne_topY_sq
      q8TopRoot_radical_relation

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField

noncomputable local instance q8LiteralTwoAdicFiniteDimensionalK1K2 :
    FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_secondQuadratic_irreducible.ne_zero).basis

noncomputable local instance q8LiteralTwoAdicFiniteDimensionalK2K3 :
    FiniteDimensional K2 K3 :=
  Module.Basis.finiteDimensional_of_finite
    (AdjoinRoot.powerBasis
      deningerQ8RootNumberNegOne_thirdQuadratic_irreducible.ne_zero).basis

noncomputable local instance q8LiteralTwoAdicFiniteDimensionalRatK2 :
    FiniteDimensional ℚ K2 := FiniteDimensional.trans ℚ K1 K2

noncomputable local instance q8LiteralTwoAdicFiniteDimensionalRatK3 :
    FiniteDimensional ℚ K3 := FiniteDimensional.trans ℚ K2 K3

noncomputable local instance q8LiteralTwoAdicNumberField : NumberField K3 := NumberField.mk

noncomputable def q8LiteralTwoAdicU : 𝓞 K3 :=
  ⟨q8LiteralTwoAdicUField, q8LiteralTwoAdicUField_isIntegral⟩

noncomputable def q8LiteralTwoAdicV : 𝓞 K3 :=
  ⟨q8LiteralTwoAdicVField, q8LiteralTwoAdicVField_isIntegral⟩

noncomputable def q8LiteralTwoAdicZ : 𝓞 K3 :=
  ⟨deningerQ8RootNumberNegOneTopRoot, q8LiteralTopRoot_isIntegral⟩

theorem q8LiteralTwoAdicU_sq :
    q8LiteralTwoAdicU ^ 2 = q8LiteralTwoAdicU + 1 := by
  apply Subtype.ext
  exact q8LiteralTwoAdicUField_sq

theorem q8LiteralTwoAdicV_sq :
    q8LiteralTwoAdicV ^ 2 = q8LiteralTwoAdicV + 10 := by
  apply Subtype.ext
  exact q8LiteralTwoAdicVField_sq

theorem q8LiteralTwoAdicZ_sq :
    q8LiteralTwoAdicZ ^ 2 =
      2 * (q8LiteralTwoAdicU + 2) * (35 + 12 * q8LiteralTwoAdicV) := by
  apply Subtype.ext
  exact q8LiteralTopRoot_two_adic_relation

theorem q8LiteralRadical_not_addVal_two_eq_one
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (u v z : B)
    (hu : u ^ 2 = u + 1)
    (hv : v ^ 2 = v + 10)
    (hz : z ^ 2 = 2 * (u + 2) * (35 + 12 * v)) :
    addVal B (2 : B) ≠ 1 := by
  intro htwo
  have htwoNonunit : ¬ IsUnit (2 : B) := by
    intro hunit
    have hval := GaloisForLFunctions.HTGeometry.addVal_of_isUnit_target hunit
    rw [htwo] at hval
    norm_num at hval
  have hotherNonunit : ¬ IsUnit ((-512 : B) * 2) := by
    intro hunit
    exact htwoNonunit (IsUnit.mul_iff.mp hunit).2
  have hoddUnit : IsUnit (1025 : B) := by
    have hsum : (1025 : B) + (-512 : B) * 2 = 1 := by norm_num
    exact (IsLocalRing.isUnit_or_isUnit_of_add_one hsum).resolve_right hotherNonunit
  let b : B := (u + 2) * (35 + 12 * v)
  let c : B := (3 - u) * (47 - 12 * v)
  have hbc : b * c = 1025 := by
    dsimp [b, c]
    calc
      (u + 2) * (35 + 12 * v) * ((3 - u) * (47 - 12 * v)) =
          ((u + 2) * (3 - u)) * ((35 + 12 * v) * (47 - 12 * v)) := by ring
      _ = 5 * 205 := by
        rw [show (u + 2) * (3 - u) = 5 by
          calc
            (u + 2) * (3 - u) = 6 + u - u ^ 2 := by ring
            _ = 5 := by rw [hu]; ring]
        rw [show (35 + 12 * v) * (47 - 12 * v) = 205 by
          calc
            (35 + 12 * v) * (47 - 12 * v) = 1645 + 144 * v - 144 * v ^ 2 := by ring
            _ = 205 := by rw [hv]; ring]
      _ = 1025 := by norm_num
  have hbUnit : IsUnit b := by
    have : IsUnit (b * c) := hbc ▸ hoddUnit
    exact (IsUnit.mul_iff.mp this).1
  have hbVal : addVal B b = 0 :=
    GaloisForLFunctions.HTGeometry.addVal_of_isUnit_target hbUnit
  have hroot : z ^ 2 = (2 : B) ^ 1 * b := by
    rw [hz]
    dsimp [b]
    ring
  have hdvd : 2 ∣ 1 :=
    GaloisForLFunctions.HTGeometry.dvd_of_addVal_pow_mul_unit
      (B := B) (p := (2 : B)) (b := b) (z := z)
      (k := 1) (r := 2) htwo hbVal hroot
  norm_num at hdvd

/-- The literal SST quaternion field is ramified at every prime above two. -/
theorem q8Literal_not_isUnramifiedAt_two
    (P : Ideal (𝓞 K3)) [P.IsPrime] (hPtwo : (2 : 𝓞 K3) ∈ P) :
    ¬ Algebra.IsUnramifiedAt ℤ P := by
  intro hunramified
  have hPne : P ≠ ⊥ := by
    intro hP
    rw [hP, Ideal.mem_bot] at hPtwo
    norm_num at hPtwo
  let p : Ideal ℤ := Ideal.span {(2 : ℤ)}
  have hpPrime : p.IsPrime := by
    dsimp [p]
    rw [Ideal.span_singleton_prime (by norm_num)]
    exact Int.prime_two
  letI : p.IsPrime := hpPrime
  have hPover : P.LiesOver p := by
    rw [Ideal.liesOver_span_iff (by exact (inferInstance : P.IsPrime).ne_top) Int.prime_two]
    simpa [p] using hPtwo
  letI : P.LiesOver p := hPover
  let B := Localization.AtPrime P
  letI : Algebra (Localization.AtPrime p) B :=
    Localization.AtPrime.algebraOfLiesOver p P
  letI : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K3) hPne B
  letI : CharZero B := charZero_of_injective_algebraMap
    (IsLocalization.injective B P.primeCompl_le_nonZeroDivisors)
  have hmap : p.map (algebraMap ℤ B) = IsLocalRing.maximalIdeal B :=
    ((Algebra.isUnramifiedAt_iff_map_eq ℤ p P).mp hunramified).2
  have hspan : Ideal.span {(2 : B)} = IsLocalRing.maximalIdeal B := by
    simpa [p, Ideal.map_span] using hmap
  have htwoIrreducible : Irreducible (2 : B) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
      (2 : B) (by norm_num) hspan.symm
  have htwoVal : addVal B (2 : B) = 1 := by
    simpa using GaloisForLFunctions.HTGeometry.addVal_pow_uniformizer htwoIrreducible 1
  let f : 𝓞 K3 →+* B := algebraMap (𝓞 K3) B
  have hu : (f q8LiteralTwoAdicU) ^ 2 = f q8LiteralTwoAdicU + 1 := by
    rw [← map_one f]
    simpa only [map_pow, map_add] using congrArg f q8LiteralTwoAdicU_sq
  have hv : (f q8LiteralTwoAdicV) ^ 2 = f q8LiteralTwoAdicV + 10 := by
    rw [← map_ofNat f 10]
    simpa only [map_pow, map_add] using congrArg f q8LiteralTwoAdicV_sq
  have hz : (f q8LiteralTwoAdicZ) ^ 2 =
      2 * (f q8LiteralTwoAdicU + 2) * (35 + 12 * f q8LiteralTwoAdicV) := by
    rw [← map_ofNat f 2, ← map_ofNat f 35, ← map_ofNat f 12]
    simpa only [map_pow, map_mul, map_add] using congrArg f q8LiteralTwoAdicZ_sq
  exact q8LiteralRadical_not_addVal_two_eq_one
    (f q8LiteralTwoAdicU) (f q8LiteralTwoAdicV) (f q8LiteralTwoAdicZ)
    hu hv hz htwoVal

/-- The rational prime two is genuinely ramified in the literal SST quaternion field. -/
theorem q8Literal_two_not_isUnramifiedIn :
    ¬ Algebra.IsUnramifiedIn (𝓞 K3) (Ideal.span {(2 : ℤ)}) := by
  intro hunramified
  letI : (Ideal.span {(2 : ℤ)}).IsMaximal := Int.prime_two.isMaximal_span_singleton
  obtain ⟨P, hPMax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (S := 𝓞 K3) (Ideal.span {(2 : ℤ)})
  letI : P.IsPrime := hPMax.isPrime
  have hPtwo : (2 : 𝓞 K3) ∈ P := by
    exact (Ideal.liesOver_span_iff hPMax.ne_top Int.prime_two).mp hPover
  exact q8Literal_not_isUnramifiedAt_two P hPtwo
    (hunramified P inferInstance hPover)

/-- Consequently the absolute field discriminant of the literal SST witness is even. -/
theorem q8Literal_two_dvd_discriminant :
    (2 : ℤ) ∣ NumberField.discr K3 := by
  by_contra htwo
  have hunramified :
      Algebra.IsUnramifiedIn (𝓞 K3) (Ideal.span {(2 : ℤ)}) :=
    (NumberField.not_dvd_discr_iff_isUnramifiedIn K3 (𝓞 K3) Int.prime_two).mp htwo
  exact q8Literal_two_not_isUnramifiedIn hunramified

end

end RHTower
