/-
# Counting Eisenstein divisors by normalized-factor submultisets

In a unique-factorization monoid, a divisor is determined by a submultiset
of normalized prime factors and a unit.  This module makes the resulting
cardinality bound explicit for Bourgain's Eisenstein integers.
-/
import GaloisForLFunctions.RHTower.BourgainEisensteinDivisorReduction
import GaloisForLFunctions.RHTower.DivisorBound
import Mathlib.Data.Multiset.Interval

namespace RHTower

open BourgainEisensteinInt

noncomputable section

local instance instEisensteinNormalizationMonoid :
    NormalizationMonoid BourgainEisensteinInt :=
  UniqueFactorizationMonoid.normalizationMonoid

/-- Norm one implies invertibility. -/
theorem eisenstein_isUnit_of_norm_eq_one
    {z : BourgainEisensteinInt} (hz : norm z = 1) :
    IsUnit z := by
  rw [isUnit_iff_dvd_one]
  refine ⟨conj z, ?_⟩
  rw [mul_conj, hz]
  rfl

/-- Every Eisenstein irreducible has norm at least two. -/
theorem two_le_norm_of_irreducible
    {z : BourgainEisensteinInt} (hz : Irreducible z) :
    2 ≤ norm z := by
  have hpos : 0 < norm z := norm_pos.mpr hz.ne_zero
  have hne : norm z ≠ 1 := fun h =>
    hz.not_isUnit (eisenstein_isUnit_of_norm_eq_one h)
  omega

/-- Associated Eisenstein integers have equal norms. -/
theorem norm_eq_of_associated
    {x y : BourgainEisensteinInt} (hxy : Associated x y) :
    norm x = norm y := by
  obtain ⟨u, hu⟩ := hxy
  rw [← hu, norm_mul, norm_coe_unit, mul_one]

/-- Number of normalized-factor submultisets of `y`. -/
noncomputable def eisensteinSubmultisetDivisorCount
    (y : BourgainEisensteinInt) : ℕ :=
  (Finset.Iic (UniqueFactorizationMonoid.normalizedFactors y)).card

/-- Submultiset divisor count is the product of multiplicities plus one. -/
theorem eisensteinSubmultisetDivisorCount_eq_prod
    (y : BourgainEisensteinInt) :
    eisensteinSubmultisetDivisorCount y =
      ∏ q ∈
          (UniqueFactorizationMonoid.normalizedFactors y).toFinset,
        ((UniqueFactorizationMonoid.normalizedFactors y).count q + 1) := by
  rw [eisensteinSubmultisetDivisorCount, Multiset.card_Iic]

/-- Actual divisors are bounded by units times normalized-factor
submultisets. -/
theorem card_eisensteinDivisors_le_units_mul_submultisets
    (y : BourgainEisensteinInt) (hy : y ≠ 0) :
    @Fintype.card {x : BourgainEisensteinInt // x ∣ y}
        (UniqueFactorizationMonoid.fintypeSubtypeDvd y hy) ≤
      Fintype.card BourgainEisensteinIntˣ *
        eisensteinSubmultisetDivisorCount y := by
  classical
  letI : Fintype {x : BourgainEisensteinInt // x ∣ y} :=
    UniqueFactorizationMonoid.fintypeSubtypeDvd y hy
  let factors :=
    UniqueFactorizationMonoid.normalizedFactors y
  let choices : Finset (Multiset BourgainEisensteinInt) :=
    Finset.Iic factors
  let f :
      ({s : Multiset BourgainEisensteinInt // s ∈ choices} ×
        BourgainEisensteinIntˣ) →
        {x : BourgainEisensteinInt // x ∣ y} :=
    fun su => ⟨(su.2 : BourgainEisensteinInt) * su.1.1.prod, by
      rw [(unit_associated_one.mul_right su.1.1.prod).dvd_iff_dvd_left,
        one_mul, ←
          (UniqueFactorizationMonoid.prod_normalizedFactors hy).dvd_iff_dvd_right]
      exact Multiset.prod_dvd_prod_of_le
        (Finset.mem_Iic.mp su.1.2)⟩
  have hsurj : Function.Surjective f := by
    intro x
    have hx : x.1 ≠ 0 := by
      intro hx
      apply hy
      have hdiv := x.2
      rw [hx, zero_dvd_iff] at hdiv
      exact hdiv
    obtain ⟨u, hu⟩ :=
      UniqueFactorizationMonoid.prod_normalizedFactors hx
    refine ⟨⟨⟨UniqueFactorizationMonoid.normalizedFactors x.1, ?_⟩,
      u⟩, ?_⟩
    · rw [Finset.mem_Iic]
      exact
        (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
          hx hy).mp x.2
    · apply Subtype.ext
      exact (mul_comm _ _).trans hu
  have hcard := Fintype.card_le_of_surjective f hsurj
  simpa only [Fintype.card_prod, Fintype.card_coe,
    eisensteinSubmultisetDivisorCount, choices, factors, mul_comm]
    using hcard

end

end RHTower
