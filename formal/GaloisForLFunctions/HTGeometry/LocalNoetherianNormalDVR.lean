import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# A normal local ring of dimension one is a discrete valuation ring

A Noetherian integrally closed local domain of Krull dimension one is a discrete valuation ring.
mathlib provides this only through the Dedekind domain interface, where the dimension hypothesis
is packaged with the global conditions of a Dedekind ring; the purely local statement is what a
local ring of dimension one needs, whether it arises as a localisation at a height-one prime or
as the local ring of a scheme at a codimension-one point.
-/

namespace GaloisForLFunctions.HTGeometry

open IsLocalRing


variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem not_isField_of_ringKrullDim_eq_one (h : ringKrullDim R = 1) : ¬ IsField R := by
  intro hfield
  have hmax : maximalIdeal R = ⊥ := IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
  have h1 : (maximalIdeal R).height = 0 := by rw [hmax, Ideal.height_bot]
  have h2 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
  rw [h1, h] at h2
  exact absurd h2.symm (by decide)

theorem dimensionLEOne_of_ringKrullDim_eq_one [IsDomain R] (h : ringKrullDim R = 1) :
    Ring.DimensionLEOne R := by
  constructor
  intro Q hQbot hQprime
  haveI := hQprime
  have hmle : (maximalIdeal R).height ≤ ((1 : ℕ) : ℕ∞) := by
    have h2 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [h] at h2
    rw [Nat.cast_one]
    exact le_of_eq (by exact_mod_cast h2)
  have hQle : Q ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hQprime.ne_top
  rcases eq_or_lt_of_le hQle with heq | hlt
  · rw [heq]
    exact maximalIdeal.isMaximal _
  · exfalso
    have hlt1 : Q.height < ((1 : ℕ) : ℕ∞) := Ideal.height_le_iff.mp hmle _ hQprime hlt
    rw [Nat.cast_one] at hlt1
    exact hQbot (Ideal.height_eq_zero_iff_eq_bot.mp (Order.lt_one_iff.mp hlt1))

/-- **A Noetherian integrally closed local domain of dimension one is a discrete valuation
ring.** -/
theorem isDiscreteValuationRing_of_ringKrullDim_eq_one [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (h : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  haveI := dimensionLEOne_of_ringKrullDim_eq_one h
  haveI : IsDedekindRing R := ⟨⟩
  have htfae := IsDiscreteValuationRing.TFAE R (not_isField_of_ringKrullDim_eq_one h)
  have hiff : IsDedekindDomain R ↔ IsDiscreteValuationRing R := htfae.out 2 0
  exact hiff.mp inferInstance


end GaloisForLFunctions.HTGeometry
