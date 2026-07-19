import GaloisForLFunctions.HTGeometry.PrimeRadialFusionFieldCorrespondence
import Mathlib.NumberTheory.FrobeniusNumber

/-!
# The prime-radial fusion conductor law

The orders of the nonzero profiles in a fusion algebra form an additive semigroup.  Schur's
conductor theorem for additive submonoids of `ℕ` then gives an exact eventual congruence law.  In
the prime-radial realization this is a law for the valuation channels of an actual embedded
hypertranscendental fusion field.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- A positive order occurs in `A` when it is the formal order of a nonzero profile in `A`. -/
def PrimeRadialOrderOccurs
    (A : NonUnitalSubalgebra ℂ PrimeRadialProfile) (n : Nat) : Prop :=
  ∃ u : A, u ≠ 0 ∧ (PowerSeries.order (u : PowerSeries ℂ)).toNat = n

/-- The order spectrum with zero adjoined is an additive submonoid of `ℕ`. -/
def primeRadialOrderSubmonoid
    (A : NonUnitalSubalgebra ℂ PrimeRadialProfile) : AddSubmonoid Nat where
  carrier := {n | n = 0 ∨ PrimeRadialOrderOccurs A n}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro m n hm hn
    rcases hm with rfl | ⟨u, hu, rfl⟩
    · simpa using hn
    rcases hn with rfl | ⟨v, hv, rfl⟩
    · exact Or.inr ⟨u, hu, by simp⟩
    · right
      refine ⟨u * v, mul_ne_zero hu hv, ?_⟩
      have hu' : (u : PowerSeries ℂ) ≠ 0 := by simpa using hu
      have hv' : (v : PowerSeries ℂ) ≠ 0 := by simpa using hv
      change (PowerSeries.order ((u : PowerSeries ℂ) * (v : PowerSeries ℂ))).toNat =
        (PowerSeries.order (u : PowerSeries ℂ)).toNat +
          (PowerSeries.order (v : PowerSeries ℂ)).toNat
      rw [PowerSeries.order_mul,
        ENat.toNat_add (PowerSeries.order_eq_top.not.mpr hu')
          (PowerSeries.order_eq_top.not.mpr hv')]

@[simp]
theorem mem_primeRadialOrderSubmonoid_iff
    (A : NonUnitalSubalgebra ℂ PrimeRadialProfile) (n : Nat) :
    n ∈ primeRadialOrderSubmonoid A ↔
      n = 0 ∨ PrimeRadialOrderOccurs A n :=
  Iff.rfl

/-- No nonzero zero-constant profile has formal order zero. -/
theorem primeRadialOrderOccurs_pos
    {A : NonUnitalSubalgebra ℂ PrimeRadialProfile} {n : Nat}
    (hn : PrimeRadialOrderOccurs A n) : 0 < n := by
  obtain ⟨u, hu, rfl⟩ := hn
  have hu' : (u : PowerSeries ℂ) ≠ 0 := by simpa using hu
  have hcoeff := PowerSeries.coeff_order hu'
  have hzero : PowerSeries.coeff 0 (u : PowerSeries ℂ) = 0 :=
    ((u : PrimeRadialProfile).2)
  by_contra hnot
  have hord : (PowerSeries.order (u : PowerSeries ℂ)).toNat = 0 := Nat.eq_zero_of_not_pos hnot
  rw [hord, hzero] at hcoeff
  exact hcoeff rfl

/-- The conductor modulus of a radial fusion algebra: the gcd of all occurring orders, with zero
adjoined. -/
def primeRadialConductorModulus
    (A : NonUnitalSubalgebra ℂ PrimeRadialProfile) : Nat :=
  Nat.setGcd (primeRadialOrderSubmonoid A : Set Nat)

theorem primeRadialConductorModulus_dvd_of_orderOccurs
    {A : NonUnitalSubalgebra ℂ PrimeRadialProfile} {n : Nat}
    (hn : PrimeRadialOrderOccurs A n) :
    primeRadialConductorModulus A ∣ n := by
  apply Nat.setGcd_dvd_of_mem
  exact (mem_primeRadialOrderSubmonoid_iff A n).mpr (Or.inr hn)

/-- A nonzero radial fusion algebra has a nonzero conductor modulus. -/
theorem primeRadialConductorModulus_ne_zero
    (A : NonUnitalSubalgebra ℂ PrimeRadialProfile)
    (hA : ∃ u : A, u ≠ 0) :
    primeRadialConductorModulus A ≠ 0 := by
  obtain ⟨u, hu⟩ := hA
  let n := (PowerSeries.order (u : PowerSeries ℂ)).toNat
  have hn : PrimeRadialOrderOccurs A n := ⟨u, hu, rfl⟩
  have hnpos : 0 < n := primeRadialOrderOccurs_pos hn
  intro hd
  have hdvd := primeRadialConductorModulus_dvd_of_orderOccurs hn
  rw [hd] at hdvd
  exact hnpos.ne' (zero_dvd_iff.mp hdvd)

/-- **Exact conductor law.**  Beyond one finite threshold, a positive valuation order occurs in
the fusion algebra exactly when it is divisible by the conductor modulus. -/
theorem primeRadialOrderOccurs_iff_dvd_eventually
    (A : NonUnitalSubalgebra ℂ PrimeRadialProfile) :
    ∃ c : Nat, ∀ n ≥ c,
      PrimeRadialOrderOccurs A n ↔ primeRadialConductorModulus A ∣ n := by
  obtain ⟨c, hc⟩ :=
    Nat.exists_mem_closure_of_ge (primeRadialOrderSubmonoid A : Set Nat)
  refine ⟨c + 1, ?_⟩
  intro n hn
  have hnc : c ≤ n := le_trans (Nat.le_succ c) hn
  have hnzero : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (Nat.zero_lt_succ c) hn)
  constructor
  · exact primeRadialConductorModulus_dvd_of_orderOccurs
  · intro hdvd
    have hmemClosure := hc n hnc hdvd
    have hmem : n ∈ primeRadialOrderSubmonoid A := by
      simpa only [AddSubmonoid.closure_eq] using hmemClosure
    rcases (mem_primeRadialOrderSubmonoid_iff A n).mp hmem with hzero | hoccurs
    · exact (hnzero hzero).elim
    · exact hoccurs

/-- The exact eventual spectrum is periodic with the conductor modulus. -/
theorem primeRadialOrderOccurs_add_modulus_iff_eventually
    (A : NonUnitalSubalgebra ℂ PrimeRadialProfile) :
    ∃ c : Nat, ∀ n ≥ c,
      PrimeRadialOrderOccurs A (n + primeRadialConductorModulus A) ↔
        PrimeRadialOrderOccurs A n := by
  obtain ⟨c, hc⟩ := primeRadialOrderOccurs_iff_dvd_eventually A
  refine ⟨c, ?_⟩
  intro n hn
  rw [hc (n + primeRadialConductorModulus A) (hn.trans (Nat.le_add_right n _)), hc n hn]
  simpa [Nat.add_comm] using
    (Nat.dvd_add_iff_left (dvd_refl (primeRadialConductorModulus A)))

/-- **Fusion-field conductor capstone.**  Every formal-profile subalgebra gives an exact embedded
fusion-closed differential field, and its nonzero valuation channels obey the conductor law. -/
theorem primeRadialFusionField_conductorLaw
    (A : NonUnitalSubalgebra ℂ PrimeRadialProfile) :
    PrimeRadialCarrierFusionClosed A.toSubmodule ∧
      ∃ c : Nat, ∀ n ≥ c,
        PrimeRadialOrderOccurs A n ↔ primeRadialConductorModulus A ∣ n := by
  exact ⟨primeRadialFusionField_fusionClosed A,
    primeRadialOrderOccurs_iff_dvd_eventually A⟩

end

end GaloisForLFunctions.HTGeometry
