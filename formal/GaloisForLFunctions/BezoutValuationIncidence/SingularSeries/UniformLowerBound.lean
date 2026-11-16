import GaloisForLFunctions.BezoutValuationIncidence.HardyLittlewoodSingularSeriesOfTheDampedSource
import GaloisForLFunctions.HTGeometry.Analysis.ReciprocalPowerProducts

/-!
# A uniform lower bound for even-gap singular series

The reciprocal-square product bounds the odd-prime factors from below.
The missing composite prime candidate four removes the factor `9/8` from
the reciprocal majorant, giving `𝔖(2h) ≥ 9/8` for every positive integer `h`.
This is an application of the Li–Yang finite-product estimate to the
Hardy–Littlewood singular series carried by the damped arithmetic source.
-/

namespace GaloisForLFunctions.BezoutValuationIncidence

open Finset Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry.ReciprocalPowerProducts

private theorem odd_prime_product_lower (P : Finset Nat.Primes)
    (hP : ∀ p ∈ P, (p : ℕ) ≠ 2) :
    (9 / 8 : ℝ) < 2 * ∏ p ∈ P, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  have hp3 (p : Nat.Primes) (hp : p ∈ P) : 3 ≤ (p : ℕ) := by
    have := p.prop.two_le
    have := hP p hp
    omega
  have hc (p : Nat.Primes) (hp : p ∈ P) :
      (((p : ℕ) - 3 : ℕ) : ℝ) + 2 = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (hp3 p hp)]
    norm_num
    ring
  have hi : Set.InjOn (fun p : Nat.Primes => (p : ℕ) - 3) P := by
    intro p hp q hq h
    apply Subtype.ext
    have := hp3 p hp
    have := hp3 q hq
    change (p : ℕ) - 3 = (q : ℕ) - 3 at h
    omega
  let S := P.image fun p => (p : ℕ) - 3
  have hone : 1 ∉ S := by
    rintro h
    obtain ⟨p, hp, heq⟩ := mem_image.mp h
    have h3 := hp3 p hp
    have hfour : (p : ℕ) = 4 := by omega
    have hprime := p.prop
    rw [hfour] at hprime
    norm_num at hprime
  have h := subproduct_lt_uniform 0 (insert 1 S)
  rw [prod_insert hone] at h
  dsimp [S] at h
  rw [prod_image hi] at h
  have heq : (∏ p ∈ P, (1 - 1 / ((((p : ℕ) - 3 : ℕ) : ℝ) + 2) ^ (0 + 2))⁻¹) =
      (∏ p ∈ P, (1 - 1 / ((p : ℝ) - 1) ^ 2))⁻¹ := by
    rw [← prod_inv_distrib]
    exact prod_congr rfl fun p hp => by rw [hc p hp]
  rw [heq] at h
  norm_num [slope] at h
  have hpos : 0 < ∏ p ∈ P, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    apply prod_pos
    intro p hp
    have h := factor_pos 0 ((p : ℕ) - 3)
    simpa only [hc p hp] using h
  rwa [← div_eq_mul_inv, div_lt_iff₀ hpos] at h

private theorem even_local_factor_ge (h : ℕ) (p : Nat.Primes) :
    1 - 1 / ((p : ℝ) - 1) ^ 2 ≤
      1 + ramanujanLagWeight (2 * (h + 1)) p / ((p : ℝ) - 1) ^ 2 := by
  rw [ramanujanLagWeight_prime p.prop]
  split_ifs
  · have hp1 : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
    have ha : 0 ≤ ((p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 := by positivity
    have hb : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    linarith only [ha, hb]
  · ring

/-- Every positive even gap has singular series at least `9/8`. -/
theorem hardyLittlewoodSingularSeries_even_ge_nine_eighths (h : ℕ) :
    (9 / 8 : ℝ) ≤ hardyLittlewoodSingularSeries (2 * (h + 1)) := by
  let p₂ : Nat.Primes := ⟨2, Nat.prime_two⟩
  apply le_of_tendsto (hasProd_hardyLittlewoodSingularSeries (by omega))
  refine eventually_atTop.mpr ⟨{p₂}, ?_⟩
  intro P hP
  have hp₂ : p₂ ∈ P := hP (mem_singleton_self p₂)
  have hodd : ∀ p ∈ P.erase p₂, (p : ℕ) ≠ 2 := by
    intro p hp heq
    exact (mem_erase.mp hp).1 (Subtype.ext heq)
  have hbase := odd_prime_product_lower (P.erase p₂) hodd
  have hcomp : (∏ p ∈ P.erase p₂, (1 - 1 / ((p : ℝ) - 1) ^ 2)) ≤
      ∏ p ∈ P.erase p₂,
        (1 + ramanujanLagWeight (2 * (h + 1)) p / ((p : ℝ) - 1) ^ 2) := by
    apply prod_le_prod
    · intro p hp
      have hp3 : 3 ≤ (p : ℕ) := by
        have := p.prop.two_le
        have := hodd p hp
        omega
      have hc : (((p : ℕ) - 3 : ℕ) : ℝ) + 2 = (p : ℝ) - 1 := by
        rw [Nat.cast_sub hp3]
        norm_num
        ring
      simpa only [hc] using (factor_pos 0 ((p : ℕ) - 3)).le
    · intro p _
      exact even_local_factor_ge h p
  have htwo : 1 + ramanujanLagWeight (2 * (h + 1)) p₂ / ((p₂ : ℝ) - 1) ^ 2 = 2 := by
    simp [p₂, ramanujanLagWeight_prime Nat.prime_two]
  rw [← mul_prod_erase P _ hp₂, htwo]
  exact hbase.le.trans (mul_le_mul_of_nonneg_left hcomp (by norm_num))

#print axioms hardyLittlewoodSingularSeries_even_ge_nine_eighths

end GaloisForLFunctions.BezoutValuationIncidence
