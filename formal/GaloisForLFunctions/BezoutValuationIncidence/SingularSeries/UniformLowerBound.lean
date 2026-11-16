import GaloisForLFunctions.BezoutValuationIncidence.HardyLittlewoodSingularSeriesOfTheDampedSource
import GaloisForLFunctions.HTGeometry.Analysis.WallisSubproducts

/-!
# A uniform lower bound for even-gap singular series

Deleting composite candidates from the Li–Yang reciprocal-square majorant
gives `𝔖(2h) ≥ 9/8` for every positive integer `h`. Exploiting parity and
Wallis' product improves this to `𝔖(2h) ≥ 4/π`. Both estimates apply to the
Hardy–Littlewood singular series carried by the damped arithmetic source.
-/

namespace GaloisForLFunctions.BezoutValuationIncidence

open Finset Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry.ReciprocalPowerProducts
open GaloisForLFunctions.BiScaleUncertainty

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
  let S := P.image fun p : Nat.Primes => (p : ℕ) - 3
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
  have hs : (HTGeometry.ReciprocalPowerProducts.slope 0 + 1) /
      HTGeometry.ReciprocalPowerProducts.slope 0 = (2 : ℝ) := by
    norm_num [HTGeometry.ReciprocalPowerProducts.slope]
  have hf : (1 - 1 / ((1 : ℝ) + 2) ^ (0 + 2))⁻¹ = (9 / 8 : ℝ) := by norm_num
  simp only [Nat.cast_one, hf, hs] at h
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
  · simp only [zero_sub, neg_div, ← sub_eq_add_neg]
    exact le_rfl

private theorem singularSeries_even_lower_bound (h : ℕ) (B : ℝ)
    (hB : ∀ P : Finset Nat.Primes, (∀ p ∈ P, (p : ℕ) ≠ 2) →
      B ≤ 2 * ∏ p ∈ P, (1 - 1 / ((p : ℝ) - 1) ^ 2)) :
    B ≤ hardyLittlewoodSingularSeries (2 * (h + 1)) := by
  let p₂ : Nat.Primes := ⟨2, Nat.prime_two⟩
  apply ge_of_tendsto (hasProd_hardyLittlewoodSingularSeries (by omega))
  refine eventually_atTop.mpr ⟨{p₂}, ?_⟩
  intro P hP
  have hp₂ : p₂ ∈ P := hP (mem_singleton_self p₂)
  have hodd : ∀ p ∈ P.erase p₂, (p : ℕ) ≠ 2 := by
    intro p hp heq
    exact (mem_erase.mp hp).1 (Subtype.ext heq)
  have hbase := hB (P.erase p₂) hodd
  have hcomp : (∏ p ∈ P.erase p₂, (1 - 1 / ((p : ℝ) - 1) ^ 2)) ≤
      ∏ p ∈ P.erase p₂,
        (1 + ramanujanLagWeight (2 * (h + 1)) p / ((p : ℝ) - 1) ^ 2) := by
    apply Finset.prod_le_prod
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
    norm_num [p₂, ramanujanLagWeight_prime Nat.prime_two]
  rw [← mul_prod_erase P _ hp₂, htwo]
  exact hbase.trans (mul_le_mul_of_nonneg_left hcomp (by norm_num))

/-- Every positive even gap has singular series at least `9/8`. -/
theorem hardyLittlewoodSingularSeries_even_ge_nine_eighths (h : ℕ) :
    (9 / 8 : ℝ) ≤ hardyLittlewoodSingularSeries (2 * (h + 1)) :=
  singularSeries_even_lower_bound h (9 / 8)
    fun P hP => (odd_prime_product_lower P hP).le

private theorem odd_prime_product_wallis (P : Finset Nat.Primes)
    (hP : ∀ p ∈ P, (p : ℕ) ≠ 2) :
    4 / Real.pi ≤ 2 * ∏ p ∈ P, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  have hn (p : Nat.Primes) (hp : p ∈ P) :
      2 * (((p : ℕ) - 3) / 2) + 3 = (p : ℕ) := by
    have hp2 := p.prop.two_le
    have hpne := hP p hp
    have hodd : (p : ℕ) % 2 ≠ 0 := by
      intro he
      exact hpne ((Nat.prime_dvd_prime_iff_eq Nat.prime_two p.prop).mp
        (Nat.dvd_of_mod_eq_zero he)).symm
    omega
  have hc (p : Nat.Primes) (hp : p ∈ P) :
      2 * ((((p : ℕ) - 3) / 2 : ℕ) : ℝ) + 2 = (p : ℝ) - 1 := by
    have he : 2 * ((((p : ℕ) - 3) / 2 : ℕ) : ℝ) + 3 = (p : ℝ) := by
      exact_mod_cast hn p hp
    linarith only [he]
  have hi : Set.InjOn (fun p : Nat.Primes => ((p : ℕ) - 3) / 2) P := by
    intro p hp q hq he
    apply Subtype.ext
    have hp' := hn p hp
    have hq' := hn q hq
    change ((p : ℕ) - 3) / 2 = ((q : ℕ) - 3) / 2 at he
    omega
  have hw := wallis_subproduct_le
    (P.image fun p : Nat.Primes => ((p : ℕ) - 3) / 2)
  rw [prod_image hi] at hw
  have heq : (∏ p ∈ P,
      (1 - 1 / (2 * ((((p : ℕ) - 3) / 2 : ℕ) : ℝ) + 2) ^ 2)⁻¹) =
      (∏ p ∈ P, (1 - 1 / ((p : ℝ) - 1) ^ 2))⁻¹ := by
    rw [← prod_inv_distrib]
    exact prod_congr rfl fun p hp => by rw [hc p hp]
  rw [heq, ← one_div] at hw
  have hpos : 0 < ∏ p ∈ P, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
    apply prod_pos
    intro p hp
    simpa only [hc p hp] using even_factor_pos (((p : ℕ) - 3) / 2)
  have h := (div_le_iff₀ hpos).mp hw
  apply (div_le_iff₀ Real.pi_pos).mpr
  nlinarith only [h]

/-- Wallis' product gives a parity-sensitive uniform lower bound for every positive even gap. -/
theorem hardyLittlewoodSingularSeries_even_ge_four_div_pi (h : ℕ) :
    4 / Real.pi ≤ hardyLittlewoodSingularSeries (2 * (h + 1)) :=
  singularSeries_even_lower_bound h (4 / Real.pi) odd_prime_product_wallis

#print axioms hardyLittlewoodSingularSeries_even_ge_nine_eighths
#print axioms hardyLittlewoodSingularSeries_even_ge_four_div_pi

end GaloisForLFunctions.BezoutValuationIncidence
