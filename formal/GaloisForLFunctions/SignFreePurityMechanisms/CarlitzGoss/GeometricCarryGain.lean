import GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.TopDigits
import Mathlib.Algebra.Ring.GeomSum

/-!
# Strict gain from geometric carry bounds

Distinct terminal exponents obey a single-geometric sum bound. Combining it
with the double-geometric prefix estimate gives a positive weight gain for
every base at least two and residue degree at least two.
-/

open Finset
namespace GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss


/-- Distinct retained exponents, each a full residue degree below the new
last-part maximum, satisfy the single-geometric terminal bound. -/
theorem retained_exponent_sum_le {p s E : ℕ} (hp : 2 ≤ p) (L : Finset ℕ)
    (hgap : ∀ e ∈ L, e + s ≤ E) :
    (p : ℤ) ^ s * ((p : ℤ) - 1) * (∑ e ∈ L, (p : ℤ) ^ e) ≤
      (p : ℤ) * (p : ℤ) ^ E := by
  have hp0 : (0 : ℤ) ≤ p := by omega
  by_cases hL : L.Nonempty
  · obtain ⟨e, he⟩ := hL
    have hsE : s ≤ E := by have := hgap e he; omega
    have hsub : L ⊆ range (E - s + 1) := by
      intro i hi
      have hg := hgap i hi
      exact mem_range.mpr (by omega)
    have hle := sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => pow_nonneg hp0 i)
    have hm := mul_le_mul_of_nonneg_left hle (by omega : (0 : ℤ) ≤ p - 1)
    rw [mul_geom_sum] at hm
    have hm' := mul_le_mul_of_nonneg_left hm (pow_nonneg hp0 s)
    have hexp : s + (E - s + 1) = E + 1 := by omega
    have hpow : (p : ℤ) ^ s * (p : ℤ) ^ (E - s + 1) = (p : ℤ) * (p : ℤ) ^ E := by
      rw [← pow_add, hexp, pow_succ]
      ring
    nlinarith only [hm', hpow, pow_nonneg hp0 s]
  · rw [not_nonempty_iff_eq_empty.mp hL, sum_empty, mul_zero]
    exact mul_nonneg hp0 (pow_nonneg hp0 E)

/-- The double-geometric loss coefficient is strictly below the available
gain for every base `p≥2` and residue degree at least two. -/
theorem carry_gain_coefficient_pos {p q : ℤ} (hp : 2 ≤ p) (hq : p ^ 2 ≤ q) :
    0 < (p - 1) * (q ^ 2 - 3 * q + 1) - p ^ 2 := by
  have hp2 : 4 ≤ p ^ 2 := by nlinarith only [hp, sq_nonneg (p - 2)]
  have hq4 : 4 ≤ q := hp2.trans hq
  have hqpoly : q + 1 ≤ q ^ 2 - 3 * q + 1 := by
    have hm := mul_nonneg (by omega : 0 ≤ q) (by omega : 0 ≤ q - 4)
    nlinarith only [hm]
  have h1 := mul_le_mul_of_nonneg_left hqpoly (by omega : 0 ≤ p - 1)
  have h2 := mul_le_mul_of_nonneg_left hq (by omega : 0 ≤ p - 1)
  have h3 := mul_nonneg (by omega : 0 ≤ p - 2) (sq_nonneg p)
  nlinarith only [h1, h2, h3, hp]

/-- The geometric prefix and terminal estimates force a strict weight gain. -/
theorem positive_gain_of_geometric_bounds {p q P X S Δ : ℤ}
    (hp : 2 ≤ p) (hq : p ^ 2 ≤ q) (hP : 0 < P)
    (hX : p * X ≤ P) (hS : q * (p - 1) * S ≤ p * P)
    (hcost : (q - 1) ^ 2 * (P - X) - (p - 1) * q * (X + S) ≤ (q - 1) ^ 2 * Δ) :
    0 < Δ := by
  have hq0 : 0 ≤ q := le_trans (sq_nonneg p) hq
  have hc := carry_gain_coefficient_pos hp hq
  have hgain := mul_pos hc hP
  have hfactor : 0 ≤ (q - 1) ^ 2 + (p - 1) * q :=
    add_nonneg (sq_nonneg _) (mul_nonneg (by omega) hq0)
  have hX' := mul_le_mul_of_nonneg_left hX hfactor
  have hS' := mul_le_mul_of_nonneg_left hS (by omega : 0 ≤ p)
  have hcost' := mul_le_mul_of_nonneg_left hcost (by omega : 0 ≤ p)
  have htotal : 0 < p * (q - 1) ^ 2 * Δ := by
    nlinarith only [hgain, hX', hS', hcost']
  by_contra hn
  have hz := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (by omega : 0 ≤ p) (sq_nonneg (q - 1))) (show Δ ≤ 0 by omega)
  exact (not_lt_of_ge hz) htotal

end GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss

#print axioms GaloisForLFunctions.SignFreePurityMechanisms.CarlitzGoss.positive_gain_of_geometric_bounds
