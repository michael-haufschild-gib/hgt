import GaloisForLFunctions.RHTower.Sieve.AlmostOrthogonality

/-!
# The geometric sum bound

A truncated geometric series with ratio on or inside the unit circle is controlled by the distance
of its ratio from one, with no dependence on the length:

`‖∑_{n < N} ζ^n‖ ≤ 2 / ‖ζ - 1‖`.

The proof is the closed form `(ζ^N - 1)/(ζ - 1)` together with `‖ζ^N‖ ≤ 1`.  Shifting the range only
multiplies by a unimodular factor, so the same bound holds on any interval of indices.

This is the elementary input behind every Gram-row estimate for exponential families: the
correlation of two exponentials at distinct frequencies is a geometric sum whose ratio is their
quotient, so the off-diagonal Gram entries are bounded by the reciprocal separation.
-/

namespace RHTower.Sieve

open Finset

/-- **Geometric sum bound.**  Uniform in the length. -/
theorem norm_geom_sum_le {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) (hne : ζ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, ζ ^ n‖ ≤ 2 / ‖ζ - 1‖ := by
  have hsub : ζ - 1 ≠ 0 := sub_ne_zero.2 hne
  have hden : (0 : ℝ) < ‖ζ - 1‖ := norm_pos_iff.2 hsub
  rw [geom_sum_eq hne, norm_div, div_le_div_iff_of_pos_right hden]
  refine le_trans (norm_sub_le _ _) ?_
  have hpow : ‖ζ ^ N‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg ζ) hζ
  simp only [norm_one]
  linarith

/-- The same bound on any interval of indices. -/
theorem norm_geom_sum_Ico_le {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) (hne : ζ ≠ 1) (a b : ℕ) :
    ‖∑ n ∈ Finset.Ico a b, ζ ^ n‖ ≤ 2 / ‖ζ - 1‖ := by
  classical
  have hshift : ∑ n ∈ Finset.Ico a b, ζ ^ n = ζ ^ a * ∑ i ∈ Finset.range (b - a), ζ ^ i := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pow_add]
  rw [hshift, norm_mul]
  have hpow : ‖ζ ^ a‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg ζ) hζ
  have hbase := norm_geom_sum_le hζ hne (b - a)
  have hnn : (0 : ℝ) ≤ ‖∑ i ∈ Finset.range (b - a), ζ ^ i‖ := norm_nonneg _
  have hden : (0 : ℝ) ≤ 2 / ‖ζ - 1‖ := by
    have : (0 : ℝ) < ‖ζ - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    positivity
  nlinarith [hpow, hbase, hnn, norm_nonneg (ζ ^ a)]

/-- The correlation of two unimodular exponential rows is a geometric sum in their quotient. -/
theorem sum_conj_pow_mul_pow (ξ η : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (starRingEnd ℂ) (ξ ^ n) * η ^ n
      = ∑ n ∈ Finset.range N, ((starRingEnd ℂ) ξ * η) ^ n := by
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_pow, ← mul_pow]

/-- **Off-diagonal Gram entry.**  Two distinct unimodular frequencies correlate at most like the
reciprocal of their separation. -/
theorem norm_sum_conj_pow_mul_pow_le {ξ η : ℂ} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ ≤ 1)
    (hne : (starRingEnd ℂ) ξ * η ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, (starRingEnd ℂ) (ξ ^ n) * η ^ n‖
      ≤ 2 / ‖(starRingEnd ℂ) ξ * η - 1‖ := by
  rw [sum_conj_pow_mul_pow ξ η N]
  refine norm_geom_sum_le ?_ hne N
  rw [norm_mul, RCLike.norm_conj, hξ, one_mul]
  exact hη

end RHTower.Sieve
