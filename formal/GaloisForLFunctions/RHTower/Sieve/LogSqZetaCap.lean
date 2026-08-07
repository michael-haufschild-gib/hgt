import GaloisForLFunctions.RHTower.CreaseBudgetPrimeMass
/-!
# The logarithmically weighted partial zeta cap

A squared logarithm is absorbed by a power: `log t ≤ t^δ/δ` with `δ = (w−1)/4` turns `n^{−w}(log n)²` into
`(16/(w−1)²)·n^{−(w+1)/2}`, and the partial zeta cap of the corpus bounds the resulting sum.  Hence

`∑_{n ≤ N} n^{−w}(log n)² ≤ (16/(w−1)²)·(1 + 2/(w−1))`,

uniformly in `N`, for every `w > 1`.  At the two exponents the sieve majorant produces:

`∑_{n ≤ N} n^{1−2σ}(log n)² ≤ (16/(2σ−2)²)(1 + 2/(2σ−2))`,
`∑_{n ≤ N} n^{−2σ}(log n)² ≤ (16/(2σ−1)²)(1 + 2/(2σ−1))`,   `σ > 1`.

Both are uniform in `N`; the first blows up like `(log N)³` at `σ = 1 + 1/log N`, the second stays bounded.
These are the last analytic inputs of the Granville–Harper–Soundararajan chain, and neither has arithmetic
content.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- **The logarithmically weighted partial zeta cap.**  A squared logarithm is absorbed by a power: with
`δ = (w−1)/4` the inequality `log t ≤ t^δ/δ` gives

`∑_{n ≤ N} n^{−w}(log n)² ≤ (16/(w−1)²)·(1 + 2/(w−1))`,

uniformly in `N`.  Only `w > 1` is needed, and the bound is the partial zeta cap of the corpus at the
shifted exponent `(w+1)/2`. -/
theorem sum_Icc_logSq_rpow_neg_le {w : ℝ} (hw : 1 < w) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-w) * (Real.log n) ^ 2)
      ≤ (16 / (w - 1) ^ 2) * (1 + 2 / (w - 1)) := by
  classical
  set δ : ℝ := (w - 1) / 4 with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    linarith
  have hshift : (1 : ℝ) < (w + 1) / 2 := by linarith
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      (n : ℝ) ^ (-w) * (Real.log n) ^ 2 ≤ (1 / δ ^ 2) * (n : ℝ) ^ (-((w + 1) / 2)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hn1
    have hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ δ / δ := Real.log_le_rpow_div hnpos.le hδ
    have hsq : (Real.log (n : ℝ)) ^ 2 ≤ (1 / δ ^ 2) * (n : ℝ) ^ (2 * δ) := by
      have h1 : (Real.log (n : ℝ)) ^ 2 ≤ ((n : ℝ) ^ δ / δ) ^ 2 :=
        pow_le_pow_left₀ hlogn hlog 2
      have h2 : ((n : ℝ) ^ δ / δ) ^ 2 = (1 / δ ^ 2) * ((n : ℝ) ^ δ) ^ 2 := by
        field_simp
      have h3 : ((n : ℝ) ^ δ) ^ 2 = (n : ℝ) ^ (2 * δ) := by
        rw [← Real.rpow_natCast ((n : ℝ) ^ δ) 2, ← Real.rpow_mul hnpos.le]
        norm_num
        ring_nf
      rw [h2, h3] at h1
      exact h1
    have hexp : (n : ℝ) ^ (-w) * (n : ℝ) ^ (2 * δ) = (n : ℝ) ^ (-((w + 1) / 2)) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      rw [hδdef]
      ring
    calc (n : ℝ) ^ (-w) * (Real.log n) ^ 2
        ≤ (n : ℝ) ^ (-w) * ((1 / δ ^ 2) * (n : ℝ) ^ (2 * δ)) :=
          mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hnpos.le _)
      _ = (1 / δ ^ 2) * ((n : ℝ) ^ (-w) * (n : ℝ) ^ (2 * δ)) := by ring
      _ = (1 / δ ^ 2) * (n : ℝ) ^ (-((w + 1) / 2)) := by rw [hexp]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hcap := RHTower.sum_Icc_rpow_neg_le hshift N
  have hstep : (1 / δ ^ 2) * ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-((w + 1) / 2))
      ≤ (1 / δ ^ 2) * (1 + 1 / ((w + 1) / 2 - 1)) :=
    mul_le_mul_of_nonneg_left hcap (by positivity)
  refine hstep.trans (le_of_eq ?_)
  rw [hδdef]
  have hw1 : w - 1 ≠ 0 := ne_of_gt (by linarith)
  have hw1' : (-1 + w) ≠ 0 := by
    intro h
    have hwe : w = 1 := by linarith
    rw [hwe] at hw
    linarith
  have hcancel : (-1 + w) * (-1 + w)⁻¹ = 1 := mul_inv_cancel₀ hw1'
  field_simp
  linear_combination (32 : ℝ) * hcancel

/-- The linear-part sum of the sieve majorant, evaluated: `w = 2σ − 1`. -/
theorem sum_Icc_logSq_rpow_one_sub_two_mul_le {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (1 - 2 * σ) * (Real.log n) ^ 2)
      ≤ (16 / (2 * σ - 2) ^ 2) * (1 + 2 / (2 * σ - 2)) := by
  have hw : (1 : ℝ) < 2 * σ - 1 := by linarith
  have hrw : ∀ n : ℕ, (n : ℝ) ^ (1 - 2 * σ) = (n : ℝ) ^ (-(2 * σ - 1)) := by
    intro n
    congr 1
    ring
  have hsum : (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (1 - 2 * σ) * (Real.log n) ^ 2)
      = ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ - 1)) * (Real.log n) ^ 2 :=
    Finset.sum_congr rfl fun n _ => by rw [hrw n]
  rw [hsum]
  have h := sum_Icc_logSq_rpow_neg_le hw N
  have hcoeff : (2 * σ - 1) - 1 = 2 * σ - 2 := by ring
  rwa [hcoeff] at h

/-- The constant-part sum of the sieve majorant, evaluated: `w = 2σ`. -/
theorem sum_Icc_logSq_rpow_neg_two_mul_le {σ : ℝ} (hσ : 1 < σ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(2 * σ)) * (Real.log n) ^ 2)
      ≤ (16 / (2 * σ - 1) ^ 2) * (1 + 2 / (2 * σ - 1)) := by
  have hw : (1 : ℝ) < 2 * σ := by linarith
  exact sum_Icc_logSq_rpow_neg_le hw N

end RHTower.Sieve
end
