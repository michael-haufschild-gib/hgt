import Mathlib

/-!
# The off-diagonal of a separated sampling set

The Gallagher route to a large-values inequality pays a factor `log N` because it controls a
Dirichlet polynomial pointwise by differentiating, and `‖D′‖ ≈ (log N)‖D‖`.  The duality route pays
instead for the off-diagonal of the sampling Gram

```text
∑_{r ≠ s} |b_r| |b_s| / |t_r − t_s| ,
```

and that is bounded by **arithmetic–geometric mean and symmetry alone**: `|b_r||b_s| ≤ (b_r²+b_s²)/2`
turns the double sum into the energy times the worst row sum of the kernel.  For a `δ`-separated
sampling set the row sum is at most `(2/δ)·H_{R−1}`, so the cost is `log R` rather than `log N`.

In density applications the number `R` of large values is far smaller than the polynomial length `N`,
so this is a genuine gain.  Removing the logarithm altogether needs the Montgomery–Vaughan Hilbert
inequality, which exploits cancellation; the bound here uses none.
-/

open Finset

namespace GaloisForLFunctions

/-- **Off-diagonal bound from a symmetric nonnegative kernel.**  For any symmetric nonnegative
kernel whose row sums are at most `H`, the weighted double sum is at most `H` times the energy.
Only AM–GM and symmetry are used — no cancellation. -/
theorem weighted_double_sum_le_rowBound {ι : Type*} [Fintype ι]
    {b : ι → ℝ} {H : ℝ} {K : ι → ι → ℝ}
    (hKsymm : ∀ r s, K r s = K s r) (hKnn : ∀ r s, 0 ≤ K r s)
    (hrow : ∀ r, ∑ s, K r s ≤ H) :
    ∑ r, ∑ s, |b r| * |b s| * K r s ≤ H * ∑ r, (b r) ^ 2 := by
  classical
  have hamgm : ∀ r s : ι, |b r| * |b s| * K r s
      ≤ ((b r) ^ 2 / 2 + (b s) ^ 2 / 2) * K r s := by
    intro r s
    refine mul_le_mul_of_nonneg_right ?_ (hKnn r s)
    nlinarith [sq_nonneg (|b r| - |b s|), sq_abs (b r), sq_abs (b s)]
  have hbound : ∑ r, ∑ s, |b r| * |b s| * K r s
      ≤ ∑ r, ∑ s, ((b r) ^ 2 / 2 + (b s) ^ 2 / 2) * K r s :=
    Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => hamgm r s
  have hsplit : ∑ r, ∑ s, ((b r) ^ 2 / 2 + (b s) ^ 2 / 2) * K r s
      = (∑ r, (b r) ^ 2 / 2 * ∑ s, K r s) + ∑ r, ∑ s, (b s) ^ 2 / 2 * K r s := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  -- the partner half becomes a row sum after commuting and using symmetry
  have hswap : ∑ r, ∑ s, (b s) ^ 2 / 2 * K r s = ∑ s, (b s) ^ 2 / 2 * ∑ r, K s r := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hKsymm r s]
  have hhalf1 : ∑ r, (b r) ^ 2 / 2 * ∑ s, K r s ≤ H / 2 * ∑ r, (b r) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    have hnn : (0 : ℝ) ≤ (b r) ^ 2 / 2 := by positivity
    calc (b r) ^ 2 / 2 * ∑ s, K r s ≤ (b r) ^ 2 / 2 * H :=
          mul_le_mul_of_nonneg_left (hrow r) hnn
      _ = H / 2 * (b r) ^ 2 := by ring
  have hhalf2 : ∑ s, (b s) ^ 2 / 2 * ∑ r, K s r ≤ H / 2 * ∑ r, (b r) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have hnn : (0 : ℝ) ≤ (b s) ^ 2 / 2 := by positivity
    calc (b s) ^ 2 / 2 * ∑ r, K s r ≤ (b s) ^ 2 / 2 * H :=
          mul_le_mul_of_nonneg_left (hrow s) hnn
      _ = H / 2 * (b s) ^ 2 := by ring
  calc ∑ r, ∑ s, |b r| * |b s| * K r s
      ≤ ∑ r, ∑ s, ((b r) ^ 2 / 2 + (b s) ^ 2 / 2) * K r s := hbound
    _ = (∑ r, (b r) ^ 2 / 2 * ∑ s, K r s) + ∑ r, ∑ s, (b s) ^ 2 / 2 * K r s := hsplit
    _ = (∑ r, (b r) ^ 2 / 2 * ∑ s, K r s) + ∑ s, (b s) ^ 2 / 2 * ∑ r, K s r := by rw [hswap]
    _ ≤ H / 2 * (∑ r, (b r) ^ 2) + H / 2 * ∑ r, (b r) ^ 2 := by linarith [hhalf1, hhalf2]
    _ = H * ∑ r, (b r) ^ 2 := by ring

/-- The reciprocal-separation kernel: `0` on the diagonal, `1/|t r − t s|` off it.  Symmetric and
nonnegative by construction. -/
noncomputable def sepKernel {ι : Type*} [DecidableEq ι] (t : ι → ℝ) : ι → ι → ℝ :=
  fun r s => if r = s then 0 else 1 / |t r - t s|

theorem sepKernel_symm {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (r s : ι) :
    sepKernel t r s = sepKernel t s r := by
  unfold sepKernel
  by_cases h : r = s
  · simp [h]
  · rw [if_neg h, if_neg (Ne.symm h), abs_sub_comm]

theorem sepKernel_nonneg {ι : Type*} [DecidableEq ι] (t : ι → ℝ) (r s : ι) :
    0 ≤ sepKernel t r s := by
  unfold sepKernel
  by_cases h : r = s
  · simp [h]
  · rw [if_neg h]
    positivity

/-- **The sampling off-diagonal bound.**  For a sampling set whose reciprocal-separation row sums are
at most `H`, the off-diagonal Gram weight is at most `H` times the energy — with `H = O(log R / δ)`
for a `δ`-separated set, against the `log N` of the Gallagher route. -/
theorem sampling_offDiagonal_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {t b : ι → ℝ} {H : ℝ} (hrow : ∀ r, ∑ s, sepKernel t r s ≤ H) :
    ∑ r, ∑ s, |b r| * |b s| * sepKernel t r s ≤ H * ∑ r, (b r) ^ 2 :=
  weighted_double_sum_le_rowBound (sepKernel_symm t) (sepKernel_nonneg t) hrow

end GaloisForLFunctions
