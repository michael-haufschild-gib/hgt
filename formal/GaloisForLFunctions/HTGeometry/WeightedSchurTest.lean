import GaloisForLFunctions.HTGeometry.SeparatedOffDiagonalBound

/-!
# The weighted Schur test

A symmetric nonnegative kernel whose *weighted* row sums satisfy `∑ₛ K r s · w s ≤ H · w r` bounds
the quadratic form by `H` times the energy.  The unweighted statement is the case `w = 1`; the
weight is what makes the test usable on kernels whose plain row sums diverge, the Hilbert–Hankel
kernel `1/(m+n+1)` among them.

The proof is the weighted arithmetic–geometric inequality
`|b r| |b s| ≤ ½ (b r² · w s / w r + b s² · w r / w s)`, which after clearing the positive weights
is `(|b r| w s - |b s| w r)² ≥ 0`, followed by symmetry to recognise both halves as weighted row
sums.
No cancellation is used.
-/

open Finset

namespace GaloisForLFunctions

/-- **The weighted Schur test.**  A symmetric nonnegative kernel with weighted row sums bounded by
`H · w` bounds the quadratic form by `H` times the energy. -/
theorem weighted_double_sum_le_weightedRowBound {ι : Type*} [Fintype ι]
    {b w : ι → ℝ} {H : ℝ} {K : ι → ι → ℝ}
    (hw : ∀ r, 0 < w r) (hKsymm : ∀ r s, K r s = K s r) (hKnn : ∀ r s, 0 ≤ K r s)
    (hrow : ∀ r, ∑ s, K r s * w s ≤ H * w r) :
    ∑ r, ∑ s, |b r| * |b s| * K r s ≤ H * ∑ r, (b r) ^ (2 : ℕ) := by
  classical
  -- the weighted arithmetic–geometric step
  have hamgm : ∀ r s : ι, |b r| * |b s| * K r s
      ≤ ((b r) ^ (2 : ℕ) / w r * w s / 2 + (b s) ^ (2 : ℕ) / w s * w r / 2) * K r s := by
    intro r s
    refine mul_le_mul_of_nonneg_right ?_ (hKnn r s)
    have hwr := hw r
    have hws := hw s
    rw [div_mul_eq_mul_div, div_div, div_mul_eq_mul_div, div_div, div_add_div _ _
      (by positivity) (by positivity), le_div_iff₀ (by positivity)]
    have hkey : 0 ≤ (|b r| * w s - |b s| * w r) ^ (2 : ℕ) := sq_nonneg _
    have hexp : (|b r| * w s - |b s| * w r) ^ (2 : ℕ)
        = (b r) ^ (2 : ℕ) * (w s) ^ (2 : ℕ) + (b s) ^ (2 : ℕ) * (w r) ^ (2 : ℕ)
          - 2 * (|b r| * |b s| * (w r * w s)) := by
      rw [sub_sq, mul_pow, mul_pow, sq_abs, sq_abs]
      ring
    nlinarith [hkey, hexp]
  have hbound : ∑ r, ∑ s, |b r| * |b s| * K r s
      ≤ ∑ r, ∑ s, ((b r) ^ (2 : ℕ) / w r * w s / 2 + (b s) ^ (2 : ℕ) / w s * w r / 2) * K r s :=
    Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => hamgm r s
  -- split into two weighted row sums
  have hsplit : ∑ r, ∑ s, ((b r) ^ (2 : ℕ) / w r * w s / 2 + (b s) ^ (2 : ℕ) / w s * w r / 2) * K r s
      = (∑ r, (b r) ^ (2 : ℕ) / w r / 2 * ∑ s, K r s * w s)
        + ∑ r, ∑ s, (b s) ^ (2 : ℕ) / w s / 2 * (K r s * w r) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  have hswap : ∑ r, ∑ s, (b s) ^ (2 : ℕ) / w s / 2 * (K r s * w r)
      = ∑ s, (b s) ^ (2 : ℕ) / w s / 2 * ∑ r, K s r * w r := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hKsymm r s]
  have hhalf : ∀ r : ι, (b r) ^ (2 : ℕ) / w r / 2 * ∑ s, K r s * w s ≤ H / 2 * (b r) ^ (2 : ℕ) := by
    intro r
    have hwr := hw r
    have hcoef : 0 ≤ (b r) ^ (2 : ℕ) / w r / 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left (hrow r) hcoef
    calc (b r) ^ (2 : ℕ) / w r / 2 * ∑ s, K r s * w s ≤ (b r) ^ (2 : ℕ) / w r / 2 * (H * w r) := hmul
      _ = H / 2 * (b r) ^ (2 : ℕ) := by field_simp
  calc ∑ r, ∑ s, |b r| * |b s| * K r s
      ≤ (∑ r, (b r) ^ (2 : ℕ) / w r / 2 * ∑ s, K r s * w s)
        + ∑ r, ∑ s, (b s) ^ (2 : ℕ) / w s / 2 * (K r s * w r) := hsplit ▸ hbound
    _ = (∑ r, (b r) ^ (2 : ℕ) / w r / 2 * ∑ s, K r s * w s)
        + ∑ s, (b s) ^ (2 : ℕ) / w s / 2 * ∑ r, K s r * w r := by rw [hswap]
    _ ≤ (∑ r, H / 2 * (b r) ^ (2 : ℕ)) + ∑ s, H / 2 * (b s) ^ (2 : ℕ) :=
        add_le_add (Finset.sum_le_sum fun r _ => hhalf r) (Finset.sum_le_sum fun s _ => hhalf s)
    _ = H * ∑ r, (b r) ^ (2 : ℕ) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring

end GaloisForLFunctions
