/-
Abel summation with a power-bounded partial sum.

This is the analytic core of the shift-average transfer.  In the transfer one must bound the tail
`∑_{h₀ < h ≤ M} Δ(h)/h` of a shift average from a bound on its partial sums `S(t) = ∑_{h ≤ t} Δ(h)`.
Summation by parts converts the weighted sum into the partial sums against the increments of the
weight `1/h`, and a bound `|S(n)| ≤ B·n^a` then gives

  `|∑_{i < n} f i / (i+1)| ≤ B·(n^{a-1} + ∑_{j=1}^{n-1} j^{a-2})`.

For `a < 1` the finite sum on the right is bounded independently of `n`, which is what makes the
tail range contribute the same exponent as the head range in the transfer.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.PSeries

open Finset

namespace HTGeometry

/-- Partial sums of `f`. -/
noncomputable def partialSum (f : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range n, f i

@[simp] theorem partialSum_zero (f : ℕ → ℝ) : partialSum f 0 = 0 := by
  simp [partialSum]

theorem partialSum_succ_sub (f : ℕ → ℝ) (i : ℕ) :
    partialSum f (i + 1) - partialSum f i = f i := by
  simp [partialSum, Finset.sum_range_succ]

/-- **Summation by parts, in the form the transfer needs.**  With `w` any weight,

  `∑_{i < n} f i · w i = S n · w (n-1) + ∑_{j=1}^{n-1} S j · (w (j-1) - w j)`,

where `S = partialSum f`.  Stated with the index shift already performed. -/
theorem sum_mul_weight_eq (f w : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range n, f i * w i
      = partialSum f n * w n - ∑ j ∈ range n, partialSum f (j + 1) * (w (j + 1) - w j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have hf : f n = partialSum f (n + 1) - partialSum f n := (partialSum_succ_sub f n).symm
    rw [hf]
    ring

/-- **Abel bound with a power-bounded partial sum.**  If `|S j| ≤ B · j^a` for all `j ≤ n`, and the
weight is `w j = 1/(j+1)` (so `w j - w (j+1) = 1/((j+1)(j+2)) ≥ 0`), then the weighted sum is
controlled by the boundary term plus the increments. -/
theorem abel_bound_of_partialSum_le
    {f : ℕ → ℝ} {B a : ℝ}
    (hS : ∀ j : ℕ, |partialSum f j| ≤ B * (j : ℝ) ^ a) (n : ℕ) :
    |∑ i ∈ range n, f i * (1 / ((i : ℝ) + 1))|
      ≤ B * (n : ℝ) ^ a * (1 / ((n : ℝ) + 1))
        + ∑ j ∈ range n, B * ((j : ℝ) + 1) ^ a * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) := by
  set w : ℕ → ℝ := fun i => 1 / ((i : ℝ) + 1) with hw
  have hkey := sum_mul_weight_eq f w n
  have hstep : ∀ j : ℕ, w (j + 1) - w j = -(1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) := by
    intro j
    have h1 : ((j : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((j : ℝ) + 1 + 1) ≠ 0 := by positivity
    simp only [hw, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  have habs1 : |partialSum f n * w n - ∑ j ∈ range n, partialSum f (j + 1) * (w (j + 1) - w j)|
      ≤ |partialSum f n * w n| + |∑ j ∈ range n, partialSum f (j + 1) * (w (j + 1) - w j)| :=
    abs_sub _ _
  have habs2 : |∑ j ∈ range n, partialSum f (j + 1) * (w (j + 1) - w j)|
      ≤ ∑ j ∈ range n, |partialSum f (j + 1)| * |w (j + 1) - w j| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun j _ => abs_mul _ _
  have hbd1 : |partialSum f n * w n| ≤ B * (n : ℝ) ^ a * (1 / ((n : ℝ) + 1)) := by
    rw [abs_mul]
    have hwn : |w n| = 1 / ((n : ℝ) + 1) := by
      simp only [hw]; exact abs_of_nonneg (by positivity)
    rw [hwn]
    exact mul_le_mul_of_nonneg_right (hS n) (by positivity)
  have hbd2 : ∀ j ∈ range n, |partialSum f (j + 1)| * |w (j + 1) - w j|
      ≤ B * ((j : ℝ) + 1) ^ a * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) := by
    intro j _
    rw [hstep j, abs_neg,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)))]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have h := hS (j + 1)
    push_cast at h
    exact h
  calc |∑ i ∈ range n, f i * (1 / ((i : ℝ) + 1))|
      = |partialSum f n * w n - ∑ j ∈ range n, partialSum f (j + 1) * (w (j + 1) - w j)| := by
        rw [← hkey]
    _ ≤ |partialSum f n * w n| + |∑ j ∈ range n, partialSum f (j + 1) * (w (j + 1) - w j)| := habs1
    _ ≤ B * (n : ℝ) ^ a * (1 / ((n : ℝ) + 1))
          + ∑ j ∈ range n, |partialSum f (j + 1)| * |w (j + 1) - w j| :=
        add_le_add hbd1 habs2
    _ ≤ B * (n : ℝ) ^ a * (1 / ((n : ℝ) + 1))
          + ∑ j ∈ range n, B * ((j : ℝ) + 1) ^ a * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2))) :=
        add_le_add le_rfl (Finset.sum_le_sum hbd2)


/-- The increment weight is dominated by `(j+1)^{a-2}`. -/
theorem increment_le_rpow {a : ℝ} (j : ℕ) :
    ((j : ℝ) + 1) ^ a * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)))
      ≤ ((j : ℝ) + 1) ^ (a - 2) := by
  have h1 : (0:ℝ) < (j : ℝ) + 1 := by positivity
  have h2 : ((j : ℝ) + 1) ^ (a - 2) = ((j : ℝ) + 1) ^ a * ((j : ℝ) + 1) ^ (-2 : ℝ) := by
    rw [← Real.rpow_add h1]; ring_nf
  rw [h2]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h3 : ((j : ℝ) + 1) ^ (-2 : ℝ) = 1 / (((j : ℝ) + 1) * ((j : ℝ) + 1)) := by
    rw [Real.rpow_neg h1.le]
    norm_num
    rw [sq, mul_inv]
  rw [h3]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith [h1]

/-- **The tail is summable for `a < 1`.**  This is what makes the tail range of the transfer
contribute the same exponent as the head range: the increment sum is bounded independently of the
truncation point. -/
theorem summable_increment {a : ℝ} (ha : a < 1) :
    Summable (fun j : ℕ => ((j : ℝ) + 1) ^ a * (1 / (((j : ℝ) + 1) * ((j : ℝ) + 2)))) := by
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => increment_le_rpow j) ?_
  have h : ∀ j : ℕ, ((j : ℝ) + 1) ^ (a - 2) = (1 : ℝ) / ((j : ℝ) + 1) ^ (2 - a) := by
    intro j
    have h1 : (0:ℝ) < (j : ℝ) + 1 := by positivity
    rw [eq_div_iff (by positivity), ← Real.rpow_add h1]
    norm_num
  simp only [h]
  have hp : (1:ℝ) < 2 - a := by linarith
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ (2 - a)) :=
    Real.summable_one_div_nat_rpow.mpr hp
  refine Summable.congr ((summable_nat_add_iff 1).mpr hsum) (fun j => ?_)
  push_cast
  ring_nf

end HTGeometry
