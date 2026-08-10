import GaloisForLFunctions.RHTower.Sieve.ShiftSumBound

/-!
# The sum over shifts, with a shift-uniform increment majorant

`abs_shift_sum_le` consumes a bound on the *maximal* partial correlation sum at each shift, which is
stronger than what the averaged theory supplies.  Rearranging summation by parts so that the sum
over shifts sits inside removes that need:

```text
| ∑_{k ≤ K} ∑_{j < n} w(k,j)·f(j)·f(j+k) |  ≤  V·P ,
```

where `P` bounds `∑_{k ≤ K} |∑_{i < J} f(i)f(i+k)|` for **every** `J ≤ J₀` — one bound, uniform in
the length of the initial segment, not a maximum taken separately at each shift — and `V` bounds
`∑_j sup_k |w(k,j+1) − w(k,j)|`.  The weight must vanish at the right end and have no increments
beyond `J₀`, which confines the partial sums that appear to lengths `≤ J₀`: for the fibre kernel
`J₀ ≍ √x`, exactly the scale at which the averaged theory speaks.

The price is that the weight's increments must be majorised *uniformly in the shift*, rather than
only their total variation at each shift.
-/

namespace RHTower.Sieve

open Finset

/-- Every partial correlation sum of length at most `J₀`, summed over the shifts `1 ≤ k ≤ K`, is at
most `P`. -/
def CorrelationUniformBound (f : ℕ → ℝ) (K J₀ : ℕ) (P : ℝ) : Prop :=
  ∀ J, J ≤ J₀ → ∑ k ∈ Finset.Icc 1 K, |∑ i ∈ Finset.range J, f i * f (i + k)| ≤ P

theorem CorrelationUniformBound.nonneg {f : ℕ → ℝ} {K J₀ : ℕ} {P : ℝ}
    (hP : CorrelationUniformBound f K J₀ P) : 0 ≤ P := by
  have := hP 0 (Nat.zero_le _)
  simpa using this

/-- **The sum over shifts, with the weights stripped uniformly.** -/
theorem abs_shift_sum_uniform_le {f : ℕ → ℝ} {K n J₀ : ℕ} {P V : ℝ}
    (hP : CorrelationUniformBound f K J₀ P)
    {w : ℕ → ℕ → ℝ} {d : ℕ → ℝ} (hd0 : ∀ j, 0 ≤ d j)
    (hd : ∀ k, 1 ≤ k → k ≤ K → ∀ j, |w k (j + 1) - w k j| ≤ d j)
    (hdz : ∀ j, J₀ ≤ j + 1 → d j = 0)
    (hhead : ∀ k, 1 ≤ k → k ≤ K → w k (n - 1) = 0)
    (hV : ∑ j ∈ Finset.range (n - 1), d j ≤ V) :
    |∑ k ∈ Finset.Icc 1 K, ∑ j ∈ Finset.range n, w k j * (f j * f (j + k))|
      ≤ V * P := by
  classical
  have hP0 : (0 : ℝ) ≤ P := hP.nonneg
  set S : ℕ → ℕ → ℝ := fun k J => ∑ i ∈ Finset.range J, f i * f (i + k) with hS
  have hparts : ∀ k, ∑ j ∈ Finset.range n, w k j * (f j * f (j + k))
      = w k (n - 1) * S k n
        - ∑ i ∈ Finset.range (n - 1), (w k (i + 1) - w k i) * S k (i + 1) := by
    intro k
    have := Finset.sum_range_by_parts (w k) (fun j => f j * f (j + k)) n
    simpa only [smul_eq_mul, hS] using this
  rw [Finset.sum_congr rfl fun k _ => hparts k, Finset.sum_sub_distrib]
  -- the head vanishes
  have hheadzero : ∑ k ∈ Finset.Icc 1 K, w k (n - 1) * S k n = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    rw [hhead k hk.1 hk.2, zero_mul]
  rw [hheadzero, zero_sub, abs_neg]
  -- the tail
  rw [Finset.sum_comm]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hrow : ∀ i ∈ Finset.range (n - 1),
      |∑ k ∈ Finset.Icc 1 K, (w k (i + 1) - w k i) * S k (i + 1)| ≤ d i * P := by
    intro i _
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hstep : ∀ k ∈ Finset.Icc 1 K,
        |(w k (i + 1) - w k i) * S k (i + 1)| ≤ d i * |S k (i + 1)| := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hd k hk.1 hk.2 i) (abs_nonneg _)
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.mul_sum]
    rcases le_or_gt (i + 1) J₀ with hle | hgt
    · exact mul_le_mul_of_nonneg_left (hP (i + 1) hle) (hd0 i)
    · have hz : d i = 0 := hdz i (by omega)
      rw [hz, zero_mul, zero_mul]
  refine le_trans (Finset.sum_le_sum hrow) ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right hV hP0

end RHTower.Sieve
