import GaloisForLFunctions.RHTower.Sieve.PrimeProfilePartitionSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The step sum of a Lipschitz profile against `dt/t`

The exponent cells `[j/m, (j+1)/m]` carry the weights

`∫_{j/m}^{(j+1)/m} dt/t = log ((j+1)/j)`,

which are exactly the limits of the prime-window reciprocal masses.  Comparing the step sum
`Σ_{j=1}^{m-1} g(j/m) · log ((j+1)/j)` with `∫_{1/m}^{1} g(t) dt/t` therefore costs only the
Lipschitz oscillation on one cell, times the total weight:

`|Σ_j g(j/m) log ((j+1)/j) − ∫_{1/m}^(1 : ℕ) g(t) dt/t| ≤ (L/m) · log m`.

No Riemann-sum theory is used: the weights *are* the cell integrals, so the comparison is one
pointwise Lipschitz estimate integrated cell by cell.
-/

namespace RHTower.Sieve

open Finset intervalIntegral MeasureTheory
open scoped Topology

noncomputable section

/-! ## Integrability on a cell -/

theorem intervalIntegrable_div_id {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => g t / t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div hg.continuousOn continuousOn_id
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  exact ne_of_gt (lt_of_lt_of_le ha hx.1)

theorem intervalIntegrable_one_div_id {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (1 : ℝ) / t) volume a b :=
  intervalIntegrable_div_id continuous_const ha hab

/-! ## The cell weight -/

theorem cellLeft_pos {m j : ℕ} (hm : 1 ≤ m) (hj : 1 ≤ j) : (0 : ℝ) < (j : ℝ) / m := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  positivity

theorem cellLeft_le_right {m j : ℕ} (hm : 1 ≤ m) : (j : ℝ) / m ≤ ((j : ℝ) + 1) / m := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  gcongr
  linarith

/-- **The cell weight is the logarithmic increment.** -/
theorem integral_one_div_cell {m j : ℕ} (hm : 1 ≤ m) (hj : 1 ≤ j) :
    (∫ t in ((j : ℝ) / m)..(((j : ℝ) + 1) / m), (1 : ℝ) / t)
      = Real.log ((j : ℝ) + 1) - Real.log j := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hleft := cellLeft_pos hm hj
  have hle := cellLeft_le_right (m := m) (j := j) hm
  have hnotmem : (0 : ℝ) ∉ Set.uIcc ((j : ℝ) / m) (((j : ℝ) + 1) / m) := by
    rw [Set.uIcc_of_le hle]
    intro hmem
    exact absurd hmem.1 (not_le.mpr hleft)
  rw [integral_one_div hnotmem]
  rw [show (((j : ℝ) + 1) / m) / ((j : ℝ) / m) = ((j : ℝ) + 1) / (j : ℝ) from by
    field_simp]
  rw [Real.log_div (by linarith) (ne_of_gt hjpos)]

/-! ## Cellwise comparison -/

theorem abs_integral_cell_sub_step_le {g : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hg : Continuous g) (hlip : ∀ s t : ℝ, |g s - g t| ≤ L * |s - t|)
    {m j : ℕ} (hm : 1 ≤ m) (hj : 1 ≤ j) :
    |(∫ t in ((j : ℝ) / m)..(((j : ℝ) + 1) / m), g t / t)
        - g ((j : ℝ) / m) * (Real.log ((j : ℝ) + 1) - Real.log j)|
      ≤ L / m * (Real.log ((j : ℝ) + 1) - Real.log j) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hleft := cellLeft_pos hm hj
  have hle := cellLeft_le_right (m := m) (j := j) hm
  set a : ℝ := (j : ℝ) / m with ha
  set b : ℝ := ((j : ℝ) + 1) / m with hb
  have hint1 : IntervalIntegrable (fun t => g t / t) volume a b :=
    intervalIntegrable_div_id hg hleft hle
  have hint2 : IntervalIntegrable (fun t => g a * ((1 : ℝ) / t)) volume a b :=
    (intervalIntegrable_one_div_id hleft hle).const_mul _
  have hweight : (∫ t in a..b, (1 : ℝ) / t) = Real.log ((j : ℝ) + 1) - Real.log j :=
    integral_one_div_cell hm hj
  have hstep : g a * (Real.log ((j : ℝ) + 1) - Real.log j)
      = ∫ t in a..b, g a * ((1 : ℝ) / t) := by
    rw [intervalIntegral.integral_const_mul, hweight]
  rw [hstep, ← intervalIntegral.integral_sub hint1 hint2]
  have hbound : |∫ t in a..b, (g t / t - g a * ((1 : ℝ) / t))|
      ≤ ∫ t in a..b, L / m * ((1 : ℝ) / t) := by
    have hsub : IntervalIntegrable (fun t => g t / t - g a * ((1 : ℝ) / t)) volume a b :=
      hint1.sub hint2
    have habs : IntervalIntegrable (fun t => |g t / t - g a * ((1 : ℝ) / t)|) volume a b :=
      hsub.abs
    have hmaj : IntervalIntegrable (fun t => L / m * ((1 : ℝ) / t)) volume a b :=
      (intervalIntegrable_one_div_id hleft hle).const_mul _
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs hle) ?_
    refine intervalIntegral.integral_mono_on hle habs hmaj ?_
    intro t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le hleft ht.1
    have hcell : |t - a| ≤ 1 / m := by
      rw [abs_of_nonneg (by linarith [ht.1])]
      have hgap : b - a = 1 / m := by rw [ha, hb]; field_simp; ring
      linarith [ht.2]
    have hlipt : |g t - g a| ≤ L / m := by
      refine le_trans (hlip t a) ?_
      calc L * |t - a| ≤ L * (1 / m) := mul_le_mul_of_nonneg_left hcell hL
        _ = L / m := by ring
    have hrw : g t / t - g a * ((1 : ℝ) / t) = (g t - g a) / t := by
      field_simp
    rw [hrw, abs_div, abs_of_pos htpos, mul_one_div]
    gcongr
  refine le_trans hbound ?_
  rw [intervalIntegral.integral_const_mul, hweight]

/-! ## The full comparison -/

theorem sum_Ico_log_increment {m : ℕ} (hm : 1 ≤ m) :
    ∑ j ∈ Finset.Ico 1 m, (Real.log ((j : ℝ) + 1) - Real.log j) = Real.log m := by
  have hcong : ∀ j ∈ Finset.Ico 1 m,
      (Real.log ((j : ℝ) + 1) - Real.log j)
        = (fun i : ℕ => Real.log i) (j + 1) - (fun i : ℕ => Real.log i) j := by
    intro j _
    have hc : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    simp only [hc]
  rw [Finset.sum_congr rfl hcong, sum_Ico_telescope (fun i : ℕ => Real.log i) hm]
  simp

/-- **The step sum is the integral, up to `(L/m)·log m`.** -/
theorem abs_stepSum_sub_integral_le {g : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hg : Continuous g) (hlip : ∀ s t : ℝ, |g s - g t| ≤ L * |s - t|)
    {m : ℕ} (hm : 1 ≤ m) :
    |∑ j ∈ Finset.Ico 1 m, g ((j : ℝ) / m) * (Real.log ((j : ℝ) + 1) - Real.log j)
        - ∫ t in (1 / (m : ℝ))..1, g t / t|
      ≤ L / m * Real.log m := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set A : ℕ → ℝ := fun k => ((k : ℝ) + 1) / m with hA
  have hAint : ∀ k < m - 1, IntervalIntegrable (fun t => g t / t) volume (A k) (A (k + 1)) := by
    intro k _
    have hleft : (0 : ℝ) < A k := by
      rw [hA]
      have : (0 : ℝ) ≤ (k : ℝ) := by positivity
      positivity
    have hle : A k ≤ A (k + 1) := by
      rw [hA]
      push_cast
      gcongr
      linarith
    exact intervalIntegrable_div_id hg hleft hle
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (n := m - 1) hAint
  have hA0 : A 0 = 1 / (m : ℝ) := by rw [hA]; push_cast; ring
  have hAm : A (m - 1) = 1 := by
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ m := hm
      push_cast [Nat.cast_sub h1]
      ring
    simp only [hA]
    rw [hcast]
    field_simp
    ring
  rw [hA0, hAm] at hsplit
  have hreindex : ∑ j ∈ Finset.Ico 1 m,
      (g ((j : ℝ) / m) * (Real.log ((j : ℝ) + 1) - Real.log j)) =
      ∑ k ∈ Finset.range (m - 1),
        (g (((k : ℝ) + 1) / m) * (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1))) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro k _
    have hc : ((1 + k : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hc, show ((k : ℝ) + 1 + 1) = (k : ℝ) + 2 from by ring]
  have hcellint : ∑ k ∈ Finset.range (m - 1), (∫ t in (A k)..(A (k + 1)), g t / t)
      = ∫ t in (1 / (m : ℝ))..1, g t / t := hsplit
  rw [hreindex, ← hcellint, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ k ∈ Finset.range (m - 1),
      |g (((k : ℝ) + 1) / m) * (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1))
          - ∫ t in (A k)..(A (k + 1)), g t / t|
        ≤ L / m * (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)) := by
    intro k _
    have hj : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
    have hcast1 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    have hAk : A k = ((k + 1 : ℕ) : ℝ) / m := by rw [hA, hcast1]
    have hAk1 : A (k + 1) = (((k + 1 : ℕ) : ℝ) + 1) / m := by
      rw [hA, hcast1]
      push_cast
      ring
    have hbase := abs_integral_cell_sub_step_le hL hg hlip (m := m) (j := k + 1) hm hj
    rw [← hAk, ← hAk1, hcast1] at hbase
    rw [show Real.log ((k : ℝ) + 2) = Real.log (((k : ℝ) + 1) + 1) from by ring_nf]
    rw [abs_sub_comm]
    exact hbase
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsum : ∑ k ∈ Finset.range (m - 1),
      (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)) = Real.log m := by
    rw [← sum_Ico_log_increment hm, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro k _
    have hc : ((1 + k : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hc, show ((k : ℝ) + 1 + 1) = (k : ℝ) + 2 from by ring]
  rw [hsum]

end

end RHTower.Sieve
