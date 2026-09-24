import Mathlib.Tactic

/-!
# Two-scale recovery of a removed zero Fourier mode

The low-frequency Route-L window has a scale-dependent constant Fourier mode.
If its removal leaves a controlled centered window at two overlapping dyadic
scales, the difference of the two means is controlled by the centered energies.
A summable geometric bound on those differences and a zero limit at infinity
then recover the mean itself.  These are finite-dimensional analytic lemmas;
the arithmetic estimate for the remaining nonzero low modes is separate.
-/

open Finset
open scoped BigOperators

namespace RHTower

/-- Two centered least-square fits on one finite set control their slope difference. -/
theorem centered_slope_difference_energy
    (s : Finset ℕ) (u : ℕ → ℝ) (a b : ℝ) :
    (a - b) ^ (2 : ℕ) * (∑ m ∈ s, (m : ℝ) ^ (2 : ℕ)) ≤
      2 * (∑ m ∈ s, (u m - (m : ℝ) * a) ^ (2 : ℕ)) +
      2 * (∑ m ∈ s, (u m - (m : ℝ) * b) ^ (2 : ℕ)) := by
  calc
    (a - b) ^ (2 : ℕ) * (∑ m ∈ s, (m : ℝ) ^ (2 : ℕ)) =
        ∑ m ∈ s, ((m : ℝ) * (a - b)) ^ (2 : ℕ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          ring
    _ ≤ ∑ m ∈ s, (2 * (u m - (m : ℝ) * a) ^ (2 : ℕ) +
        2 * (u m - (m : ℝ) * b) ^ (2 : ℕ)) := by
          apply Finset.sum_le_sum
          intro m hm
          nlinarith [sq_nonneg ((u m - (m : ℝ) * a) +
            (u m - (m : ℝ) * b))]
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The dyadic overlap has cubic second moment. -/
theorem lower_overlap_square_sum (L : ℕ) :
    (L : ℝ) ^ (3 : ℕ) ≤
      ∑ m ∈ Finset.Ioc L (2 * L), (m : ℝ) ^ (2 : ℕ) := by
  have hcard : (Finset.Ioc L (2 * L)).card = L := by
    simp
    omega
  calc
    (L : ℝ) ^ (3 : ℕ) = ∑ _m ∈ Finset.Ioc L (2 * L), (L : ℝ) ^ (2 : ℕ) := by
      simp [hcard]
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro m hm
      have hL : L < m := (Finset.mem_Ioc.mp hm).1
      have hLr : (L : ℝ) ≤ (m : ℝ) := by exact_mod_cast hL.le
      nlinarith

/-- Centered energies on one dyadic overlap bound the difference of its slopes. -/
theorem overlap_slope_difference_energy
    (L : ℕ) (u : ℕ → ℝ) (a b : ℝ) :
    (L : ℝ) ^ (3 : ℕ) * (a - b) ^ (2 : ℕ) ≤
      2 * (∑ m ∈ Finset.Ioc L (2 * L),
        (u m - (m : ℝ) * a) ^ (2 : ℕ)) +
      2 * (∑ m ∈ Finset.Ioc L (2 * L),
        (u m - (m : ℝ) * b) ^ (2 : ℕ)) := by
  have hbase := centered_slope_difference_energy (Finset.Ioc L (2 * L)) u a b
  have hlow := lower_overlap_square_sum L
  calc
    (L : ℝ) ^ (3 : ℕ) * (a - b) ^ (2 : ℕ) =
        (a - b) ^ (2 : ℕ) * (L : ℝ) ^ (3 : ℕ) := by ring
    _ ≤ (a - b) ^ (2 : ℕ) *
        (∑ m ∈ Finset.Ioc L (2 * L), (m : ℝ) ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hlow (sq_nonneg _)
    _ ≤ _ := hbase

/-- A convergent sequence whose consecutive changes obey a geometric budget has its
initial value bounded by the full budget. -/
theorem dyadic_slope_telescope
    (a : ℕ → ℝ) (r C : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (hC : 0 ≤ C)
    (hstep : ∀ n, |a n - a (n + 1)| ≤ C * r ^ n)
    (hlim : Filter.Tendsto a Filter.atTop (nhds (0 : ℝ))) :
    |a 0| ≤ C / (1 - r) := by
  have hgeom : ∀ n : ℕ, (1 - r) * (∑ k ∈ Finset.range n, r ^ k) = 1 - r ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        (1 - r) * ((∑ k ∈ Finset.range n, r ^ k) + r ^ n) =
            (1 - r) * (∑ k ∈ Finset.range n, r ^ k) + (1 - r) * r ^ n := by ring
        _ = 1 - r ^ n + (1 - r) * r ^ n := by rw [ih]
        _ = 1 - r ^ (n + 1) := by rw [pow_succ]; ring
  have hsum (n : ℕ) : (∑ k ∈ Finset.range n, r ^ k) ≤ 1 / (1 - r) := by
    have hrpow : 0 ≤ r ^ n := pow_nonneg hr0 _
    have hmul : (1 - r) * (∑ k ∈ Finset.range n, r ^ k) ≤ 1 := by
      linarith [hgeom n]
    apply (le_div_iff₀ (sub_pos.mpr hr1)).2
    nlinarith
  have hpartial : ∀ n : ℕ,
      |a 0| ≤ C * (∑ k ∈ Finset.range n, r ^ k) + |a n| := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have htri : |a n| ≤ |a n - a (n + 1)| + |a (n + 1)| := by
        calc
          |a n| = |(a n - a (n + 1)) + a (n + 1)| := by rw [sub_add_cancel]
          _ ≤ _ := abs_add_le _ _
      calc
        |a 0| ≤ C * (∑ k ∈ Finset.range n, r ^ k) + |a n| := ih
        _ ≤ C * (∑ k ∈ Finset.range n, r ^ k) +
            |a n - a (n + 1)| + |a (n + 1)| := by linarith
        _ ≤ C * ((∑ k ∈ Finset.range n, r ^ k) + r ^ n) +
            |a (n + 1)| := by linarith [hstep n]
        _ = C * (∑ k ∈ Finset.range (n + 1), r ^ k) + |a (n + 1)| := by
          rw [Finset.sum_range_succ]
  have hbound (n : ℕ) : |a 0| ≤ C / (1 - r) + |a n| := by
    have h := hpartial n
    have hs := mul_le_mul_of_nonneg_left (hsum n) hC
    have hs' : C * (∑ k ∈ Finset.range n, r ^ k) ≤ C / (1 - r) := by
      simpa [div_eq_mul_inv] using hs
    linarith
  have hlimabs : Filter.Tendsto (fun n => |a n|) Filter.atTop (nhds (0 : ℝ)) := by
    simpa using hlim.abs
  by_contra hnot
  have hδ : 0 < |a 0| - C / (1 - r) := sub_pos.mpr (lt_of_not_ge hnot)
  have hev : ∀ᶠ n : ℕ in Filter.atTop, |a n| < |a 0| - C / (1 - r) :=
    hlimabs.eventually (gt_mem_nhds hδ)
  obtain ⟨n, hn⟩ := hev.exists
  linarith [hbound n]

end RHTower
