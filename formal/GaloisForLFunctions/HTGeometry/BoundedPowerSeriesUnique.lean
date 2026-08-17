import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A bounded power series vanishing near zero has vanishing coefficients

A power series with bounded coefficients converges on the open unit interval.  If it vanishes
identically on a neighbourhood of zero, every coefficient vanishes: peel the first `m` coefficients,
which are zero by induction, divide by `t^m`, and let `t` tend to zero — the remaining tail is
bounded by `C|t|/(1-|t|)`.

No analyticity machinery is needed, only the geometric tail bound.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- A power series with bounded coefficients is summable inside the unit interval. -/
theorem summable_of_bounded_coeff {c : ℕ → ℝ} {C t : ℝ}
    (hbound : ∀ n, |c n| ≤ C) (ht : |t| < 1) :
    Summable fun n => c n * t ^ n := by
  refine Summable.of_norm_bounded (g := fun n => C * |t| ^ n) ?_ ?_
  · exact (summable_geometric_of_lt_one (abs_nonneg t) ht).mul_left C
  · intro n
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_right (hbound n) (by positivity)

/-- The tail of the shifted series is bounded by the geometric tail. -/
theorem abs_tsum_shift_tail_le {c : ℕ → ℝ} {C t : ℝ}
    (hbound : ∀ n, |c n| ≤ C) (ht : |t| < 1) (m : ℕ) :
    |∑' n : ℕ, c (n + 1 + m) * t ^ (n + 1)| ≤ C * |t| / (1 - |t|) := by
  have ht0 : (0 : ℝ) ≤ |t| := abs_nonneg t
  have h1t : (0 : ℝ) < 1 - |t| := by linarith
  have hgeom : Summable fun n : ℕ => C * |t| ^ (n + 1) := by
    have := (summable_geometric_of_lt_one ht0 ht).mul_left (C * |t|)
    refine this.congr fun n => ?_
    rw [pow_succ]
    ring
  have hsum : Summable fun n : ℕ => c (n + 1 + m) * t ^ (n + 1) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ => C * |t| ^ (n + 1)) hgeom ?_
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_right (hbound _) (by positivity)
  calc |∑' n : ℕ, c (n + 1 + m) * t ^ (n + 1)|
      ≤ ∑' n : ℕ, |c (n + 1 + m) * t ^ (n + 1)| := by
        have h := norm_tsum_le_tsum_norm (f := fun n : ℕ => c (n + 1 + m) * t ^ (n + 1))
          (by simpa [Real.norm_eq_abs] using hsum.abs)
        simpa [Real.norm_eq_abs] using h
    _ ≤ ∑' n : ℕ, C * |t| ^ (n + 1) := by
        refine hsum.abs.tsum_le_tsum ?_ hgeom
        intro n
        rw [abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_right (hbound _) (by positivity)
    _ = C * |t| / (1 - |t|) := by
        have hval : ∑' n : ℕ, C * |t| ^ (n + 1) = C * |t| * ∑' n : ℕ, |t| ^ n := by
          rw [← tsum_mul_left]
          refine tsum_congr fun n => ?_
          rw [pow_succ]
          ring
        rw [hval, tsum_geometric_of_lt_one ht0 ht]
        field_simp

/-- **Uniqueness of the coefficients.**  A power series with bounded coefficients that vanishes on
a neighbourhood of zero has all coefficients zero. -/
theorem coeff_eq_zero_of_tsum_eq_zero {c : ℕ → ℝ} {C r : ℝ} (hC : 0 ≤ C) (hr : 0 < r) (hr1 : r ≤ 1)
    (hbound : ∀ n, |c n| ≤ C)
    (hzero : ∀ t : ℝ, 0 < |t| → |t| < r → ∑' n : ℕ, c n * t ^ n = 0) :
    ∀ n, c n = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    -- the shifted series vanishes for every small nonzero parameter
    have hshift : ∀ t : ℝ, 0 < |t| → |t| < r → ∑' n : ℕ, c (n + m) * t ^ n = 0 := by
      intro t ht0 htr
      have ht1 : |t| < 1 := lt_of_lt_of_le htr hr1
      have hsum := summable_of_bounded_coeff hbound ht1
      have hsplit := hsum.sum_add_tsum_nat_add m
      have hzeros : ∑ n ∈ Finset.range m, c n * t ^ n = 0 := by
        refine Finset.sum_eq_zero fun n hn => ?_
        rw [ih n (Finset.mem_range.mp hn), zero_mul]
      rw [hzeros, zero_add, hzero t ht0 htr] at hsplit
      have htail : ∑' n : ℕ, c (n + m) * t ^ (n + m) = 0 := hsplit
      have hfactor : ∑' n : ℕ, c (n + m) * t ^ (n + m)
          = t ^ m * ∑' n : ℕ, c (n + m) * t ^ n := by
        rw [← tsum_mul_left]
        refine tsum_congr fun n => ?_
        rw [pow_add]
        ring
      rw [hfactor] at htail
      have htne : t ^ m ≠ 0 := pow_ne_zero m (by
        intro h
        rw [h] at ht0
        simp at ht0)
      exact (mul_eq_zero.mp htail).resolve_left htne
    -- the head is the tail, which is small
    have hbnd : ∀ t : ℝ, 0 < |t| → |t| < r → |c m| ≤ C * |t| / (1 - |t|) := by
      intro t ht0 htr
      have ht1 : |t| < 1 := lt_of_lt_of_le htr hr1
      have hsum : Summable fun n : ℕ => c (n + m) * t ^ n := by
        refine Summable.of_norm_bounded (g := fun n : ℕ => C * |t| ^ n)
          ((summable_geometric_of_lt_one (abs_nonneg t) ht1).mul_left C) ?_
        intro n
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_right (hbound _) (by positivity)
      have hpeel := hsum.sum_add_tsum_nat_add 1
      rw [hshift t ht0 htr] at hpeel
      have hhead : ∑ n ∈ Finset.range 1, c (n + m) * t ^ n = c m := by
        simp
      rw [hhead] at hpeel
      have hval : c m = -∑' n : ℕ, c (n + 1 + m) * t ^ (n + 1) := by
        have hcongr : ∑' n : ℕ, c (n + 1 + m) * t ^ (n + 1)
            = ∑' n : ℕ, c (n + 1 + m) * t ^ (n + 1) := rfl
        linarith [hpeel]
      rw [hval, abs_neg]
      exact abs_tsum_shift_tail_le hbound ht1 m
    -- let the parameter tend to zero
    by_contra hne
    have hpos : 0 < |c m| := abs_pos.mpr hne
    set t : ℝ := min (min (r / 2) (|c m| / (2 * (C + 1)))) (1 / 4) with hT
    have ht1 : t ≤ r / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    have ht2 : t ≤ |c m| / (2 * (C + 1)) := le_trans (min_le_left _ _) (min_le_right _ _)
    have ht3 : t ≤ 1 / 4 := min_le_right _ _
    have htpos : 0 < t := by
      rw [hT]
      refine lt_min (lt_min (by linarith) ?_) (by norm_num)
      positivity
    have htabs : |t| = t := abs_of_pos htpos
    have htr : |t| < r := by rw [htabs]; linarith
    have hden : (0 : ℝ) < 1 - t := by linarith
    have hCt : C * t ≤ |c m| / 2 := by
      have h1 : C * t ≤ C * (|c m| / (2 * (C + 1))) := mul_le_mul_of_nonneg_left ht2 hC
      have h2 : C * (|c m| / (2 * (C + 1))) ≤ |c m| / 2 := by
        rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
        nlinarith [hpos]
      linarith
    have hfinal := hbnd t (by rw [htabs]; exact htpos) htr
    rw [htabs, le_div_iff₀ hden] at hfinal
    nlinarith [hpos, hCt, ht3, hden]

end GaloisForLFunctions.HTGeometry
