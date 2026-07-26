import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# The sign of the sine on the half-period intervals

The real sine is positive exactly on the even half-periods `(2kπ, (2k+1)π)`, negative exactly on the
odd ones `((2k+1)π, (2k+2)π)`, and zero exactly on `πℤ`.  Mathlib supplies the sign only on the
first half-period together with the reflection `sin (x + nπ) = (-1)ⁿ sin x`; this module turns those
into the global characterisation and records that the sign intervals are pairwise disjoint.

The characterisation is what lets a square wave `sgn (sin x)` be integrated by splitting the line
into the countable disjoint family of half-periods.
-/

open Real Set

namespace GaloisForLFunctions.HTGeometry

theorem neg_one_zpow_two_mul (k : ℤ) : ((-1 : ℝ) ^ (2 * k)) = 1 := by
  rw [zpow_mul]
  norm_num

theorem neg_one_zpow_two_mul_add_one (k : ℤ) : ((-1 : ℝ) ^ (2 * k + 1)) = -1 := by
  rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), neg_one_zpow_two_mul]
  norm_num

/-- Reduction of the sine to its first half-period. -/
theorem sin_eq_zpow_mul_sin_sub (x : ℝ) (n : ℤ) :
    Real.sin x = (-1 : ℝ) ^ n * Real.sin (x - n * π) := by
  have h := Real.sin_add_int_mul_pi (x - n * π) n
  rw [sub_add_cancel] at h
  exact h

/-- On an odd half-period the sine is negative. -/
theorem sin_neg_of_mem_oddInterval {k : ℤ} {x : ℝ}
    (h : x ∈ Ioo ((2 * (k : ℝ) + 1) * π) ((2 * (k : ℝ) + 2) * π)) : Real.sin x < 0 := by
  obtain ⟨h1, h2⟩ := h
  have hshift : 0 < x - (2 * k + 1) * π := by linarith
  have hshift' : x - (2 * (k : ℝ) + 1) * π < π := by nlinarith [Real.pi_pos]
  have hpos : 0 < Real.sin (x - (2 * (k : ℝ) + 1) * π) :=
    Real.sin_pos_of_pos_of_lt_pi hshift hshift'
  have hcast : ((2 * k + 1 : ℤ) : ℝ) = 2 * (k : ℝ) + 1 := by push_cast; ring
  have hval := sin_eq_zpow_mul_sin_sub x (2 * k + 1)
  rw [hcast, neg_one_zpow_two_mul_add_one] at hval
  rw [hval]
  linarith

/-- On an even half-period the sine is positive. -/
theorem sin_pos_of_mem_evenInterval {k : ℤ} {x : ℝ}
    (h : x ∈ Ioo ((2 * (k : ℝ)) * π) ((2 * (k : ℝ) + 1) * π)) : 0 < Real.sin x := by
  obtain ⟨h1, h2⟩ := h
  have hshift : 0 < x - 2 * (k : ℝ) * π := by linarith
  have hshift' : x - 2 * (k : ℝ) * π < π := by nlinarith [Real.pi_pos]
  have hpos : 0 < Real.sin (x - 2 * (k : ℝ) * π) :=
    Real.sin_pos_of_pos_of_lt_pi hshift hshift'
  have hcast : ((2 * k : ℤ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
  have hval := sin_eq_zpow_mul_sin_sub x (2 * k)
  rw [hcast, neg_one_zpow_two_mul] at hval
  rw [hval]
  linarith

/-- Every real lies in a closed half-period determined by the floor of `x/π`. -/
theorem exists_int_mem_halfPeriod (x : ℝ) :
    ∃ m : ℤ, (m : ℝ) * π ≤ x ∧ x < ((m : ℝ) + 1) * π := by
  refine ⟨⌊x / π⌋, ?_, ?_⟩
  · have h := Int.floor_le (x / π)
    rw [le_div_iff₀ Real.pi_pos] at h
    linarith
  · have h := Int.lt_floor_add_one (x / π)
    rw [div_lt_iff₀ Real.pi_pos] at h
    linarith

/-- **Global sign characterisation.**  The sine is negative exactly on the odd half-periods. -/
theorem sin_neg_iff (x : ℝ) :
    Real.sin x < 0 ↔ ∃ k : ℤ, x ∈ Ioo ((2 * (k : ℝ) + 1) * π) ((2 * (k : ℝ) + 2) * π) := by
  constructor
  · intro hneg
    obtain ⟨m, hm1, hm2⟩ := exists_int_mem_halfPeriod x
    have hne : x ≠ (m : ℝ) * π := by
      intro hx
      have : Real.sin x = 0 := by
        rw [hx]
        exact Real.sin_int_mul_pi m
      linarith
    have hlt : (m : ℝ) * π < x := lt_of_le_of_ne hm1 (Ne.symm hne)
    have hshift : 0 < x - (m : ℝ) * π := by linarith
    have hshift' : x - (m : ℝ) * π < π := by nlinarith [Real.pi_pos]
    have hpos : 0 < Real.sin (x - (m : ℝ) * π) :=
      Real.sin_pos_of_pos_of_lt_pi hshift hshift'
    have hval := sin_eq_zpow_mul_sin_sub x m
    rcases Int.even_or_odd m with hev | hod
    · exfalso
      obtain ⟨j, hj⟩ := hev
      have hcast : ((-1 : ℝ) ^ m) = 1 := by
        rw [show m = 2 * j by omega]
        exact neg_one_zpow_two_mul j
      rw [hcast, one_mul] at hval
      linarith
    · obtain ⟨j, hj⟩ := hod
      refine ⟨j, ?_, ?_⟩
      · have : (m : ℝ) = 2 * (j : ℝ) + 1 := by exact_mod_cast congrArg (Int.cast : ℤ → ℝ) hj
        linarith [hlt, this ▸ hlt]
      · have hmj : (m : ℝ) = 2 * (j : ℝ) + 1 := by
          exact_mod_cast congrArg (Int.cast : ℤ → ℝ) hj
        have : x < ((m : ℝ) + 1) * π := hm2
        rw [hmj] at this
        linarith [this]
  · rintro ⟨k, hk⟩
    exact sin_neg_of_mem_oddInterval hk

/-- The odd half-periods are pairwise disjoint. -/
theorem pairwise_disjoint_oddInterval :
    Pairwise (Function.onFun Disjoint
      (fun k : ℤ => Ioo ((2 * (k : ℝ) + 1) * π) ((2 * (k : ℝ) + 2) * π))) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  rintro x ⟨hi1, hi2⟩ ⟨hj1, hj2⟩
  have hpi := Real.pi_pos
  rcases lt_or_gt_of_ne hij with h | h
  · have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h
    nlinarith
  · have hij' : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast h
    nlinarith

/-- An odd half-period meeting `[1,∞)` has nonnegative index. -/
theorem zero_le_of_oddInterval_mem_Ici {k : ℤ} {x : ℝ} (hx : 1 ≤ x)
    (h : x ∈ Ioo ((2 * (k : ℝ) + 1) * π) ((2 * (k : ℝ) + 2) * π)) : 0 ≤ k := by
  by_contra hk
  have hk1 : k ≤ -1 := by omega
  have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast hk1
  have hpi := Real.pi_pos
  have hup : (2 * (k : ℝ) + 2) * π ≤ 0 := by nlinarith
  linarith [h.2, hx]

end GaloisForLFunctions.HTGeometry
