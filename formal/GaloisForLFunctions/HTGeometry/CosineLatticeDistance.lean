import Mathlib

/-!
# A cosine near one puts the angle near the lattice

`1 − cos θ = 2 sin²(θ/2)`, and on `[0, π/2]` the sine is at least `2/π` times its argument, so a
small value of `1 − cos θ` forces `θ` to be within `π√(c/2)` of `2πℤ`.  This is the bridge between the
Fejér kernel's smallness criterion, which is stated through the cosine, and the location of its peaks
on the dual lattice.
-/

open Real

namespace GaloisForLFunctions

/-- **A cosine near one puts the angle near `2πℤ`.** -/
theorem exists_int_abs_sub_two_pi_mul_le {θ c : ℝ} (hc : 0 ≤ c) (h : 1 - Real.cos θ ≤ c) :
    ∃ m : ℤ, |θ - 2 * Real.pi * m| ≤ Real.pi * Real.sqrt (c / 2) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set m : ℤ := round (θ / (2 * Real.pi)) with hm
  set r : ℝ := θ - 2 * Real.pi * m with hr
  refine ⟨m, ?_⟩
  -- `r` is within half a period
  have hhalf : |r| ≤ Real.pi := by
    have h1 : |θ / (2 * Real.pi) - (m : ℝ)| ≤ 1 / 2 := by
      rw [hm]
      exact abs_sub_round _
    have h2 : |θ - 2 * Real.pi * m| = (2 * Real.pi) * |θ / (2 * Real.pi) - (m : ℝ)| := by
      have hfac : θ - 2 * Real.pi * m = (2 * Real.pi) * (θ / (2 * Real.pi) - (m : ℝ)) := by
        field_simp
      rw [hfac, abs_mul, abs_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)]
    rw [hr, h2]
    calc (2 * Real.pi) * |θ / (2 * Real.pi) - (m : ℝ)| ≤ (2 * Real.pi) * (1 / 2) := by
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.pi := by ring
  -- the half-angle identity
  have hcos : Real.cos θ = Real.cos r := by
    rw [hr]
    have := Real.cos_add_int_mul_two_pi (θ - 2 * Real.pi * m) m
    rw [← this]
    congr 1
    ring
  have hsin : 1 - Real.cos r = 2 * Real.sin (r / 2) ^ 2 := by
    have h2 : Real.cos r = 1 - 2 * Real.sin (r / 2) ^ 2 := by
      have := Real.cos_two_mul (r / 2)
      have hpyth := Real.sin_sq_add_cos_sq (r / 2)
      have hr2 : 2 * (r / 2) = r := by ring
      rw [hr2] at this
      nlinarith [this, hpyth]
    rw [h2]
    ring
  -- Jordan's inequality on the half angle
  have hsinbound : (2 / Real.pi) * |r / 2| ≤ |Real.sin (r / 2)| := by
    by_cases hpos : 0 ≤ r / 2
    · rw [abs_of_nonneg hpos, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hpos (by
        have : |r| ≤ Real.pi := hhalf
        have hr2 : r / 2 ≤ Real.pi / 2 := by
          have := abs_le.mp hhalf
          linarith [this.2]
        linarith))]
      exact Real.mul_le_sin hpos (by
        have := abs_le.mp hhalf
        linarith [this.2])
    · push Not at hpos
      have hneg : r / 2 < 0 := hpos
      have hneg' : (0 : ℝ) ≤ -(r / 2) := by linarith
      have hle : -(r / 2) ≤ Real.pi / 2 := by
        have := abs_le.mp hhalf
        linarith [this.1]
      have hjordan := Real.mul_le_sin hneg' hle
      rw [abs_of_neg hneg, abs_of_neg (Real.sin_neg_of_neg_of_neg_pi_lt hneg (by
        have := abs_le.mp hhalf
        linarith [this.1]))]
      rw [Real.sin_neg] at hjordan
      linarith
  -- combine
  have hsq : 2 * ((2 / Real.pi) * |r / 2|) ^ 2 ≤ c := by
    have hsin2 : (2 * Real.sin (r / 2) ^ 2) ≤ c := by
      rw [← hsin, ← hcos]
      exact h
    have habs : ((2 / Real.pi) * |r / 2|) ^ 2 ≤ Real.sin (r / 2) ^ 2 := by
      have h0 : (0 : ℝ) ≤ (2 / Real.pi) * |r / 2| := by positivity
      calc ((2 / Real.pi) * |r / 2|) ^ 2 ≤ |Real.sin (r / 2)| ^ 2 := by
            exact pow_le_pow_left₀ h0 hsinbound 2
        _ = Real.sin (r / 2) ^ 2 := sq_abs _
    linarith
  have hrbound : |r| ≤ Real.pi * Real.sqrt (c / 2) := by
    have hkey : (|r| / Real.pi) ^ 2 ≤ c / 2 := by
      have habs2 : (2 / Real.pi) * |r / 2| = |r| / Real.pi := by
        rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
        field_simp
      rw [habs2] at hsq
      linarith
    have hnn : (0 : ℝ) ≤ |r| / Real.pi := by positivity
    have hsqrt : |r| / Real.pi ≤ Real.sqrt (c / 2) := by
      have hc2 : (0 : ℝ) ≤ c / 2 := by positivity
      exact (Real.le_sqrt hnn hc2).mpr hkey
    calc |r| = Real.pi * (|r| / Real.pi) := by field_simp
      _ ≤ Real.pi * Real.sqrt (c / 2) := by
          exact mul_le_mul_of_nonneg_left hsqrt (le_of_lt hπ)
  exact hrbound

end GaloisForLFunctions
