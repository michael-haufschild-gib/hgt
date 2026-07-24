import GaloisForLFunctions.HTGeometry.QuarterRootTelescopeSum

/-!
# Linear domination of the square-root–log term

Past the explicit quartic threshold `(16/κ)⁴`:

`2·√t·log t ≤ (κ/2)·t`,

by the quarter-root bound `log t ≤ 4·√√t` and
`8·(√√t)³ ≤ (κ/2)·(√√t)⁴` once `√√t ≥ 16/κ`.  The companion absorbs an
additive constant: for `t` past `max((16/κ)⁴, (2/κ)·y)` the whole junk
`y + 2√t·log t` sits below `κ·t`.
-/

namespace HTGeometry

/-- `2√t·log t ≤ (κ/2)t` for `t ≥ (16/κ)⁴`. -/
theorem two_sqrt_mul_log_le_of_quartic_ge {κ t : ℝ} (hκ : 0 < κ)
    (ht : (16 / κ) ^ 4 ≤ t) :
    2 * Real.sqrt t * Real.log t ≤ κ / 2 * t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  rcases le_or_gt 1 t with h1 | h1
  · set s := Real.sqrt (Real.sqrt t) with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 (Real.sqrt_pos.2 ht0)
    have hsqt : Real.sqrt t = s ^ 2 :=
      (Real.sq_sqrt (Real.sqrt_nonneg t)).symm
    have ht4 : t = s ^ 4 := by
      have h2 := Real.sq_sqrt ht0.le
      rw [hsqt] at h2
      rw [← h2]
      ring
    have hlog : Real.log t ≤ 4 * s := by
      have := log_le_four_quarter_root_sub_one h1
      rw [← hs] at this
      linarith
    have hsge : 16 / κ ≤ s := by
      have h2 : Real.sqrt ((16 / κ) ^ 4) ≤ Real.sqrt t :=
        Real.sqrt_le_sqrt ht
      have h3 : Real.sqrt ((16 / κ) ^ 4) = (16 / κ) ^ 2 := by
        rw [show ((16 : ℝ) / κ) ^ 4 = ((16 / κ) ^ 2) ^ 2 by ring,
          Real.sqrt_sq (by positivity)]
      have h4 : Real.sqrt ((16 / κ) ^ 2) ≤ Real.sqrt (Real.sqrt t) :=
        Real.sqrt_le_sqrt (by rw [← h3]; exact h2)
      rwa [Real.sqrt_sq (by positivity), ← hs] at h4
    have hstep1 : 2 * Real.sqrt t * Real.log t ≤ 2 * s ^ 2 * (4 * s) := by
      rw [hsqt]
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    have hstep2 : 2 * s ^ 2 * (4 * s) ≤ κ / 2 * s ^ 4 := by
      have hks : 16 ≤ κ * s := by
        rw [div_le_iff₀ hκ] at hsge
        linarith
      nlinarith [mul_nonneg (pow_pos hs0 3).le
        (by linarith : (0 : ℝ) ≤ κ * s - 16)]
    calc 2 * Real.sqrt t * Real.log t
        ≤ 2 * s ^ 2 * (4 * s) := hstep1
      _ ≤ κ / 2 * s ^ 4 := hstep2
      _ = κ / 2 * t := by rw [← ht4]
  · have hlog0 : Real.log t ≤ 0 := Real.log_nonpos ht0.le h1.le
    have h2 : 0 ≤ 2 * Real.sqrt t * (-Real.log t) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith [ht0, hκ]

/-- Junk absorption: past `max((16/κ)⁴, (2/κ)·y)` the additive junk
`y + 2√t·log t` is dominated by `κ·t`. -/
theorem add_two_sqrt_mul_log_le_of_threshold {κ y T : ℝ} (hκ : 0 < κ)
    (hT1 : (16 / κ) ^ 4 ≤ T) (hT2 : 2 / κ * y ≤ T) :
    ∀ t : ℝ, T ≤ t → y + 2 * Real.sqrt t * Real.log t ≤ κ * t := by
  intro t htT
  have h2 := two_sqrt_mul_log_le_of_quartic_ge hκ (le_trans hT1 htT)
  have h4 : 2 / κ * y ≤ t := le_trans hT2 htT
  have h5 := mul_le_mul_of_nonneg_left h4
    (by positivity : (0 : ℝ) ≤ κ / 2)
  have h6 : κ / 2 * (2 / κ * y) = y := by
    field_simp
  linarith

end HTGeometry
