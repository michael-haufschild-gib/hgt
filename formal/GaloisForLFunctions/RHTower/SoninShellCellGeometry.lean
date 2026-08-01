import GaloisForLFunctions.RHTower.SoninL2Model

/-!
# The geometry of the shell cells

The cells of a shell are not translates of one profile: they accumulate at the inner radius, the
`n`-th cell sitting at distance of order `1/n` from it with width of order `1/n²`.  So the
orthonormal family they carry is a family of ever narrower bumps piling up at the inner edge, not a
family of oscillating modes of growing frequency.

The width formula below is what fixes the frequency scale of the `n`-th cell, and hence how many
cells are usable at a given dilation scale.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

/-- The exact width of the `n`-th shell cell. -/
theorem shellRight_sub_shellLeft (a b : ℝ) (n : ℕ) :
    shellRight a b n - shellLeft a b n =
      (b - a) / (((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  have h3 : ((n : ℝ) + 3) ≠ 0 := by positivity
  rw [shellRight, shellLeft]
  field_simp
  ring

/-- The cells shrink: the width is at most `(b - a)/(n+2)²`. -/
theorem shellRight_sub_shellLeft_le (a b : ℝ) (hab : a ≤ b) (n : ℕ) :
    shellRight a b n - shellLeft a b n ≤ (b - a) / ((n : ℝ) + 2) ^ 2 := by
  rw [shellRight_sub_shellLeft a b n]
  have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have h3 : (0 : ℝ) < (n : ℝ) + 3 := by positivity
  have hden : ((n : ℝ) + 2) ^ 2 ≤ ((n : ℝ) + 2) * ((n : ℝ) + 3) := by nlinarith
  have hnum : (0 : ℝ) ≤ b - a := sub_nonneg.mpr hab
  exact div_le_div_of_nonneg_left hnum (by positivity) hden

/-- The cells accumulate at the inner radius. -/
theorem tendsto_shellLeft_atTop (a b : ℝ) :
    Filter.Tendsto (fun n : ℕ => shellLeft a b n) Filter.atTop (nhds a) := by
  have hdiv : Filter.Tendsto (fun n : ℕ => (b - a) / ((n : ℝ) + 3)) Filter.atTop (nhds 0) := by
    have hden : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 3)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop
    have hinv : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 3)⁻¹) Filter.atTop (nhds 0) :=
      hden.inv_tendsto_atTop
    have hmul := hinv.const_mul (b - a)
    simpa [div_eq_mul_inv] using hmul
  have h := hdiv.const_add a
  simpa [shellLeft] using h

end RHTower
