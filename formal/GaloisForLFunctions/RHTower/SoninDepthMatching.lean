import Mathlib

/-!
# Matching the Sonin aperture depth to the Wold first trace

The Sonin aperture cannot be compared with the prime cutoff arbitrarily: the Wold first trace fixes
its logarithmic depth.  With the source-defined schedule `N_x = ⌊2 / (a_x log r)⌋` the residual is
less than one step, and therefore the geometric escape `r^{N_x d}` is squeezed between
`r^{−d} exp(2d / a_x)` and `exp(2d / a_x)` — the two reflected Wold–Gamma gauge norms.  Aperture
escape and Gamma first trace have the same height-one essential type once the depth is matched.
-/

namespace RHTower

/-- The source-defined Sonin depth schedule: `N_x = ⌊2 / (a_x log r)⌋`. -/
noncomputable def soninDepth (a r : ℝ) : ℕ := ⌊2 / (a * Real.log r)⌋₊

/-- **`(18b)`: the schedule matches the Wold first trace to within one step.** -/
theorem soninDepth_bounds {a r : ℝ} (ha : 0 < a) (hr : 1 < r) :
    0 ≤ 2 / a - (soninDepth a r : ℝ) * Real.log r ∧
      2 / a - (soninDepth a r : ℝ) * Real.log r < Real.log r := by
  have hL : 0 < Real.log r := Real.log_pos hr
  have ht : (0 : ℝ) ≤ 2 / (a * Real.log r) := by positivity
  have hfloor_le : ((soninDepth a r : ℕ) : ℝ) ≤ 2 / (a * Real.log r) :=
    Nat.floor_le ht
  have hlt_floor : 2 / (a * Real.log r) < ((soninDepth a r : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hkey : (soninDepth a r : ℝ) * Real.log r ≤ 2 / a := by
    have := mul_le_mul_of_nonneg_right hfloor_le hL.le
    calc (soninDepth a r : ℝ) * Real.log r
        ≤ 2 / (a * Real.log r) * Real.log r := this
      _ = 2 / a := by field_simp
  have hkey2 : 2 / a < ((soninDepth a r : ℝ) + 1) * Real.log r := by
    have := mul_lt_mul_of_pos_right hlt_floor hL
    calc 2 / a = 2 / (a * Real.log r) * Real.log r := by field_simp
      _ < ((soninDepth a r : ℝ) + 1) * Real.log r := this
  constructor
  · linarith
  · nlinarith [hkey2]

/-- **`(18d)`–`(18e)`: the aperture escape and the Wold gauge have the same height.** -/
theorem soninDepth_rpow_bounds {a r d : ℝ} (ha : 0 < a) (hr : 1 < r) (hd : 0 ≤ d) :
    r ^ (-d) * Real.exp (2 * d / a) ≤ r ^ ((soninDepth a r : ℝ) * d) ∧
      r ^ ((soninDepth a r : ℝ) * d) ≤ Real.exp (2 * d / a) := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hL : 0 < Real.log r := Real.log_pos hr
  obtain ⟨hb1, hb2⟩ := soninDepth_bounds ha hr
  have hrepr : r ^ ((soninDepth a r : ℝ) * d)
      = Real.exp ((soninDepth a r : ℝ) * Real.log r * d) := by
    rw [Real.rpow_def_of_pos hr0]
    congr 1
    ring
  have hneg : r ^ (-d) = Real.exp (-(Real.log r * d)) := by
    rw [Real.rpow_def_of_pos hr0]
    congr 1
    ring
  have hAd : 2 * d / a = 2 / a * d := by ring
  constructor
  · rw [hrepr, hneg, ← Real.exp_add, hAd]
    refine Real.exp_le_exp.mpr ?_
    have h := mul_le_mul_of_nonneg_right hb2.le hd
    nlinarith [h]
  · rw [hrepr, hAd]
    refine Real.exp_le_exp.mpr ?_
    have h := mul_nonneg hb1 hd
    nlinarith [h]


/-- **`(18e)`: with the depth matched, a two-sided aperture rigidity bound transfers to the Wold
gauge.**  The escape `r^{N_x d}` and the gauge `exp(2 d / a_x)` differ by the fixed factor
`r^{−d}`, so the aperture cannot supply a larger essential type than the first trace. -/
theorem norm_le_of_soninDepth_rigidity {a r d C₁ C₂ K : ℝ} (ha : 0 < a) (hr : 1 < r)
    (hd : 0 ≤ d) (hC₁ : 0 ≤ C₁)
    (hlow : C₁ * r ^ ((soninDepth a r : ℝ) * d) ≤ K)
    (hup : K ≤ C₂ * r ^ ((soninDepth a r : ℝ) * d)) (hC₂ : 0 ≤ C₂) :
    C₁ * (r ^ (-d) * Real.exp (2 * d / a)) ≤ K ∧ K ≤ C₂ * Real.exp (2 * d / a) := by
  obtain ⟨h1, h2⟩ := soninDepth_rpow_bounds ha hr hd
  constructor
  · exact le_trans (mul_le_mul_of_nonneg_left h1 hC₁) hlow
  · exact le_trans hup (mul_le_mul_of_nonneg_left h2 hC₂)

end RHTower
