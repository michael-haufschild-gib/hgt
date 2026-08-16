import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The small-value window horizon is reciprocal, the mass cone horizon is linear

A harmonic small-value theorem of the shape

`log (z/y) > 40/δ + 2  ⟹  ∃ m ∈ (y, z], |R(m)| ≤ δ m + log z + 1`

has a window demand reciprocal in the relative error `δ`.  At critical scale `X = e^h` the
type-zero target `|R(X)| ≤ X^{1/2+ε}` is exactly the choice `δ = X^{-1/2+ε}`, so the demanded
window width is `40 e^{(1/2-ε)h} + 2`: exponential in the logarithmic height.

Every available mass cone has only a linear logarithmic horizon `log (z/y) ≤ C h`, so for all
large `h` no admissible window exists.  Read in the other direction, a linear horizon forces
`δ > 40/(C h - 2)`, and the critically normalized bound this produces, `40 e^{h/2}/(C h - 2)`,
diverges.  The mismatch is between an exponential and a linear horizon; it cannot be closed by
propagating the same anchors further.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-! ## The critical target as a small-value parameter -/

/-- **(24.58)** At critical scale `X = e^h` the type-zero target `X^{1/2+ε}` is exactly the
relative error `δ = X^{-1/2+ε}`. -/
theorem smallValueTarget_mul (h eps : ℝ) :
    Real.exp (-((1 / 2 - eps) * h)) * Real.exp h = Real.exp ((1 / 2 + eps) * h) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- **(24.59)** The window width demanded by the critical target. -/
theorem smallValueWindowDemand (h eps : ℝ) :
    40 / Real.exp (-((1 / 2 - eps) * h)) + 2
      = 40 * Real.exp ((1 / 2 - eps) * h) + 2 := by
  have hne : Real.exp ((1 / 2 - eps) * h) ≠ 0 := (Real.exp_pos _).ne'
  rw [Real.exp_neg]
  congr 1
  field_simp

/-! ## The exponential demand outruns every linear horizon -/

theorem tendsto_exp_div_id_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun h : ℝ => Real.exp (c * h) / h) atTop atTop := by
  have hbase : Tendsto (fun t : ℝ => Real.exp t / t ^ 1) atTop atTop :=
    Real.tendsto_exp_div_pow_atTop 1
  have hscale : Tendsto (fun h : ℝ => c * h) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id
  have hcomp := (hbase.comp hscale).const_mul_atTop hc
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with h hh
  rw [Function.comp_apply]
  field_simp

/-- **(24.59)** No linear window horizon can meet the exponential demand of the critical target. -/
theorem eventually_lt_smallValueWindowDemand (C : ℝ) {eps : ℝ} (heps : eps < 1 / 2) :
    ∀ᶠ h : ℝ in atTop, C * h < 40 * Real.exp ((1 / 2 - eps) * h) + 2 := by
  have hpos : 0 < 1 / 2 - eps := by linarith
  have hdiv : Tendsto (fun h : ℝ => 40 * (Real.exp ((1 / 2 - eps) * h) / h)) atTop atTop :=
    (tendsto_exp_div_id_atTop hpos).const_mul_atTop (by norm_num)
  filter_upwards [hdiv.eventually_gt_atTop C, eventually_gt_atTop (0 : ℝ)] with h hgt hh
  have hstep : C * h < 40 * Real.exp ((1 / 2 - eps) * h) := by
    rw [mul_div_assoc'] at hgt
    rw [← sub_pos]
    have hkey : C < 40 * Real.exp ((1 / 2 - eps) * h) / h := hgt
    rw [lt_div_iff₀ hh] at hkey
    linarith
  linarith

/-- **(24.59)** For all large logarithmic heights, no window inside a linear cone is admissible for
the critical target. -/
theorem no_admissible_window (C : ℝ) {eps : ℝ} (heps : eps < 1 / 2) :
    ∀ᶠ h : ℝ in atTop, ∀ w : ℝ, w ≤ C * h →
      ¬ (40 / Real.exp (-((1 / 2 - eps) * h)) + 2 < w) := by
  filter_upwards [eventually_lt_smallValueWindowDemand C heps] with h hh w hw hcon
  rw [smallValueWindowDemand] at hcon
  linarith

/-! ## What a linear horizon can force -/

/-- **(24.60)** A linear window horizon forces a relative error at least reciprocal in the
height. -/
theorem smallValueParameter_lower {C h delta w : ℝ} (hdelta : 0 < delta) (hCh : 2 < C * h)
    (hw : w ≤ C * h) (hadm : 40 / delta + 2 < w) : 40 / (C * h - 2) < delta := by
  have hpos : 0 < C * h - 2 := by linarith
  have hstep : 40 / delta < C * h - 2 := by linarith
  rw [div_lt_iff₀ hdelta] at hstep
  rw [div_lt_iff₀ hpos]
  linarith

/-- **(24.60)** The critically normalized bound that a linear horizon produces diverges: the
criterion retains exponential type `1/2`. -/
theorem tendsto_criticalNormalizedBound_atTop {C : ℝ} (hC : 0 < C) :
    Tendsto (fun h : ℝ => 40 / (C * h - 2) * Real.exp (h / 2)) atTop atTop := by
  have hhalf : Tendsto (fun h : ℝ => Real.exp ((1 / 2 : ℝ) * h) / h) atTop atTop :=
    tendsto_exp_div_id_atTop (by norm_num)
  have hscaled : Tendsto (fun h : ℝ => 40 / (2 * C) * (Real.exp ((1 / 2 : ℝ) * h) / h))
      atTop atTop :=
    hhalf.const_mul_atTop (by positivity)
  refine tendsto_atTop_mono' atTop ?_ hscaled
  filter_upwards [eventually_gt_atTop (max 1 (4 / C))] with h hh
  have hh1 : (1 : ℝ) < h := lt_of_le_of_lt (le_max_left _ _) hh
  have hh2 : 4 / C < h := lt_of_le_of_lt (le_max_right _ _) hh
  have hhpos : (0 : ℝ) < h := by linarith
  have hCh : 4 < C * h := by
    rw [div_lt_iff₀ hC] at hh2
    linarith
  have hden : 0 < C * h - 2 := by linarith
  have hbound : C * h - 2 ≤ C * h := by linarith
  have hexp : 0 < Real.exp ((1 / 2 : ℝ) * h) := Real.exp_pos _
  have hrewrite : (1 / 2 : ℝ) * h = h / 2 := by ring
  have hstep : 40 / (2 * C) * (Real.exp ((1 / 2 : ℝ) * h) / h)
      ≤ 40 / (C * h - 2) * Real.exp (h / 2) := by
    rw [hrewrite]
    have hlhs : 40 / (2 * C) * (Real.exp (h / 2) / h)
        = 40 / (2 * C * h) * Real.exp (h / 2) := by
      field_simp
    rw [hlhs]
    refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (Real.exp_pos _))
    refine div_le_div_of_nonneg_left (by norm_num) hden ?_
    nlinarith
  exact hstep

end

end RHTower
