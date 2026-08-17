import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The unit-step difference quotient of a real power

The mean value theorem writes the unit backward difference of `t ↦ t^r` as `-r ξ^{r-1}` with
`ξ` in the open unit interval above the base point.  Normalising by `x^{r-1}` therefore leaves
`-r t^{r-1}` with `t = ξ/x ∈ [1, (x+1)/x]`, and `t^{r-1} → 1` uniformly as `x → ∞`.  So a unit
difference raises the power by exactly one, with limit constant `-r`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The mean value form of the normalised unit step of a real power. -/
theorem exists_rpow_unit_step_quotient (r : ℝ) {x : ℝ} (hx : 0 < x) :
    ∃ t : ℝ, 1 ≤ t ∧ t ≤ (x + 1) / x
      ∧ (x ^ r - (x + 1) ^ r) / x ^ (r - 1) = -r * t ^ (r - 1) := by
  have hcont : ContinuousOn (fun s : ℝ => s ^ r) (Set.Icc x (x + 1)) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := lt_of_lt_of_le hx hs.1
    exact (Real.continuousAt_rpow_const s r (Or.inl (ne_of_gt hs0))).continuousWithinAt
  have hderiv : ∀ s ∈ Set.Ioo x (x + 1),
      HasDerivAt (fun s : ℝ => s ^ r) (r * s ^ (r - 1)) s := by
    intro s hs
    have hs0 : (0 : ℝ) < s := lt_trans hx hs.1
    exact Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hs0))
  obtain ⟨xi, hxi, hslope⟩ := exists_hasDerivAt_eq_slope (fun s : ℝ => s ^ r)
    (fun s => r * s ^ (r - 1)) (by linarith : x < x + 1) hcont hderiv
  have hxi0 : (0 : ℝ) < xi := lt_trans hx hxi.1
  have hden : (x + 1) - x = 1 := by ring
  rw [hden, div_one] at hslope
  refine ⟨xi / x, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hx, one_mul]
    exact hxi.1.le
  · exact div_le_div_of_nonneg_right hxi.2.le hx.le
  · have hstep : x ^ r - (x + 1) ^ r = -r * xi ^ (r - 1) := by
      have := hslope
      linarith [this]
    have hxr : (0 : ℝ) < x ^ (r - 1) := Real.rpow_pos_of_pos hx _
    rw [hstep, Real.div_rpow hxi0.le hx.le]
    field_simp

/-- **The unit step raises the power by exactly one.**  The normalised backward unit difference of
`x^r` tends to `-r`. -/
theorem tendsto_rpow_unit_step_quotient (r : ℝ) :
    Tendsto (fun x : ℝ => (x ^ r - (x + 1) ^ r) / x ^ (r - 1)) atTop (𝓝 (-r)) := by
  have hratio : Tendsto (fun x : ℝ => ((x + 1) / x) ^ (r - 1)) atTop (𝓝 1) := by
    have hbase : Tendsto (fun x : ℝ => (x + 1) / x) atTop (𝓝 1) := by
      have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.congr fun x => (one_div x).symm
      have h : Tendsto (fun x : ℝ => 1 + 1 / x) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add hinv
      rw [add_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      field_simp
    have hcont : ContinuousAt (fun y : ℝ => y ^ (r - 1)) 1 :=
      Real.continuousAt_rpow_const 1 (r - 1) (Or.inl one_ne_zero)
    have := hcont.tendsto.comp hbase
    simpa [Real.one_rpow, Function.comp_def] using this
  rw [Metric.tendsto_atTop]
  intro eps heps
  have hcoef : (0 : ℝ) < |r| + 1 := by positivity
  have hdelta : (0 : ℝ) < eps / (|r| + 1) := by positivity
  obtain ⟨X, hX⟩ := Metric.tendsto_atTop.1 hratio (eps / (|r| + 1)) hdelta
  refine ⟨max X 1, fun x hx => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_right X 1) hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  obtain ⟨t, ht1, ht2, hteq⟩ := exists_rpow_unit_step_quotient r hx0
  have ha := hX x (le_trans (le_max_left X 1) hx)
  rw [Real.dist_eq] at ha ⊢
  have hcmp : |t ^ (r - 1) - 1| ≤ |((x + 1) / x) ^ (r - 1) - 1| := by
    have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht1
    rcases le_or_gt 0 (r - 1) with hr | hr
    · have h1 : (1 : ℝ) ≤ t ^ (r - 1) := Real.one_le_rpow ht1 hr
      have h2 : t ^ (r - 1) ≤ ((x + 1) / x) ^ (r - 1) := Real.rpow_le_rpow ht0 ht2 hr
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · have h1 : t ^ (r - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 hr.le
      have h2 : ((x + 1) / x) ^ (r - 1) ≤ t ^ (r - 1) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) ht2 hr.le
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
  have hfinal : |(x ^ r - (x + 1) ^ r) / x ^ (r - 1) - -r| = |r| * |t ^ (r - 1) - 1| := by
    rw [hteq]
    have : -r * t ^ (r - 1) - -r = -r * (t ^ (r - 1) - 1) := by ring
    rw [this, abs_mul, abs_neg]
  rw [hfinal]
  calc |r| * |t ^ (r - 1) - 1| ≤ |r| * |((x + 1) / x) ^ (r - 1) - 1| :=
        mul_le_mul_of_nonneg_left hcmp (abs_nonneg r)
    _ ≤ (|r| + 1) * |((x + 1) / x) ^ (r - 1) - 1| :=
        mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    _ < (|r| + 1) * (eps / (|r| + 1)) := mul_lt_mul_of_pos_left ha hcoef
    _ = eps := by field_simp

end GaloisForLFunctions.HTGeometry
