import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The universal profile of the Riemann–Siegel phase

The phase of `χ(1/2+it)·n^{it}` is `f(t) = -t log t + (B+1) t` for a parameter `B`, whose unique
stationary point is `t₀ = e^{B}`.  Writing `t = t₀(1+v)` gives the exact factorisation

```text
f(t) - f(t₀) = t₀ · ψ(v),      ψ(v) = v - (1+v) log(1+v),
```

so the local geometry of *every* such stationary point is governed by the single universal profile
`ψ`, independent of `B`.  This file records `ψ` and the facts needed to invert it:

* `ψ(0) = 0`, `ψ'(v) = -log(1+v)`, so `0` is the unique critical point and a strict maximum;
* `ψ ≤ 0` on `(-1,∞)`, with the two-sided quadratic comparison

  ```text
  v²/4 ≤ -ψ(v) ≤ v²      on (-1,1],
  ```

  the upper bound holding on all of `(-1,∞)`;
* `-ψ` is strictly increasing on `[0,∞)` and strictly decreasing on `(-1,0]`.

Both comparisons come from the single elementary gap `K(v) = log(1+v) - v/2`, which is increasing
on `(-1,1]` and vanishes at `0`.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

/-- The universal profile of the Riemann–Siegel phase at a stationary point. -/
def logPhaseProfile (v : ℝ) : ℝ := v - (1 + v) * Real.log (1 + v)

@[simp] theorem logPhaseProfile_zero : logPhaseProfile 0 = 0 := by
  simp [logPhaseProfile]

/-- `ψ'(v) = -log(1+v)`: the profile has a single critical point, at `v = 0`. -/
theorem hasDerivAt_logPhaseProfile {v : ℝ} (hv : -1 < v) :
    HasDerivAt logPhaseProfile (-Real.log (1 + v)) v := by
  have hpos : (0 : ℝ) < 1 + v := by linarith
  have hne : (1 + v) ≠ 0 := ne_of_gt hpos
  have hu : HasDerivAt (fun x : ℝ => 1 + x) 1 v :=
    HasDerivAt.const_add 1 (hasDerivAt_id' (x := v))
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + x)) ((1 + v)⁻¹ * 1) v :=
    (Real.hasDerivAt_log hne).comp v hu
  have hprod := hu.mul hlog
  have hmain := (hasDerivAt_id' (x := v)).sub hprod
  refine hmain.congr_deriv ?_
  field_simp
  ring

/-- `log(1+v) ≤ v`. -/
theorem log_one_add_le {v : ℝ} (hv : -1 < v) : Real.log (1 + v) ≤ v := by
  have hpos : (0 : ℝ) < 1 + v := by linarith
  simpa using Real.log_le_sub_one_of_pos hpos

/-- `log(1+v) ≥ v/(1+v)`. -/
theorem le_log_one_add {v : ℝ} (hv : -1 < v) : v / (1 + v) ≤ Real.log (1 + v) := by
  have hpos : (0 : ℝ) < 1 + v := by linarith
  have hinv : (0 : ℝ) < (1 + v)⁻¹ := inv_pos.mpr hpos
  have h := Real.log_le_sub_one_of_pos hinv
  rw [Real.log_inv] at h
  have hid : v / (1 + v) = 1 - (1 + v)⁻¹ := by
    field_simp
    ring
  rw [hid]
  linarith

/-- **The profile is nonpositive.**  The stationary point is a maximum. -/
theorem logPhaseProfile_nonpos {v : ℝ} (hv : -1 < v) : logPhaseProfile v ≤ 0 := by
  have hpos : (0 : ℝ) < 1 + v := by linarith
  have h := le_log_one_add hv
  have hmul : (1 + v) * (v / (1 + v)) ≤ (1 + v) * Real.log (1 + v) :=
    mul_le_mul_of_nonneg_left h hpos.le
  have hid : (1 + v) * (v / (1 + v)) = v := by field_simp
  rw [hid] at hmul
  simp only [logPhaseProfile]
  linarith

/-- **The quadratic upper bound.**  `-ψ(v) ≤ v²` on the whole ray. -/
theorem neg_logPhaseProfile_le_sq {v : ℝ} (hv : -1 < v) : -logPhaseProfile v ≤ v ^ (2 : ℕ) := by
  have hpos : (0 : ℝ) < 1 + v := by linarith
  have h := log_one_add_le hv
  have hmul : (1 + v) * Real.log (1 + v) ≤ (1 + v) * v :=
    mul_le_mul_of_nonneg_left h hpos.le
  simp only [logPhaseProfile]
  nlinarith [hmul]

/-! ### The elementary gap `K(v) = log(1+v) - v/2` -/

/-- The half-slope gap of the logarithm. -/
def halfLogGap (v : ℝ) : ℝ := Real.log (1 + v) - v / 2

@[simp] theorem halfLogGap_zero : halfLogGap 0 = 0 := by simp [halfLogGap]

theorem hasDerivAt_halfLogGap {v : ℝ} (hv : -1 < v) :
    HasDerivAt halfLogGap ((1 + v)⁻¹ - 1 / 2) v := by
  have hpos : (0 : ℝ) < 1 + v := by linarith
  have hne : (1 + v) ≠ 0 := ne_of_gt hpos
  have hu : HasDerivAt (fun x : ℝ => 1 + x) 1 v :=
    HasDerivAt.const_add 1 (hasDerivAt_id' (x := v))
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + x)) ((1 + v)⁻¹ * 1) v :=
    (Real.hasDerivAt_log hne).comp v hu
  have hhalf : HasDerivAt (fun x : ℝ => x / 2) (1 / 2 : ℝ) v := by
    simpa using (hasDerivAt_id' (x := v)).div_const 2
  have h := hlog.sub hhalf
  refine h.congr_deriv ?_
  ring

/-- `K` is monotone on every closed subinterval of `(-1,1]`. -/
theorem monotoneOn_halfLogGap {a b : ℝ} (ha : -1 < a) (hb : b ≤ 1) :
    MonotoneOn halfLogGap (Icc a b) := by
  have hderiv : ∀ x ∈ interior (Icc a b), 0 ≤ deriv halfLogGap x := by
    intro x hx
    rw [interior_Icc] at hx
    have hx1 : -1 < x := lt_of_lt_of_le ha hx.1.le
    have hx2 : x ≤ 1 := hx.2.le.trans hb
    have hpos : (0 : ℝ) < 1 + x := by linarith
    rw [(hasDerivAt_halfLogGap hx1).deriv]
    have : (1 + x) ≤ 2 := by linarith
    have h2 : (2 : ℝ)⁻¹ ≤ (1 + x)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hpos this
    linarith [h2]
  have hdiff : DifferentiableOn ℝ halfLogGap (interior (Icc a b)) := by
    intro x hx
    rw [interior_Icc] at hx
    have hx1 : -1 < x := lt_of_lt_of_le ha hx.1.le
    exact ((hasDerivAt_halfLogGap hx1).differentiableAt).differentiableWithinAt
  have hcont : ContinuousOn halfLogGap (Icc a b) := by
    intro x hx
    have hx1 : -1 < x := lt_of_lt_of_le ha hx.1
    exact ((hasDerivAt_halfLogGap hx1).continuousAt).continuousWithinAt
  exact monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont hdiff hderiv

theorem halfLogGap_nonneg {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) : 0 ≤ halfLogGap v := by
  have hmono := monotoneOn_halfLogGap (a := 0) (b := 1) (by norm_num) le_rfl
  have := hmono (left_mem_Icc.mpr (by norm_num)) ⟨h0, h1⟩ h0
  simpa using this

theorem halfLogGap_nonpos {v : ℝ} (hv : -1 < v) (h0 : v ≤ 0) : halfLogGap v ≤ 0 := by
  have hmono := monotoneOn_halfLogGap (a := v) (b := 0) hv (by norm_num)
  have := hmono (left_mem_Icc.mpr h0) (right_mem_Icc.mpr h0) h0
  simpa using this

/-! ### The quadratic lower bound -/

/-- The gap between `-ψ` and its quadratic minorant. -/
def logPhaseQuadGap (v : ℝ) : ℝ := -logPhaseProfile v - v ^ (2 : ℕ) / 4

@[simp] theorem logPhaseQuadGap_zero : logPhaseQuadGap 0 = 0 := by
  simp [logPhaseQuadGap]

theorem hasDerivAt_logPhaseQuadGap {v : ℝ} (hv : -1 < v) :
    HasDerivAt logPhaseQuadGap (halfLogGap v) v := by
  have h1 := (hasDerivAt_logPhaseProfile hv).neg
  have h2 : HasDerivAt (fun x : ℝ => x ^ (2 : ℕ) / 4) (2 * v / 4) v := by
    simpa using ((hasDerivAt_pow 2 v).div_const 4)
  have h := h1.sub h2
  refine h.congr_deriv ?_
  simp [halfLogGap]
  ring

/-- **The quadratic lower bound.**  `v²/4 ≤ -ψ(v)` on `(-1,1]`. -/
theorem sq_div_four_le_neg_logPhaseProfile {v : ℝ} (hv : -1 < v) (h1 : v ≤ 1) :
    v ^ (2 : ℕ) / 4 ≤ -logPhaseProfile v := by
  have key : 0 ≤ logPhaseQuadGap v := by
    rcases le_or_gt 0 v with h0 | h0
    · -- increasing on [0, v]
      have hmono : MonotoneOn logPhaseQuadGap (Icc 0 v) := by
        have hderiv : ∀ x ∈ interior (Icc (0 : ℝ) v), 0 ≤ deriv logPhaseQuadGap x := by
          intro x hx
          rw [interior_Icc] at hx
          have hx1 : -1 < x := by linarith [hx.1]
          rw [(hasDerivAt_logPhaseQuadGap hx1).deriv]
          exact halfLogGap_nonneg hx.1.le (hx.2.le.trans h1)
        have hdiff : DifferentiableOn ℝ logPhaseQuadGap (interior (Icc (0 : ℝ) v)) := by
          intro x hx
          rw [interior_Icc] at hx
          have hx1 : -1 < x := by linarith [hx.1]
          exact ((hasDerivAt_logPhaseQuadGap hx1).differentiableAt).differentiableWithinAt
        have hcont : ContinuousOn logPhaseQuadGap (Icc (0 : ℝ) v) := by
          intro x hx
          have hx1 : -1 < x := by linarith [hx.1]
          exact ((hasDerivAt_logPhaseQuadGap hx1).continuousAt).continuousWithinAt
        exact monotoneOn_of_deriv_nonneg (convex_Icc 0 v) hcont hdiff hderiv
      have := hmono (left_mem_Icc.mpr h0) (right_mem_Icc.mpr h0) h0
      simpa using this
    · -- decreasing on [v, 0]
      have hmono : AntitoneOn logPhaseQuadGap (Icc v 0) := by
        have hderiv : ∀ x ∈ interior (Icc v (0 : ℝ)), deriv logPhaseQuadGap x ≤ 0 := by
          intro x hx
          rw [interior_Icc] at hx
          have hx1 : -1 < x := lt_trans hv hx.1
          rw [(hasDerivAt_logPhaseQuadGap hx1).deriv]
          exact halfLogGap_nonpos hx1 hx.2.le
        have hdiff : DifferentiableOn ℝ logPhaseQuadGap (interior (Icc v (0 : ℝ))) := by
          intro x hx
          rw [interior_Icc] at hx
          have hx1 : -1 < x := lt_trans hv hx.1
          exact ((hasDerivAt_logPhaseQuadGap hx1).differentiableAt).differentiableWithinAt
        have hcont : ContinuousOn logPhaseQuadGap (Icc v (0 : ℝ)) := by
          intro x hx
          have hx1 : -1 < x := lt_of_lt_of_le hv hx.1
          exact ((hasDerivAt_logPhaseQuadGap hx1).continuousAt).continuousWithinAt
        exact antitoneOn_of_deriv_nonpos (convex_Icc v 0) hcont hdiff hderiv
      have := hmono (left_mem_Icc.mpr h0.le) (right_mem_Icc.mpr h0.le) h0.le
      simpa using this
  simp only [logPhaseQuadGap] at key
  linarith

/-! ### Strict monotonicity of `-ψ` -/

theorem hasDerivAt_neg_logPhaseProfile {v : ℝ} (hv : -1 < v) :
    HasDerivAt (fun x : ℝ => -logPhaseProfile x) (Real.log (1 + v)) v := by
  have hpos : (0 : ℝ) < 1 + v := by linarith
  have hne : (1 + v) ≠ 0 := ne_of_gt hpos
  have hfun : (fun x : ℝ => -logPhaseProfile x)
      = fun x : ℝ => (1 + x) * Real.log (1 + x) - x := by
    funext x
    simp only [logPhaseProfile]
    ring
  rw [hfun]
  have hu : HasDerivAt (fun x : ℝ => 1 + x) 1 v :=
    HasDerivAt.const_add 1 (hasDerivAt_id' (x := v))
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + x)) ((1 + v)⁻¹ * 1) v :=
    (Real.hasDerivAt_log hne).comp v hu
  have h := (hu.mul hlog).sub (hasDerivAt_id' (x := v))
  refine h.congr_deriv ?_
  field_simp
  ring

/-- `-ψ` is strictly increasing to the right of the stationary point. -/
theorem strictMonoOn_neg_logPhaseProfile :
    StrictMonoOn (fun v : ℝ => -logPhaseProfile v) (Ici (0 : ℝ)) := by
  have hderiv : ∀ x ∈ interior (Ici (0 : ℝ)), 0 < deriv (fun v : ℝ => -logPhaseProfile v) x := by
    intro x hx
    rw [interior_Ici] at hx
    have hx0 : (0 : ℝ) < x := hx
    have hx1 : -1 < x := by linarith
    rw [(hasDerivAt_neg_logPhaseProfile hx1).deriv]
    exact Real.log_pos (by linarith)
  have hcont : ContinuousOn (fun v : ℝ => -logPhaseProfile v) (Ici (0 : ℝ)) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx
    have hx1 : -1 < x := by linarith
    exact ((hasDerivAt_neg_logPhaseProfile hx1).continuousAt).continuousWithinAt
  exact strictMonoOn_of_deriv_pos (convex_Ici 0) hcont hderiv

/-- `-ψ` is strictly decreasing to the left of the stationary point. -/
theorem strictAntiOn_neg_logPhaseProfile {a : ℝ} (ha : -1 < a) :
    StrictAntiOn (fun v : ℝ => -logPhaseProfile v) (Icc a 0) := by
  have hderiv : ∀ x ∈ interior (Icc a (0 : ℝ)), deriv (fun v : ℝ => -logPhaseProfile v) x < 0 := by
    intro x hx
    rw [interior_Icc] at hx
    have hx1 : -1 < x := lt_trans ha hx.1
    rw [(hasDerivAt_neg_logPhaseProfile hx1).deriv]
    exact Real.log_neg (by linarith) (by linarith [hx.2])
  have hcont : ContinuousOn (fun v : ℝ => -logPhaseProfile v) (Icc a (0 : ℝ)) := by
    intro x hx
    have hx1 : -1 < x := lt_of_lt_of_le ha hx.1
    exact ((hasDerivAt_neg_logPhaseProfile hx1).continuousAt).continuousWithinAt
  exact strictAntiOn_of_deriv_neg (convex_Icc a 0) hcont hderiv

end GaloisForLFunctions.RHTower
