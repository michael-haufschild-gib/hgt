import GaloisForLFunctions.RHTower.LogPhaseProfile

/-!
# The cubic refinement of the universal phase profile

`LogPhaseProfile` gives the two-sided comparison `v²/4 ≤ -ψ(v) ≤ v²`.  Inverting the Morse
substitution `w = sgn(v)√(-2ψ(v))` needs the sharper statement that `-ψ` is *asymptotically* the
exact quadratic `v²/2`.  This file proves the explicit cubic bound

```text
| -ψ(v) - v²/2 | ≤ |v|³/3       for |v| ≤ 1/2,
```

together with the logarithmic estimate it rests on,

```text
| log(1+v) - v | ≤ v²           for |v| ≤ 1/2.
```

Both come from sign analysis of the two comparison functions `v² ± (log(1+v) - v)`, whose
derivatives are `v(1+2v)/(1+v)` and `v(3+2v)/(1+v)`.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

/-! ### Two comparison helpers -/

private theorem nonneg_of_hasDerivAt_right {F D : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hF0 : F 0 = 0)
    (hD : ∀ x ∈ Icc (0 : ℝ) b, HasDerivAt F (D x) x)
    (hpos : ∀ x ∈ Ioo (0 : ℝ) b, 0 ≤ D x) :
    ∀ x ∈ Icc (0 : ℝ) b, 0 ≤ F x := by
  have hcont : ContinuousOn F (Icc 0 b) := fun x hx => ((hD x hx).continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ F (interior (Icc 0 b)) := by
    intro x hx
    rw [interior_Icc] at hx
    exact ((hD x ⟨hx.1.le, hx.2.le⟩).differentiableAt).differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Icc (0 : ℝ) b), 0 ≤ deriv F x := by
    intro x hx
    have hx' := hx
    rw [interior_Icc] at hx'
    rw [(hD x ⟨hx'.1.le, hx'.2.le⟩).deriv]
    exact hpos x hx'
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc 0 b) hcont hdiff hderiv
  intro x hx
  have h := hmono (left_mem_Icc.mpr hb) hx hx.1
  rw [hF0] at h
  exact h

private theorem nonneg_of_hasDerivAt_left {F D : ℝ → ℝ} {a : ℝ} (ha : a ≤ 0)
    (hF0 : F 0 = 0)
    (hD : ∀ x ∈ Icc a (0 : ℝ), HasDerivAt F (D x) x)
    (hneg : ∀ x ∈ Ioo a (0 : ℝ), D x ≤ 0) :
    ∀ x ∈ Icc a (0 : ℝ), 0 ≤ F x := by
  have hcont : ContinuousOn F (Icc a 0) := fun x hx => ((hD x hx).continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ F (interior (Icc a 0)) := by
    intro x hx
    rw [interior_Icc] at hx
    exact ((hD x ⟨hx.1.le, hx.2.le⟩).differentiableAt).differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Icc a (0 : ℝ)), deriv F x ≤ 0 := by
    intro x hx
    have hx' := hx
    rw [interior_Icc] at hx'
    rw [(hD x ⟨hx'.1.le, hx'.2.le⟩).deriv]
    exact hneg x hx'
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc a 0) hcont hdiff hderiv
  intro x hx
  have h := hanti hx (right_mem_Icc.mpr ha) hx.2
  rw [hF0] at h
  exact h

private theorem nonpos_of_hasDerivAt_left {F D : ℝ → ℝ} {a : ℝ} (ha : a ≤ 0)
    (hF0 : F 0 = 0)
    (hD : ∀ x ∈ Icc a (0 : ℝ), HasDerivAt F (D x) x)
    (hpos : ∀ x ∈ Ioo a (0 : ℝ), 0 ≤ D x) :
    ∀ x ∈ Icc a (0 : ℝ), F x ≤ 0 := by
  have hcont : ContinuousOn F (Icc a 0) := fun x hx => ((hD x hx).continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ F (interior (Icc a 0)) := by
    intro x hx
    rw [interior_Icc] at hx
    exact ((hD x ⟨hx.1.le, hx.2.le⟩).differentiableAt).differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Icc a (0 : ℝ)), 0 ≤ deriv F x := by
    intro x hx
    have hx' := hx
    rw [interior_Icc] at hx'
    rw [(hD x ⟨hx'.1.le, hx'.2.le⟩).deriv]
    exact hpos x hx'
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc a 0) hcont hdiff hderiv
  intro x hx
  have h := hmono hx (right_mem_Icc.mpr ha) hx.2
  rw [hF0] at h
  exact h

/-! ### The logarithmic remainder -/

/-- The first-order remainder of the logarithm. -/
def logRemainder (v : ℝ) : ℝ := Real.log (1 + v) - v

@[simp] theorem logRemainder_zero : logRemainder 0 = 0 := by simp [logRemainder]

theorem hasDerivAt_logRemainder {v : ℝ} (hv : -1 < v) :
    HasDerivAt logRemainder ((1 + v)⁻¹ - 1) v := by
  have hpos : (0 : ℝ) < 1 + v := by linarith
  have hne : (1 + v) ≠ 0 := ne_of_gt hpos
  have hu : HasDerivAt (fun x : ℝ => 1 + x) 1 v :=
    HasDerivAt.const_add 1 (hasDerivAt_id' (x := v))
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + x)) ((1 + v)⁻¹ * 1) v :=
    (Real.hasDerivAt_log hne).comp v hu
  have h := hlog.sub (hasDerivAt_id' (x := v))
  refine h.congr_deriv ?_
  ring

/-- The upper comparison function `v² + (log(1+v) - v)`. -/
private def logUpper (v : ℝ) : ℝ := v ^ 2 + logRemainder v

/-- The lower comparison function `v² - (log(1+v) - v)`. -/
private def logLower (v : ℝ) : ℝ := v ^ 2 - logRemainder v

private theorem hasDerivAt_logUpper {v : ℝ} (hv : -1 < v) :
    HasDerivAt logUpper (v * (1 + 2 * v) / (1 + v)) v := by
  have hpos : (0 : ℝ) < 1 + v := by linarith
  have h := (hasDerivAt_pow 2 v).add (hasDerivAt_logRemainder hv)
  refine h.congr_deriv ?_
  field_simp
  ring

private theorem hasDerivAt_logLower {v : ℝ} (hv : -1 < v) :
    HasDerivAt logLower (v * (3 + 2 * v) / (1 + v)) v := by
  have hpos : (0 : ℝ) < 1 + v := by linarith
  have h := (hasDerivAt_pow 2 v).sub (hasDerivAt_logRemainder hv)
  refine h.congr_deriv ?_
  field_simp
  ring

/-- **The quadratic bound on the logarithmic remainder.**  `|log(1+v) - v| ≤ v²` for `|v| ≤ 1/2`. -/
theorem abs_logRemainder_le_sq {v : ℝ} (h1 : -(1/2 : ℝ) ≤ v) (h2 : v ≤ 1/2) :
    |logRemainder v| ≤ v ^ 2 := by
  have hv : -1 < v := by linarith
  have hup : 0 ≤ logUpper v := by
    rcases le_or_gt 0 v with h0 | h0
    · refine nonneg_of_hasDerivAt_right (b := 1/2) (D := fun x => x * (1 + 2 * x) / (1 + x))
        (by norm_num) (by simp [logUpper]) (fun x hx => hasDerivAt_logUpper (by linarith [hx.1]))
        (fun x hx => ?_) v ⟨h0, h2⟩
      have hx1 : (0 : ℝ) < 1 + x := by linarith [hx.1]
      have : (0 : ℝ) ≤ x * (1 + 2 * x) := by nlinarith [hx.1.le]
      positivity
    · refine nonneg_of_hasDerivAt_left (a := -(1/2 : ℝ)) (D := fun x => x * (1 + 2 * x) / (1 + x))
        (by norm_num) (by simp [logUpper]) (fun x hx => hasDerivAt_logUpper (by linarith [hx.1]))
        (fun x hx => ?_) v ⟨h1, h0.le⟩
      have hx1 : (0 : ℝ) < 1 + x := by linarith [hx.1]
      have hnum : x * (1 + 2 * x) ≤ 0 := by nlinarith [hx.1, hx.2]
      exact div_nonpos_of_nonpos_of_nonneg hnum hx1.le
  have hlow : 0 ≤ logLower v := by
    rcases le_or_gt 0 v with h0 | h0
    · refine nonneg_of_hasDerivAt_right (b := 1/2) (D := fun x => x * (3 + 2 * x) / (1 + x))
        (by norm_num) (by simp [logLower]) (fun x hx => hasDerivAt_logLower (by linarith [hx.1]))
        (fun x hx => ?_) v ⟨h0, h2⟩
      have hx1 : (0 : ℝ) < 1 + x := by linarith [hx.1]
      have : (0 : ℝ) ≤ x * (3 + 2 * x) := by nlinarith [hx.1.le]
      positivity
    · refine nonneg_of_hasDerivAt_left (a := -(1/2 : ℝ)) (D := fun x => x * (3 + 2 * x) / (1 + x))
        (by norm_num) (by simp [logLower]) (fun x hx => hasDerivAt_logLower (by linarith [hx.1]))
        (fun x hx => ?_) v ⟨h1, h0.le⟩
      have hx1 : (0 : ℝ) < 1 + x := by linarith [hx.1]
      have hnum : x * (3 + 2 * x) ≤ 0 := by nlinarith [hx.1, hx.2]
      exact div_nonpos_of_nonpos_of_nonneg hnum hx1.le
  simp only [logUpper, logLower] at hup hlow
  rw [abs_le]
  constructor <;> linarith

/-! ### The cubic remainder of the profile -/

/-- The second-order remainder of the universal profile. -/
def logPhaseCubicRemainder (v : ℝ) : ℝ := -logPhaseProfile v - v ^ 2 / 2

@[simp] theorem logPhaseCubicRemainder_zero : logPhaseCubicRemainder 0 = 0 := by
  simp [logPhaseCubicRemainder]

theorem hasDerivAt_logPhaseCubicRemainder {v : ℝ} (hv : -1 < v) :
    HasDerivAt logPhaseCubicRemainder (logRemainder v) v := by
  have h1 := hasDerivAt_neg_logPhaseProfile hv
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) (2 * v / 2) v := by
    simpa using ((hasDerivAt_pow 2 v).div_const 2)
  have h := h1.sub h2
  refine h.congr_deriv ?_
  simp [logRemainder]

private def cubicUpper (v : ℝ) : ℝ := v ^ 3 / 3 + logPhaseCubicRemainder v
private def cubicLower (v : ℝ) : ℝ := v ^ 3 / 3 - logPhaseCubicRemainder v

private theorem hasDerivAt_cubicUpper {v : ℝ} (hv : -1 < v) :
    HasDerivAt cubicUpper (v ^ 2 + logRemainder v) v := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ 3 / 3) (3 * v ^ 2 / 3) v := by
    simpa using ((hasDerivAt_pow 3 v).div_const 3)
  have h := h1.add (hasDerivAt_logPhaseCubicRemainder hv)
  refine h.congr_deriv ?_
  ring

private theorem hasDerivAt_cubicLower {v : ℝ} (hv : -1 < v) :
    HasDerivAt cubicLower (v ^ 2 - logRemainder v) v := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ 3 / 3) (3 * v ^ 2 / 3) v := by
    simpa using ((hasDerivAt_pow 3 v).div_const 3)
  have h := h1.sub (hasDerivAt_logPhaseCubicRemainder hv)
  refine h.congr_deriv ?_
  ring

/-- **The cubic bound.**  `|-ψ(v) - v²/2| ≤ |v|³/3` for `|v| ≤ 1/2`. -/
theorem abs_logPhaseCubicRemainder_le {v : ℝ} (h1 : -(1/2 : ℝ) ≤ v) (h2 : v ≤ 1/2) :
    |logPhaseCubicRemainder v| ≤ |v| ^ 3 / 3 := by
  have hUderiv : ∀ x : ℝ, -(1/2 : ℝ) < x → x < 1/2 → 0 ≤ x ^ 2 + logRemainder x := by
    intro x hx1 hx2
    have h := abs_le.mp (abs_logRemainder_le_sq hx1.le hx2.le)
    linarith [h.1]
  have hLderiv : ∀ x : ℝ, -(1/2 : ℝ) < x → x < 1/2 → 0 ≤ x ^ 2 - logRemainder x := by
    intro x hx1 hx2
    have h := abs_le.mp (abs_logRemainder_le_sq hx1.le hx2.le)
    linarith [h.2]
  rcases le_or_gt 0 v with h0 | h0
  · have hU : 0 ≤ cubicUpper v :=
      nonneg_of_hasDerivAt_right (b := 1/2) (D := fun x => x ^ 2 + logRemainder x)
        (by norm_num) (by simp [cubicUpper])
        (fun x hx => hasDerivAt_cubicUpper (by linarith [hx.1]))
        (fun x hx => hUderiv x (by linarith [hx.1]) hx.2) v ⟨h0, h2⟩
    have hL : 0 ≤ cubicLower v :=
      nonneg_of_hasDerivAt_right (b := 1/2) (D := fun x => x ^ 2 - logRemainder x)
        (by norm_num) (by simp [cubicLower])
        (fun x hx => hasDerivAt_cubicLower (by linarith [hx.1]))
        (fun x hx => hLderiv x (by linarith [hx.1]) hx.2) v ⟨h0, h2⟩
    simp only [cubicUpper, cubicLower] at hU hL
    rw [abs_of_nonneg h0, abs_le]
    constructor <;> linarith
  · have hU : cubicUpper v ≤ 0 :=
      nonpos_of_hasDerivAt_left (a := -(1/2 : ℝ)) (D := fun x => x ^ 2 + logRemainder x)
        (by norm_num) (by simp [cubicUpper])
        (fun x hx => hasDerivAt_cubicUpper (by linarith [hx.1]))
        (fun x hx => hUderiv x hx.1 (by linarith [hx.2])) v ⟨h1, h0.le⟩
    have hL : cubicLower v ≤ 0 :=
      nonpos_of_hasDerivAt_left (a := -(1/2 : ℝ)) (D := fun x => x ^ 2 - logRemainder x)
        (by norm_num) (by simp [cubicLower])
        (fun x hx => hasDerivAt_cubicLower (by linarith [hx.1]))
        (fun x hx => hLderiv x hx.1 (by linarith [hx.2])) v ⟨h1, h0.le⟩
    simp only [cubicUpper, cubicLower] at hU hL
    rw [abs_of_neg h0, abs_le]
    constructor <;> nlinarith [hU, hL]

end GaloisForLFunctions.RHTower
