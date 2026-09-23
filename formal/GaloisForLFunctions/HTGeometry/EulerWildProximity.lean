import GaloisForLFunctions.HTGeometry.ProximityFirstOrderAutonomous
import GaloisForLFunctions.HTGeometry.NevanlinnaEntireCharacteristic
import GaloisForLFunctions.HTGeometry.OmittedValueCharacteristicBound

/-!
# The wild branch turns the characteristic into a logarithmic derivative

If the relation forces `c‖f‖^{m+1} ≤ ‖z f′‖^m` at every point where `‖f‖` is large — which happens
exactly when the maximal total degree of the relation sits at the coefficient of `(z f′)^(0 : ℕ)` — then
taking `log⁺` and integrating over the circle gives

```text
(m+1)·m(r,f) ≤ m·m(r, z f′) + E ≤ m·(log⁺ r + m(r,f) + m(r, f′/f)) + E,
```

so for an entire `f`, where the characteristic is the proximity,

```text
T(r,f) ≤ m·m(r, f′/f) + m·log⁺ r + E.
```

The right side is a logarithmic-derivative proximity, which is the error term of Nevanlinna theory.
The inequality `T ≤ S` is the same collapse that proves Picard's theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open ValueDistribution Metric Real

/-- The proximity function of the coordinate is `log⁺` of the radius. -/
theorem proximity_id_eq (r : ℝ) :
    proximity (fun z : ℂ => z) ⊤ r = Real.posLog |r| := by
  rw [ValueDistribution.proximity_top]
  rw [circleAverage_congr_sphere (f₂ := fun _ : ℂ => Real.posLog |r|) ?_]
  · exact circleAverage_const _ _ _
  · intro x hx
    rw [mem_sphere_iff_norm, sub_zero] at hx
    simp only [hx]

set_option maxHeartbeats 1000000 in
/-- **The wild branch bounds the characteristic by a logarithmic-derivative proximity.** -/
theorem characteristic_le_logDeriv_of_wild {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (horder : ∀ z : ℂ, meromorphicOrderAt f z ≠ ⊤)
    {m : ℕ} (hm : 1 ≤ m) {c R₂ : ℝ} (hc : 0 < c) (hR₂ : 1 ≤ R₂)
    (hwild : ∀ z : ℂ, R₂ ≤ ‖f z‖ → c * ‖f z‖ ^ (m + 1) ≤ ‖z * deriv f z‖ ^ m)
    {r : ℝ} (hr : 1 ≤ r) :
    characteristic f ⊤ r
      ≤ (m : ℝ) * proximity (fun z => deriv f z / f z) ⊤ r
        + (m : ℝ) * Real.log r + (|Real.log c| + ((m : ℝ) + 1) * Real.log R₂) := by
  classical
  have hr0 : (0 : ℝ) < r := by linarith
  have hrne : r ≠ 0 := ne_of_gt hr0
  set E₀ : ℝ := |Real.log c| + ((m : ℝ) + 1) * Real.log R₂ with hE₀
  have hlogR₂ : 0 ≤ Real.log R₂ := Real.log_nonneg hR₂
  -- the pointwise inequality
  have hpt : ∀ z : ℂ, ((m : ℝ) + 1) * Real.posLog ‖f z‖
      ≤ (m : ℝ) * Real.posLog ‖z * deriv f z‖ + E₀ := by
    intro z
    have hnn : 0 ≤ Real.posLog ‖z * deriv f z‖ := Real.posLog_nonneg
    rcases le_or_gt R₂ ‖f z‖ with hbig | hsmall
    · have hfpos : (0 : ℝ) < ‖f z‖ := by linarith
      have hw := hwild z hbig
      have hwpos : (0 : ℝ) < c * ‖f z‖ ^ (m + 1) := by positivity
      have hWpos : (0 : ℝ) < ‖z * deriv f z‖ ^ m := lt_of_lt_of_le hwpos hw
      have hWnorm : (0 : ℝ) < ‖z * deriv f z‖ := by
        by_contra hcon
        push Not at hcon
        have : ‖z * deriv f z‖ = 0 := le_antisymm hcon (norm_nonneg _)
        rw [this, zero_pow (by omega)] at hWpos
        exact lt_irrefl 0 hWpos
      have hlog := Real.log_le_log hwpos hw
      rw [Real.log_mul (ne_of_gt hc) (by positivity), Real.log_pow, Real.log_pow] at hlog
      have hfL : Real.log ‖f z‖ = Real.posLog ‖f z‖ := by
        refine (Real.posLog_eq_log ?_).symm
        rw [abs_of_pos hfpos]
        linarith
      have hWL : Real.log ‖z * deriv f z‖ ≤ Real.posLog ‖z * deriv f z‖ := by
        rw [Real.posLog_apply]
        exact le_max_right _ _
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hcast, hfL] at hlog
      have hlogc : -|Real.log c| ≤ Real.log c := neg_abs_le _
      nlinarith [hlog, hWL, hlogc, hlogR₂, hnn]
    · have hfL : Real.posLog ‖f z‖ ≤ Real.log R₂ := by
        refine le_trans (Real.posLog_le_posLog (norm_nonneg _) hsmall.le) ?_
        exact le_of_eq (Real.posLog_eq_log (by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ R₂)]; exact hR₂))
      have habs : (0 : ℝ) ≤ |Real.log c| := abs_nonneg _
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      rw [hE₀]
      nlinarith [hfL, hnn, habs, hm0]
  -- integrate
  have hintf : CircleIntegrable (fun z : ℂ => Real.posLog ‖f z‖) 0 r :=
    ((Real.continuous_posLog.comp (continuous_norm.comp hf.continuous)).comp
      (continuous_circleMap 0 r)).intervalIntegrable 0 (2 * Real.pi)
  have hcontW : Continuous fun z : ℂ => z * deriv f z := continuous_id.mul hf.deriv.continuous
  have hintW : CircleIntegrable (fun z : ℂ => Real.posLog ‖z * deriv f z‖) 0 r :=
    ((Real.continuous_posLog.comp (continuous_norm.comp hcontW)).comp
      (continuous_circleMap 0 r)).intervalIntegrable 0 (2 * Real.pi)
  have hcm : CircleIntegrable (fun z : ℂ => ((m : ℝ) + 1) * Real.posLog ‖f z‖) 0 r :=
    hintf.const_mul _
  have hcW : CircleIntegrable (fun z : ℂ => (m : ℝ) * Real.posLog ‖z * deriv f z‖) 0 r :=
    hintW.const_mul _
  have hmono : circleAverage (fun z : ℂ => ((m : ℝ) + 1) * Real.posLog ‖f z‖) 0 r
      ≤ circleAverage (fun z : ℂ => (m : ℝ) * Real.posLog ‖z * deriv f z‖ + E₀) 0 r :=
    circleAverage_mono hcm (hcW.add (circleIntegrable_const E₀ 0 r)) (fun x _ => hpt x)
  have hA1 : circleAverage (fun z : ℂ => ((m : ℝ) + 1) * Real.posLog ‖f z‖) 0 r
      = ((m : ℝ) + 1) * proximity f ⊤ r := by
    rw [ValueDistribution.proximity_top]
    simpa [smul_eq_mul] using
      circleAverage_fun_smul (a := ((m : ℝ) + 1)) (f := fun z : ℂ => Real.posLog ‖f z‖)
        (c := (0 : ℂ)) (R := r)
  have hA2 : circleAverage (fun z : ℂ => (m : ℝ) * Real.posLog ‖z * deriv f z‖ + E₀) 0 r
      = (m : ℝ) * proximity (fun z : ℂ => z * deriv f z) ⊤ r + E₀ := by
    rw [circleAverage_fun_add hcW (circleIntegrable_const E₀ 0 r), circleAverage_const,
      ValueDistribution.proximity_top]
    congr 1
    simpa [smul_eq_mul] using
      circleAverage_fun_smul (a := (m : ℝ)) (f := fun z : ℂ => Real.posLog ‖z * deriv f z‖)
        (c := (0 : ℂ)) (R := r)
  rw [hA1, hA2] at hmono
  -- split the product and the derivative
  have hmW : Meromorphic (fun z : ℂ => z * deriv f z) := by
    intro z
    exact (analyticAt_id.meromorphicAt).mul ((hf.deriv.analyticAt z).meromorphicAt)
  have hsplit : proximity (fun z : ℂ => z * deriv f z) ⊤ r
      ≤ proximity (fun z : ℂ => z) ⊤ r + proximity (deriv f) ⊤ r := by
    have := ValueDistribution.proximity_mul_top_le
      (f₁ := fun z : ℂ => z) (f₂ := deriv f)
      (fun z => analyticAt_id.meromorphicAt) (fun z => (hf.deriv.analyticAt z).meromorphicAt)
    exact this r
  have hderiv : proximity (deriv f) ⊤ r
      ≤ proximity f ⊤ r + proximity (fun z => deriv f z / f z) ⊤ r :=
    proximity_deriv_le_add_logDeriv hf hrne (fun u _ => horder u)
  have hid : proximity (fun z : ℂ => z) ⊤ r = Real.log r := by
    rw [proximity_id_eq r, abs_of_pos hr0]
    exact Real.posLog_eq_log (by rw [abs_of_pos hr0]; exact hr)
  have hchar : proximity f ⊤ r = characteristic f ⊤ r := by
    rw [GaloisForLFunctions.Nevanlinna.characteristic_top_eq_proximity_of_analyticOnNhd
      (fun z _ => hf.analyticAt z)]
  rw [hid] at hsplit
  rw [hchar] at hderiv
  rw [hchar] at hmono
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  nlinarith [hmono, hsplit, hderiv, hm1]

set_option maxHeartbeats 1000000 in
/-- **The wild branch, with the logarithmic derivative taken at a shift.**  Replacing `f` by `f − a`
in the denominator costs one constant and lets the estimate be applied where the shifted function
does not vanish. -/
theorem characteristic_le_logDeriv_shift_of_wild {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ)
    (horder : ∀ z : ℂ, meromorphicOrderAt (fun w => f w - a) z ≠ ⊤)
    {m : ℕ} (hm : 1 ≤ m) {c R₂ : ℝ} (hc : 0 < c) (hR₂ : 1 ≤ R₂)
    (hwild : ∀ z : ℂ, R₂ ≤ ‖f z‖ → c * ‖f z‖ ^ (m + 1) ≤ ‖z * deriv f z‖ ^ m)
    {r : ℝ} (hr : 1 ≤ r) :
    characteristic f ⊤ r
      ≤ (m : ℝ) * proximity (fun z => deriv f z / (f z - a)) ⊤ r
        + (m : ℝ) * Real.log r
        + ((|Real.log c| + ((m : ℝ) + 1) * Real.log R₂)
          + (m : ℝ) * (Real.posLog ‖a‖ + Real.log 2)) := by
  classical
  have hr0 : (0 : ℝ) < r := by linarith
  have hrne : r ≠ 0 := ne_of_gt hr0
  set E₀ : ℝ := |Real.log c| + ((m : ℝ) + 1) * Real.log R₂ with hE₀
  have hlogR₂ : 0 ≤ Real.log R₂ := Real.log_nonneg hR₂
  -- the pointwise inequality
  have hpt : ∀ z : ℂ, ((m : ℝ) + 1) * Real.posLog ‖f z‖
      ≤ (m : ℝ) * Real.posLog ‖z * deriv f z‖ + E₀ := by
    intro z
    have hnn : 0 ≤ Real.posLog ‖z * deriv f z‖ := Real.posLog_nonneg
    rcases le_or_gt R₂ ‖f z‖ with hbig | hsmall
    · have hfpos : (0 : ℝ) < ‖f z‖ := by linarith
      have hw := hwild z hbig
      have hwpos : (0 : ℝ) < c * ‖f z‖ ^ (m + 1) := by positivity
      have hWpos : (0 : ℝ) < ‖z * deriv f z‖ ^ m := lt_of_lt_of_le hwpos hw
      have hWnorm : (0 : ℝ) < ‖z * deriv f z‖ := by
        by_contra hcon
        push Not at hcon
        have : ‖z * deriv f z‖ = 0 := le_antisymm hcon (norm_nonneg _)
        rw [this, zero_pow (by omega)] at hWpos
        exact lt_irrefl 0 hWpos
      have hlog := Real.log_le_log hwpos hw
      rw [Real.log_mul (ne_of_gt hc) (by positivity), Real.log_pow, Real.log_pow] at hlog
      have hfL : Real.log ‖f z‖ = Real.posLog ‖f z‖ := by
        refine (Real.posLog_eq_log ?_).symm
        rw [abs_of_pos hfpos]
        linarith
      have hWL : Real.log ‖z * deriv f z‖ ≤ Real.posLog ‖z * deriv f z‖ := by
        rw [Real.posLog_apply]
        exact le_max_right _ _
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hcast, hfL] at hlog
      have hlogc : -|Real.log c| ≤ Real.log c := neg_abs_le _
      nlinarith [hlog, hWL, hlogc, hlogR₂, hnn]
    · have hfL : Real.posLog ‖f z‖ ≤ Real.log R₂ := by
        refine le_trans (Real.posLog_le_posLog (norm_nonneg _) hsmall.le) ?_
        exact le_of_eq (Real.posLog_eq_log (by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ R₂)]; exact hR₂))
      have habs : (0 : ℝ) ≤ |Real.log c| := abs_nonneg _
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      rw [hE₀]
      nlinarith [hfL, hnn, habs, hm0]
  -- integrate
  have hintf : CircleIntegrable (fun z : ℂ => Real.posLog ‖f z‖) 0 r :=
    ((Real.continuous_posLog.comp (continuous_norm.comp hf.continuous)).comp
      (continuous_circleMap 0 r)).intervalIntegrable 0 (2 * Real.pi)
  have hcontW : Continuous fun z : ℂ => z * deriv f z := continuous_id.mul hf.deriv.continuous
  have hintW : CircleIntegrable (fun z : ℂ => Real.posLog ‖z * deriv f z‖) 0 r :=
    ((Real.continuous_posLog.comp (continuous_norm.comp hcontW)).comp
      (continuous_circleMap 0 r)).intervalIntegrable 0 (2 * Real.pi)
  have hcm : CircleIntegrable (fun z : ℂ => ((m : ℝ) + 1) * Real.posLog ‖f z‖) 0 r :=
    hintf.const_mul _
  have hcW : CircleIntegrable (fun z : ℂ => (m : ℝ) * Real.posLog ‖z * deriv f z‖) 0 r :=
    hintW.const_mul _
  have hmono : circleAverage (fun z : ℂ => ((m : ℝ) + 1) * Real.posLog ‖f z‖) 0 r
      ≤ circleAverage (fun z : ℂ => (m : ℝ) * Real.posLog ‖z * deriv f z‖ + E₀) 0 r :=
    circleAverage_mono hcm (hcW.add (circleIntegrable_const E₀ 0 r)) (fun x _ => hpt x)
  have hA1 : circleAverage (fun z : ℂ => ((m : ℝ) + 1) * Real.posLog ‖f z‖) 0 r
      = ((m : ℝ) + 1) * proximity f ⊤ r := by
    rw [ValueDistribution.proximity_top]
    simpa [smul_eq_mul] using
      circleAverage_fun_smul (a := ((m : ℝ) + 1)) (f := fun z : ℂ => Real.posLog ‖f z‖)
        (c := (0 : ℂ)) (R := r)
  have hA2 : circleAverage (fun z : ℂ => (m : ℝ) * Real.posLog ‖z * deriv f z‖ + E₀) 0 r
      = (m : ℝ) * proximity (fun z : ℂ => z * deriv f z) ⊤ r + E₀ := by
    rw [circleAverage_fun_add hcW (circleIntegrable_const E₀ 0 r), circleAverage_const,
      ValueDistribution.proximity_top]
    congr 1
    simpa [smul_eq_mul] using
      circleAverage_fun_smul (a := (m : ℝ)) (f := fun z : ℂ => Real.posLog ‖z * deriv f z‖)
        (c := (0 : ℂ)) (R := r)
  rw [hA1, hA2] at hmono
  -- split the product and the derivative
  have hmW : Meromorphic (fun z : ℂ => z * deriv f z) := by
    intro z
    exact (analyticAt_id.meromorphicAt).mul ((hf.deriv.analyticAt z).meromorphicAt)
  have hsplit : proximity (fun z : ℂ => z * deriv f z) ⊤ r
      ≤ proximity (fun z : ℂ => z) ⊤ r + proximity (deriv f) ⊤ r := by
    have := ValueDistribution.proximity_mul_top_le
      (f₁ := fun z : ℂ => z) (f₂ := deriv f)
      (fun z => analyticAt_id.meromorphicAt) (fun z => (hf.deriv.analyticAt z).meromorphicAt)
    exact this r
  have hderivfun : deriv (fun w => f w - a) = deriv f := by
    funext w
    exact deriv_sub_const a
  have hderiv0 := proximity_deriv_le_add_logDeriv (hf.sub_const a) hrne (fun u _ => horder u)
  rw [hderivfun] at hderiv0
  have hshift : proximity (fun w => f w - a) ⊤ r
      ≤ proximity f ⊤ r + (Real.posLog ‖a‖ + Real.log 2) := by
    have hsub := characteristic_sub_const_le hf a r
    rw [← GaloisForLFunctions.Nevanlinna.characteristic_top_eq_proximity_of_analyticOnNhd
        (fun z _ => (hf.sub_const a).analyticAt z),
      ← GaloisForLFunctions.Nevanlinna.characteristic_top_eq_proximity_of_analyticOnNhd
        (fun z _ => hf.analyticAt z)]
    exact hsub
  have hderiv : proximity (deriv f) ⊤ r
      ≤ proximity f ⊤ r + (Real.posLog ‖a‖ + Real.log 2)
        + proximity (fun z => deriv f z / (f z - a)) ⊤ r := by
    linarith [hderiv0, hshift]
  have hid : proximity (fun z : ℂ => z) ⊤ r = Real.log r := by
    rw [proximity_id_eq r, abs_of_pos hr0]
    exact Real.posLog_eq_log (by rw [abs_of_pos hr0]; exact hr)
  have hchar : proximity f ⊤ r = characteristic f ⊤ r := by
    rw [GaloisForLFunctions.Nevanlinna.characteristic_top_eq_proximity_of_analyticOnNhd
      (fun z _ => hf.analyticAt z)]
  rw [hid] at hsplit
  rw [hchar] at hderiv
  rw [hchar] at hmono
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  nlinarith [hmono, hsplit, hderiv, hm1]

end GaloisForLFunctions.HTGeometry
