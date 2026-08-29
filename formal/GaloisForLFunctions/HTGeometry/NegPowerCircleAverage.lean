import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Circle averages of negative powers of the distance to a point

For `0 < α < 1` the average of `‖r e^{iθ} − u‖^{-α}` over the circle of radius `r` is at most a
constant multiple of `r^{-α}`, *uniformly in the point `u`*.  The mechanism is the elementary
inequality

```text
‖r e^{iθ} − u‖ ≥ r · |sin(θ − arg u)|,
```

which says that the distance from a point of the circle to `u` is at least its distance to the line
through `0` and `u`, together with the integrability of `|sin|^{-α}`.

This uniform bound is what makes the sum over an entire divisor affordable in Nevanlinna's estimate
for the proximity of a logarithmic derivative: each of the `n(R)` divisor terms costs a fixed
constant in the `α`-th power average, so the resulting logarithm costs only `log n(R)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Real MeasureTheory intervalIntegral

/-! ## Integrability of a negative power of `|sin|` -/

theorem measurable_abs_sin_rpow_neg (α : ℝ) :
    Measurable fun θ : ℝ => |Real.sin θ| ^ (-α) :=
  (Real.continuous_sin.abs.measurable).pow_const _

/-- On `[0, π/2]` the negative power of `|sin|` is dominated by the same power of the argument. -/
theorem abs_sin_rpow_neg_le_of_mem_left {α : ℝ} (hα0 : 0 < α) {θ : ℝ}
    (h0 : 0 < θ) (h1 : θ ≤ π / 2) :
    |Real.sin θ| ^ (-α) ≤ (2 / π) ^ (-α) * θ ^ (-α) := by
  have hπ : 0 < π := Real.pi_pos
  have hlow : 2 / π * θ ≤ Real.sin θ := Real.mul_le_sin h0.le h1
  have hpos : 0 < 2 / π * θ := by positivity
  have hsin : 0 < Real.sin θ := lt_of_lt_of_le hpos hlow
  have habs : |Real.sin θ| = Real.sin θ := abs_of_pos hsin
  rw [habs]
  have hstep : Real.sin θ ^ (-α) ≤ (2 / π * θ) ^ (-α) := by
    refine Real.rpow_le_rpow_of_nonpos hpos hlow (by linarith)
  calc Real.sin θ ^ (-α) ≤ (2 / π * θ) ^ (-α) := hstep
    _ = (2 / π) ^ (-α) * θ ^ (-α) := by
        rw [Real.mul_rpow (by positivity) h0.le]

theorem intervalIntegrable_abs_sin_rpow_neg_left {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IntervalIntegrable (fun θ => |Real.sin θ| ^ (-α)) volume 0 (π / 2) := by
  have hπ : 0 < π := Real.pi_pos
  have hdom : IntervalIntegrable (fun θ : ℝ => (2 / π) ^ (-α) * θ ^ (-α)) volume 0 (π / 2) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _
  refine IntervalIntegrable.mono_fun' hdom
    ((measurable_abs_sin_rpow_neg α).aestronglyMeasurable.restrict) ?_
  have hae : ∀ᵐ θ : ℝ ∂(volume.restrict (Set.uIoc 0 (π / 2))),
      ‖|Real.sin θ| ^ (-α)‖ ≤ (2 / π) ^ (-α) * θ ^ (-α) := by
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc fun θ hθ => ?_
    rw [Set.uIoc_of_le (by positivity)] at hθ
    have h0 : 0 < θ := hθ.1
    have h1 : θ ≤ π / 2 := hθ.2
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact abs_sin_rpow_neg_le_of_mem_left hα0 h0 h1
  exact hae

theorem intervalIntegrable_abs_sin_rpow_neg_right {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IntervalIntegrable (fun θ => |Real.sin θ| ^ (-α)) volume (π / 2) π := by
  have hbase := intervalIntegrable_abs_sin_rpow_neg_left hα0 hα1
  have hcomp := hbase.comp_sub_left π
  have hfun : (fun θ : ℝ => |Real.sin (π - θ)| ^ (-α)) = fun θ : ℝ => |Real.sin θ| ^ (-α) := by
    funext θ
    rw [Real.sin_pi_sub]
  rw [hfun] at hcomp
  have hleft : π - π / 2 = π / 2 := by ring
  have hright : π - 0 = π := by ring
  rw [hleft, hright] at hcomp
  exact hcomp.symm

theorem intervalIntegrable_abs_sin_rpow_neg_pi {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IntervalIntegrable (fun θ => |Real.sin θ| ^ (-α)) volume 0 π :=
  (intervalIntegrable_abs_sin_rpow_neg_left hα0 hα1).trans
    (intervalIntegrable_abs_sin_rpow_neg_right hα0 hα1)

theorem intervalIntegrable_abs_sin_rpow_neg_two_pi {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IntervalIntegrable (fun θ => |Real.sin θ| ^ (-α)) volume 0 (2 * π) := by
  have hbase := intervalIntegrable_abs_sin_rpow_neg_pi hα0 hα1
  have hcomp := hbase.comp_sub_right π
  have hfun : (fun θ : ℝ => |Real.sin (θ - π)| ^ (-α)) = fun θ : ℝ => |Real.sin θ| ^ (-α) := by
    funext θ
    rw [Real.sin_sub_pi, abs_neg]
  rw [hfun] at hcomp
  have hleft : (0 : ℝ) + π = π := by ring
  have hright : π + π = 2 * π := by ring
  rw [hleft, hright] at hcomp
  exact hbase.trans hcomp

/-- The finite constant `∫_0^{2π} |sin θ|^{-α} dθ`. -/
noncomputable def sinNegPowerConst (α : ℝ) : ℝ := ∫ θ in (0 : ℝ)..(2 * π), |Real.sin θ| ^ (-α)

theorem sinNegPowerConst_nonneg (α : ℝ) : 0 ≤ sinNegPowerConst α := by
  rw [sinNegPowerConst]
  refine intervalIntegral.integral_nonneg (by positivity) fun θ _ => ?_
  positivity

/-- The `|sin|` integral is translation invariant: `|sin|` is `π`-periodic, hence `2π`-periodic. -/
theorem integral_abs_sin_rpow_neg_shift {α : ℝ} (φ : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * π), |Real.sin (θ - φ)| ^ (-α) = sinNegPowerConst α := by
  have hper : Function.Periodic (fun θ : ℝ => |Real.sin θ| ^ (-α)) (2 * π) := fun θ => by
    show |Real.sin (θ + 2 * π)| ^ (-α) = |Real.sin θ| ^ (-α)
    rw [Real.sin_add_two_pi]
  rw [intervalIntegral.integral_comp_sub_right (fun θ => |Real.sin θ| ^ (-α)) φ]
  have h := Function.Periodic.intervalIntegral_add_eq hper (0 - φ) 0
  rw [sinNegPowerConst, show (2 : ℝ) * π - φ = 0 - φ + 2 * π by ring, h]
  norm_num

/-! ## The geometric lower bound on the circle -/

/-- **The distance from a circle point to `u` is at least its distance to the line through `u`.** -/
theorem norm_circle_sub_ge (r : ℝ) (hr : 0 ≤ r) (u : ℂ) (θ : ℝ) :
    r * |Real.sin (θ - u.arg)| ≤ ‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖ := by
  set φ : ℝ := u.arg with hφ
  set ρ : ℝ := ‖u‖ with hρ
  have hu : (ρ : ℂ) * Complex.exp ((φ : ℝ) * Complex.I) = u := Complex.norm_mul_exp_arg_mul_I u
  have hexp : Complex.exp ((φ : ℝ) * Complex.I) * Complex.exp (((θ - φ : ℝ)) * Complex.I)
      = Complex.exp ((θ : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hrot : (r : ℂ) * Complex.exp ((θ : ℝ) * Complex.I) - u
      = Complex.exp ((φ : ℝ) * Complex.I)
        * ((r : ℂ) * Complex.exp (((θ - φ : ℝ)) * Complex.I) - (ρ : ℂ)) := by
    rw [← hu, mul_sub]
    rw [show Complex.exp ((φ : ℝ) * Complex.I) * ((r : ℂ) * Complex.exp (((θ - φ : ℝ)) * Complex.I))
        = (r : ℂ) * (Complex.exp ((φ : ℝ) * Complex.I)
          * Complex.exp (((θ - φ : ℝ)) * Complex.I)) from by ring]
    rw [hexp]
    ring
  have hre : (((φ : ℝ) : ℂ) * Complex.I).re = 0 := by simp
  have him : ((r : ℂ) * Complex.exp (((θ - φ : ℝ)) * Complex.I) - (ρ : ℂ)).im
      = r * Real.sin (θ - φ) := by
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Complex.exp_ofReal_mul_I_im]
  have hle := Complex.abs_im_le_norm
    ((r : ℂ) * Complex.exp (((θ - φ : ℝ)) * Complex.I) - (ρ : ℂ))
  rw [him] at hle
  rw [hrot, norm_mul, Complex.norm_exp, hre, Real.exp_zero, one_mul]
  calc r * |Real.sin (θ - φ)| = |r * Real.sin (θ - φ)| := by
        rw [abs_mul, abs_of_nonneg hr]
    _ ≤ _ := hle


/-- Periodicity extends the integrability of `|sin|^{-α}` to every interval. -/
theorem intervalIntegrable_abs_sin_rpow_neg {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (a b : ℝ) :
    IntervalIntegrable (fun θ => |Real.sin θ| ^ (-α)) volume a b := by
  have hper : Function.Periodic (fun θ : ℝ => |Real.sin θ| ^ (-α)) (2 * π) := fun θ => by
    show |Real.sin (θ + 2 * π)| ^ (-α) = |Real.sin θ| ^ (-α)
    rw [Real.sin_add_two_pi]
  exact Function.Periodic.intervalIntegrable₀ hper (by positivity)
    (intervalIntegrable_abs_sin_rpow_neg_two_pi hα0 hα1) a b

/-- The zero set of a shifted sine is countable, hence null. -/
theorem countable_sin_shift_eq_zero (φ : ℝ) : {θ : ℝ | Real.sin (θ - φ) = 0}.Countable := by
  have hsub : {θ : ℝ | Real.sin (θ - φ) = 0} ⊆ Set.range (fun n : ℤ => φ + (n : ℝ) * π) := by
    intro θ hθ
    rw [Set.mem_setOf_eq, Real.sin_eq_zero_iff] at hθ
    obtain ⟨n, hn⟩ := hθ
    exact ⟨n, by linarith [hn]⟩
  exact Set.Countable.mono hsub (Set.countable_range _)

/-- The `α`-power kernel is interval-integrable on the circle, and bounded by the shifted sine
majorant. -/
theorem circle_rpow_neg_aux {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {r : ℝ} (hr : 0 < r) (u : ℂ) :
    IntervalIntegrable (fun θ => ‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖ ^ (-α)) volume 0
        (2 * π) ∧
      (fun θ : ℝ => ‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖ ^ (-α))
        ≤ᵐ[volume] fun θ : ℝ => r ^ (-α) * |Real.sin (θ - u.arg)| ^ (-α) := by
  set φ : ℝ := u.arg with hφ
  set F : ℝ → ℝ := fun θ => ‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖ ^ (-α) with hF
  set g : ℝ → ℝ := fun θ => r ^ (-α) * |Real.sin (θ - φ)| ^ (-α) with hg
  have hgint : IntervalIntegrable g volume 0 (2 * π) := by
    have h := (intervalIntegrable_abs_sin_rpow_neg hα0 hα1 (0 - φ) (2 * π - φ)).comp_sub_right φ
    simp only [sub_add_cancel] at h
    exact h.const_mul _
  have hFmeas : Measurable F := by
    refine Measurable.pow_const ?_ _
    refine (Continuous.norm ?_).measurable
    fun_prop
  have hpt : ∀ θ : ℝ, Real.sin (θ - φ) ≠ 0 → F θ ≤ g θ := by
    intro θ hθ
    have habs : 0 < |Real.sin (θ - φ)| := abs_pos.mpr hθ
    have hlow : 0 < r * |Real.sin (θ - φ)| := by positivity
    have hge : r * |Real.sin (θ - φ)| ≤ ‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖ :=
      norm_circle_sub_ge r hr.le u θ
    have hstep : ‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖ ^ (-α)
        ≤ (r * |Real.sin (θ - φ)|) ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos hlow hge (by linarith)
    rw [hF, hg]
    calc ‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖ ^ (-α)
        ≤ (r * |Real.sin (θ - φ)|) ^ (-α) := hstep
      _ = r ^ (-α) * |Real.sin (θ - φ)| ^ (-α) := Real.mul_rpow hr.le (abs_nonneg _)
  have hnull : (volume : Measure ℝ) {θ : ℝ | Real.sin (θ - φ) = 0} = 0 :=
    (countable_sin_shift_eq_zero φ).measure_zero volume
  have haeglobal : F ≤ᵐ[volume] g := by
    have hcompl : ∀ᵐ θ : ℝ, Real.sin (θ - φ) ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simpa using hnull
    filter_upwards [hcompl] with θ hθ
    exact hpt θ hθ
  have hFint : IntervalIntegrable F volume 0 (2 * π) := by
    refine IntervalIntegrable.mono_fun' hgint hFmeas.aestronglyMeasurable.restrict ?_
    filter_upwards [MeasureTheory.ae_restrict_of_ae haeglobal] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact hθ
  exact ⟨hFint, haeglobal⟩

theorem intervalIntegrable_norm_circle_sub_rpow_neg {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {r : ℝ} (hr : 0 < r) (u : ℂ) :
    IntervalIntegrable (fun θ => ‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖ ^ (-α)) volume 0
      (2 * π) := (circle_rpow_neg_aux hα0 hα1 hr u).1

/-- **The uniform circle bound.**  The integral of `‖r e^{iθ} − u‖^{-α}` over the full circle is at
most `r^{-α}` times a constant depending only on `α` — in particular not on `u`. -/
theorem intervalIntegral_norm_circle_sub_rpow_neg_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {r : ℝ} (hr : 0 < r) (u : ℂ) :
    ∫ θ in (0 : ℝ)..(2 * π), ‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖ ^ (-α)
      ≤ r ^ (-α) * sinNegPowerConst α := by
  obtain ⟨hFint, haeglobal⟩ := circle_rpow_neg_aux hα0 hα1 hr u
  have hgint : IntervalIntegrable
      (fun θ => r ^ (-α) * |Real.sin (θ - u.arg)| ^ (-α)) volume 0 (2 * π) := by
    have h := (intervalIntegrable_abs_sin_rpow_neg hα0 hα1 (0 - u.arg)
      (2 * π - u.arg)).comp_sub_right u.arg
    simp only [sub_add_cancel] at h
    exact h.const_mul _
  have hgval : ∫ θ in (0 : ℝ)..(2 * π), r ^ (-α) * |Real.sin (θ - u.arg)| ^ (-α)
      = r ^ (-α) * sinNegPowerConst α := by
    rw [intervalIntegral.integral_const_mul, integral_abs_sin_rpow_neg_shift]
  have hmono := intervalIntegral.integral_mono_ae (by positivity : (0 : ℝ) ≤ 2 * π) hFint hgint
    haeglobal
  rw [hgval] at hmono
  exact hmono

/-- **Subadditivity of the `α`-th power over a finite sum**, for `0 ≤ α ≤ 1`. -/
theorem rpow_sum_le_sum_rpow {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (∑ i ∈ s, f i) ^ α ≤ ∑ i ∈ s, (f i) ^ α := by
  classical
  induction s using Finset.induction with
  | empty => simp [Real.zero_rpow (ne_of_gt hα0)]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hsum : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg hfs
      calc (f a + ∑ i ∈ s, f i) ^ α ≤ (f a) ^ α + (∑ i ∈ s, f i) ^ α :=
            Real.rpow_add_le_add_rpow hfa hsum hα0.le hα1
        _ ≤ (f a) ^ α + ∑ i ∈ s, (f i) ^ α := by
            have := ih hfs
            linarith


/-- `(x⁻¹)^α = x^{-α}` for `x ≥ 0`. -/
theorem inv_rpow_eq_rpow_neg {x : ℝ} (hx : 0 ≤ x) (α : ℝ) : (x⁻¹) ^ α = x ^ (-α) := by
  rw [Real.inv_rpow hx, Real.rpow_neg hx]

/-- **The `α`-power average of a divisor-kernel sum.**  Each divisor point contributes a fixed
constant, uniformly in its position, so the whole sum contributes only its total `α`-power weight. -/
theorem intervalIntegral_kernelSum_rpow_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {r Rr : ℝ} (hr : 0 < r) (hRr : 0 < Rr)
    (S : Finset ℂ) (m : ℂ → ℝ) (hm : ∀ u ∈ S, 0 ≤ m u) :
    ∫ θ in (0 : ℝ)..(2 * π),
        (∑ u ∈ S, m u * (‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖⁻¹ + Rr⁻¹)) ^ α
      ≤ (∑ u ∈ S, (m u) ^ α) * (r ^ (-α) * sinNegPowerConst α + 2 * π * Rr ^ (-α)) := by
  classical
  set F : ℝ → ℝ := fun θ =>
    (∑ u ∈ S, m u * (‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖⁻¹ + Rr⁻¹)) ^ α with hF
  set G : ℝ → ℝ := fun θ =>
    ∑ u ∈ S, (m u) ^ α * (‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖ ^ (-α) + Rr ^ (-α))
    with hG
  -- pointwise domination
  have hpt : ∀ θ : ℝ, F θ ≤ G θ := by
    intro θ
    have hterm0 : ∀ u ∈ S, 0 ≤ m u * (‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖⁻¹ + Rr⁻¹) := by
      intro u hu
      have h1 : 0 ≤ ‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖⁻¹ := by positivity
      have h2 : 0 ≤ Rr⁻¹ := by positivity
      exact mul_nonneg (hm u hu) (by linarith)
    refine le_trans (rpow_sum_le_sum_rpow S _ hterm0 hα0 hα1.le) ?_
    refine Finset.sum_le_sum fun u hu => ?_
    have hnn : (0 : ℝ) ≤ ‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖⁻¹ := by positivity
    have hRinv : (0 : ℝ) ≤ Rr⁻¹ := by positivity
    rw [Real.mul_rpow (hm u hu) (by linarith)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (hm u hu) α)
    refine le_trans (Real.rpow_add_le_add_rpow hnn hRinv hα0.le hα1.le) ?_
    rw [inv_rpow_eq_rpow_neg (norm_nonneg _), inv_rpow_eq_rpow_neg hRr.le]
  -- integrability
  have hGterm : ∀ u ∈ S, IntervalIntegrable
      (fun θ : ℝ => (m u) ^ α * (‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖ ^ (-α) + Rr ^ (-α)))
      volume 0 (2 * π) := fun u _ =>
    ((intervalIntegrable_norm_circle_sub_rpow_neg hα0 hα1 hr u).add
      intervalIntegrable_const).const_mul _
  have hGint : IntervalIntegrable G volume 0 (2 * π) := by
    have h := IntervalIntegrable.sum S hGterm
    have heq : (∑ i ∈ S, fun θ : ℝ => (m i) ^ α
        * (‖(r : ℂ) * Complex.exp (θ * Complex.I) - i‖ ^ (-α) + Rr ^ (-α))) = G := by
      funext θ
      rw [hG]
      simp [Finset.sum_apply]
    rwa [heq] at h
  have hFmeas : Measurable F := by
    rw [hF]
    refine Measurable.pow_const ?_ _
    refine Finset.measurable_sum _ fun u _ => ?_
    refine Measurable.const_mul ?_ _
    refine Measurable.add ?_ measurable_const
    exact ((Continuous.norm (by fun_prop)).measurable).inv
  have hFint : IntervalIntegrable F volume 0 (2 * π) := by
    refine IntervalIntegrable.mono_fun' hGint hFmeas.aestronglyMeasurable.restrict ?_
    refine MeasureTheory.ae_restrict_of_ae (Filter.Eventually.of_forall fun θ => ?_)
    have h0 : 0 ≤ F θ := by
      rw [hF]
      exact Real.rpow_nonneg (Finset.sum_nonneg fun u hu => by
        have h1 : 0 ≤ ‖(r : ℂ) * Complex.exp (θ * Complex.I) - u‖⁻¹ := by positivity
        have h2 : (0 : ℝ) ≤ Rr⁻¹ := by positivity
        exact mul_nonneg (hm u hu) (by linarith)) α
    show ‖F θ‖ ≤ G θ
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact hpt θ
  -- integrate
  have hmono := intervalIntegral.integral_mono_ae (by positivity : (0 : ℝ) ≤ 2 * π) hFint hGint
    (Filter.Eventually.of_forall hpt)
  refine le_trans hmono ?_
  rw [hG, intervalIntegral.integral_finsetSum hGterm]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun u hu => ?_
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
    (intervalIntegrable_norm_circle_sub_rpow_neg hα0 hα1 hr u) intervalIntegrable_const]
  have hconst : ∫ _θ in (0 : ℝ)..(2 * π), Rr ^ (-α) = 2 * π * Rr ^ (-α) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hconst]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (hm u hu) α)
  have hbase := intervalIntegral_norm_circle_sub_rpow_neg_le hα0 hα1 hr u
  linarith

end GaloisForLFunctions.HTGeometry
