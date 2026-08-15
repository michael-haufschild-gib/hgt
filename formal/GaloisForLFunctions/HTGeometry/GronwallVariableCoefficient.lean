import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Grönwall's inequality with a variable coefficient

The Volterra estimate behind every Liouville--Green error bound is not the constant-coefficient
Grönwall inequality of the ODE library but its integral form with a **variable** weight: a function
obeying

```text
|h(x)| ≤ 1 + ∫_a^x φ(t) |h(t)| dt ,   φ ≥ 0 ,
```

obeys `|h(x)| ≤ exp ∫_a^x φ`, with the total mass of `φ` — not a bound on it times the length of the
interval — in the exponent.  That distinction is the whole content of Olver's error-control
function: the bound is governed by the variation of the control, and stays finite on infinite
intervals where a uniform bound times the length would not.

The proof is the classical one: the accumulated integral `H` satisfies `H' = φ|h| ≤ φ(1+H)`, so
`(1+H) e^{-∫φ}` is nonincreasing and starts at `1`.
-/

open Set intervalIntegral MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- **Grönwall's inequality, integral form, variable coefficient.** -/
theorem abs_le_exp_integral_of_volterra_bound {a b : ℝ} (hab : a ≤ b) {h φ : ℝ → ℝ}
    (hh : Continuous h) (hφ : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hbd : ∀ x ∈ Icc a b, |h x| ≤ 1 + ∫ t in a..x, φ t * |h t|) :
    ∀ x ∈ Icc a b, |h x| ≤ Real.exp (∫ t in a..x, φ t) := by
  have hcont1 : Continuous fun t => φ t * |h t| := hφ.mul hh.abs
  set H : ℝ → ℝ := fun x => ∫ t in a..x, φ t * |h t| with hHdef
  set Φ : ℝ → ℝ := fun x => ∫ t in a..x, φ t with hΦdef
  have hHd : ∀ x : ℝ, HasDerivAt H (φ x * |h x|) x := by
    intro x
    exact intervalIntegral.integral_hasDerivAt_right
      (hcont1.intervalIntegrable a x)
      (hcont1.stronglyMeasurableAtFilter _ _) hcont1.continuousAt
  have hΦd : ∀ x : ℝ, HasDerivAt Φ (φ x) x := by
    intro x
    exact intervalIntegral.integral_hasDerivAt_right
      (hφ.intervalIntegrable a x)
      (hφ.stronglyMeasurableAtFilter _ _) hφ.continuousAt
  set G : ℝ → ℝ := fun x => (1 + H x) * Real.exp (-Φ x) with hGdef
  have hGd : ∀ x : ℝ, HasDerivAt G
      ((φ x * |h x|) * Real.exp (-Φ x) + (1 + H x) * (-(φ x) * Real.exp (-Φ x))) x := by
    intro x
    have h1 : HasDerivAt (fun y => 1 + H y) (φ x * |h x|) x := by
      simpa using (hHd x).const_add 1
    have h2 : HasDerivAt (fun y => Real.exp (-Φ y)) (-(φ x) * Real.exp (-Φ x)) x := by
      have := ((hΦd x).neg).exp
      simpa [mul_comm] using this
    exact h1.mul h2
  have hGdiff : Differentiable ℝ G := fun x => (hGd x).differentiableAt
  have hnonpos : ∀ x ∈ interior (Icc a b), deriv G x ≤ 0 := by
    intro x hx
    have hxmem : x ∈ Icc a b := interior_subset hx
    rw [(hGd x).deriv]
    have hle : |h x| ≤ 1 + H x := hbd x hxmem
    have hmul : φ x * |h x| ≤ φ x * (1 + H x) :=
      mul_le_mul_of_nonneg_left hle (hφ0 x)
    have hexp : (0 : ℝ) < Real.exp (-Φ x) := Real.exp_pos _
    nlinarith [hmul, hexp]
  have hanti : AntitoneOn G (Icc a b) :=
    antitoneOn_of_deriv_nonpos (convex_Icc a b) hGdiff.continuous.continuousOn
      (hGdiff.differentiableOn) hnonpos
  intro x hx
  have hGa : G a = 1 := by
    rw [hGdef, hHdef, hΦdef]
    simp
  have hGle : G x ≤ 1 := by
    rw [← hGa]
    exact hanti (left_mem_Icc.mpr hab) hx hx.1
  have hexp : (0 : ℝ) < Real.exp (-Φ x) := Real.exp_pos _
  have hkey : 1 + H x ≤ Real.exp (Φ x) := by
    have h1 : (1 + H x) * Real.exp (-Φ x) ≤ 1 := hGle
    have h2 : Real.exp (-Φ x) = (Real.exp (Φ x))⁻¹ := by
      rw [Real.exp_neg]
    rw [h2, mul_inv_le_iff₀ (Real.exp_pos _)] at h1
    linarith
  exact le_trans (hbd x hx) hkey


/-- The accumulated integral of a function inside the Grönwall envelope. -/
theorem integral_mul_abs_le_exp_sub_one {a b : ℝ} {h φ : ℝ → ℝ}
    (hh : Continuous h) (hφ : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hle : ∀ x ∈ Icc a b, |h x| ≤ Real.exp (∫ t in a..x, φ t)) :
    ∀ x ∈ Icc a b, ∫ t in a..x, φ t * |h t| ≤ Real.exp (∫ t in a..x, φ t) - 1 := by
  intro x hx
  have hxa : a ≤ x := hx.1
  have hprim : Continuous fun t : ℝ => Real.exp (∫ s in a..t, φ s) :=
    Real.continuous_exp.comp
      (intervalIntegral.continuous_primitive (fun u v => hφ.intervalIntegrable u v) a)
  have hle' : ∫ t in a..x, φ t * |h t| ≤ ∫ t in a..x, φ t * Real.exp (∫ s in a..t, φ s) := by
    refine intervalIntegral.integral_mono_on hxa
      ((hφ.mul hh.abs).intervalIntegrable a x)
      ((hφ.mul hprim).intervalIntegrable a x) fun t ht => ?_
    have htmem : t ∈ Icc a b := ⟨ht.1, le_trans ht.2 hx.2⟩
    exact mul_le_mul_of_nonneg_left (hle t htmem) (hφ0 t)
  have hexact : ∫ t in a..x, φ t * Real.exp (∫ s in a..t, φ s)
      = Real.exp (∫ s in a..x, φ s) - 1 := by
    have hderiv : ∀ t ∈ uIcc a x,
        HasDerivAt (fun y => Real.exp (∫ s in a..y, φ s))
          (φ t * Real.exp (∫ s in a..t, φ s)) t := by
      intro t _
      have hΦd : HasDerivAt (fun y => ∫ s in a..y, φ s) (φ t) t :=
        intervalIntegral.integral_hasDerivAt_right
          (hφ.intervalIntegrable a t)
          (hφ.stronglyMeasurableAtFilter _ _) hφ.continuousAt
      have := hΦd.exp
      simpa [mul_comm] using this
    have hint : IntervalIntegrable
        (fun t => φ t * Real.exp (∫ s in a..t, φ s)) volume a x :=
      (hφ.mul hprim).intervalIntegrable a x
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp
  linarith [hle', hexact.le, hexact.ge]

/-- The error form: the deviation from `1` is bounded by `exp − 1`. -/
theorem abs_sub_one_le_exp_sub_one_of_volterra_bound {a b : ℝ} (hab : a ≤ b) {h φ : ℝ → ℝ}
    (hh : Continuous h) (hφ : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hbd : ∀ x ∈ Icc a b, |h x - 1| ≤ ∫ t in a..x, φ t * |h t|) :
    ∀ x ∈ Icc a b, |h x - 1| ≤ Real.exp (∫ t in a..x, φ t) - 1 := by
  have hbd' : ∀ x ∈ Icc a b, |h x| ≤ 1 + ∫ t in a..x, φ t * |h t| := by
    intro x hx
    have h1 : |h x| - 1 ≤ |h x - 1| := by
      have := abs_sub_abs_le_abs_sub (h x) 1
      simpa using this
    have h2 := hbd x hx
    linarith
  intro x hx
  have hmain := abs_le_exp_integral_of_volterra_bound hab hh hφ hφ0 hbd' x hx
  have hmono : ∫ t in a..x, φ t * |h t| ≤ Real.exp (∫ t in a..x, φ t) - 1 := by
    have hxa : a ≤ x := hx.1
    have hpos : (0 : ℝ) ≤ ∫ t in a..x, φ t * |h t| := by
      refine intervalIntegral.integral_nonneg hxa fun t _ => ?_
      exact mul_nonneg (hφ0 t) (abs_nonneg _)
    have hle : ∫ t in a..x, φ t * |h t| ≤ ∫ t in a..x, φ t * Real.exp (∫ s in a..t, φ s) := by
      refine intervalIntegral.integral_mono_on hxa
        ((hφ.mul hh.abs).intervalIntegrable a x)
        ((hφ.mul (Real.continuous_exp.comp
          (intervalIntegral.continuous_primitive
            (fun u v => hφ.intervalIntegrable u v) a))).intervalIntegrable a x)
        fun t ht => ?_
      have htmem : t ∈ Icc a b := ⟨ht.1, le_trans ht.2 hx.2⟩
      exact mul_le_mul_of_nonneg_left
        (abs_le_exp_integral_of_volterra_bound hab hh hφ hφ0 hbd' t htmem) (hφ0 t)
    have hexact : ∫ t in a..x, φ t * Real.exp (∫ s in a..t, φ s)
        = Real.exp (∫ s in a..x, φ s) - 1 := by
      have hderiv : ∀ t ∈ uIcc a x,
          HasDerivAt (fun y => Real.exp (∫ s in a..y, φ s))
            (φ t * Real.exp (∫ s in a..t, φ s)) t := by
        intro t _
        have hΦd : HasDerivAt (fun y => ∫ s in a..y, φ s) (φ t) t :=
          intervalIntegral.integral_hasDerivAt_right
            (hφ.intervalIntegrable a t)
            (hφ.stronglyMeasurableAtFilter _ _) hφ.continuousAt
        have := hΦd.exp
        simpa [mul_comm] using this
      have hint : IntervalIntegrable
          (fun t => φ t * Real.exp (∫ s in a..t, φ s)) volume a x :=
        (hφ.mul (Real.continuous_exp.comp
          (intervalIntegral.continuous_primitive
            (fun u v => hφ.intervalIntegrable u v) a))).intervalIntegrable a x
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
      simp
    linarith [hle, hexact]
  exact le_trans (hbd x hx) hmono

end GaloisForLFunctions.HTGeometry
