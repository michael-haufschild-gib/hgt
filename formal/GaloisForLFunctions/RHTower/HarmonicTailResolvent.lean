import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The harmonic tail is the exact critical outgoing resolvent

In critical logarithmic normalization the harmonic remainder tail is

`(𝒯r)(h) = -∫_0^∞ e^{-s/2} r(h+s) ds = -e^{h/2} ∫_h^∞ e^{-t/2} r(t) dt`,

and the mass outgoing current is `1/2 − ∂_h`.  Differentiating the tail gives the exact resolvent
equation

`(1/2 − ∂_h) 𝒯 = −I`,

so on the logarithmic frequency `e^{iξh}` the two symbols are `−(1/2 − iξ)^{-1}` and `1/2 − iξ`, and
their product is `−1` at every frequency.  No favourable spectral sector is hidden: any scalar
transform commuting with logarithmic translations and retaining a stable inverse can only
re-coordinate the current.
-/

open MeasureTheory Set Filter Topology intervalIntegral

namespace RHTower

noncomputable section

/-! ## The tail transform -/

/-- The critically weighted tail `∫_h^∞ e^{-t/2} r(t) dt`. -/
def harmonicTailKernel (r : ℝ → ℝ) (h : ℝ) : ℝ := ∫ t in Set.Ioi h, Real.exp (-t / 2) * r t

/-- The harmonic tail transform `(𝒯r)(h) = -e^{h/2} ∫_h^∞ e^{-t/2} r(t) dt`. -/
def harmonicTail (r : ℝ → ℝ) (h : ℝ) : ℝ := -Real.exp (h / 2) * harmonicTailKernel r h

theorem integrableOn_harmonicTailIntegrand {r : ℝ → ℝ} (hr : Continuous r) {C : ℝ}
    (hb : ∀ t, |r t| ≤ C) (c : ℝ) :
    IntegrableOn (fun t => Real.exp (-t / 2) * r t) (Set.Ioi c) := by
  have hCnn : 0 ≤ C := le_trans (abs_nonneg (r 0)) (hb 0)
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t)) (Set.Ioi c) :=
    exp_neg_integrableOn_Ioi c (by norm_num)
  have hdom : IntegrableOn (fun t : ℝ => C * Real.exp (-(1 / 2 : ℝ) * t)) (Set.Ioi c) :=
    hexp.const_mul C
  refine Integrable.mono' hdom ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · filter_upwards with t
    have hexpt : Real.exp (-t / 2) = Real.exp (-(1 / 2 : ℝ) * t) := by
      congr 1
      ring
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _), hexpt, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hb t) (Real.exp_nonneg _)

theorem harmonicTailKernel_eq_sub {r : ℝ → ℝ} (hr : Continuous r) {C : ℝ} (hb : ∀ t, |r t| ≤ C)
    {a h : ℝ} (hah : a ≤ h) :
    harmonicTailKernel r h
      = harmonicTailKernel r a - ∫ t in a..h, Real.exp (-t / 2) * r t := by
  have hIa := integrableOn_harmonicTailIntegrand hr hb a
  have hIh := integrableOn_harmonicTailIntegrand hr hb h
  have hIoc : IntegrableOn (fun t => Real.exp (-t / 2) * r t) (Set.Ioc a h) :=
    hIa.mono_set (Set.Ioc_subset_Ioi_self)
  have hunion : Set.Ioc a h ∪ Set.Ioi h = Set.Ioi a := Set.Ioc_union_Ioi_eq_Ioi hah
  have hdisj : Disjoint (Set.Ioc a h) (Set.Ioi h) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.2 (not_le.2 hx')
  have hsplit : ∫ t in Set.Ioi a, Real.exp (-t / 2) * r t
      = (∫ t in Set.Ioc a h, Real.exp (-t / 2) * r t)
        + ∫ t in Set.Ioi h, Real.exp (-t / 2) * r t := by
    rw [← hunion]
    exact setIntegral_union hdisj measurableSet_Ioi hIoc hIh
  have hinterval : ∫ t in a..h, Real.exp (-t / 2) * r t
      = ∫ t in Set.Ioc a h, Real.exp (-t / 2) * r t :=
    intervalIntegral.integral_of_le hah
  rw [harmonicTailKernel, harmonicTailKernel, hinterval, hsplit]
  ring

theorem hasDerivAt_harmonicTailKernel {r : ℝ → ℝ} (hr : Continuous r) {C : ℝ}
    (hb : ∀ t, |r t| ≤ C) (h : ℝ) :
    HasDerivAt (harmonicTailKernel r) (-(Real.exp (-h / 2) * r h)) h := by
  have hcont : Continuous fun t : ℝ => Real.exp (-t / 2) * r t := by fun_prop
  have hbase : HasDerivAt (fun u : ℝ => ∫ t in (h - 1)..u, Real.exp (-t / 2) * r t)
      (Real.exp (-h / 2) * r h) h := by
    refine intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable _ _) ?_ hcont.continuousAt
    exact (hcont.stronglyMeasurableAtFilter _ _)
  have hshift : HasDerivAt
      (fun u : ℝ => harmonicTailKernel r (h - 1) - ∫ t in (h - 1)..u, Real.exp (-t / 2) * r t)
      (-(Real.exp (-h / 2) * r h)) h := by
    exact HasDerivAt.const_sub (harmonicTailKernel r (h - 1)) hbase
  refine hshift.congr_of_eventuallyEq ?_
  have hmem : Set.Ioi (h - 1) ∈ nhds h :=
    isOpen_Ioi.mem_nhds (Set.mem_Ioi.2 (by linarith))
  filter_upwards [hmem] with u hu
  exact harmonicTailKernel_eq_sub hr hb (le_of_lt hu)

/-! ## The exact resolvent equation -/

/-- **(24.76) The harmonic tail is the exact inverse of the critical outgoing operator.** -/
theorem hasDerivAt_harmonicTail {r : ℝ → ℝ} (hr : Continuous r) {C : ℝ} (hb : ∀ t, |r t| ≤ C)
    (h : ℝ) :
    HasDerivAt (harmonicTail r) (1 / 2 * harmonicTail r h + r h) h := by
  have hker := hasDerivAt_harmonicTailKernel hr hb h
  have hexp : HasDerivAt (fun u : ℝ => -Real.exp (u / 2)) (-(1 / 2 * Real.exp (h / 2))) h := by
    have h1 : HasDerivAt (fun u : ℝ => u / 2) (1 / 2) h := by
      simpa using (hasDerivAt_id h).div_const 2
    have h2 : HasDerivAt (fun u : ℝ => Real.exp (u / 2)) (Real.exp (h / 2) * (1 / 2)) h := h1.exp
    have h3 := h2.neg
    have heq : -(Real.exp (h / 2) * (1 / 2)) = -(1 / 2 * Real.exp (h / 2)) := by ring
    rw [heq] at h3
    exact h3
  have hprod : HasDerivAt (fun u : ℝ => -Real.exp (u / 2) * harmonicTailKernel r u)
      (-(1 / 2 * Real.exp (h / 2)) * harmonicTailKernel r h
        + -Real.exp (h / 2) * -(Real.exp (-h / 2) * r h)) h := hexp.mul hker
  have hval : -(1 / 2 * Real.exp (h / 2)) * harmonicTailKernel r h
      + -Real.exp (h / 2) * -(Real.exp (-h / 2) * r h)
      = 1 / 2 * harmonicTail r h + r h := by
    have hcancel : Real.exp (h / 2) * Real.exp (-h / 2) = 1 := by
      rw [← Real.exp_add, show h / 2 + -h / 2 = 0 by ring, Real.exp_zero]
    rw [harmonicTail]
    linear_combination (r h) * hcancel
  rw [hval] at hprod
  exact hprod

/-- **(24.76)** in operator form: `(1/2 − ∂_h) 𝒯 = −I`. -/
theorem harmonicTail_resolvent {r : ℝ → ℝ} (hr : Continuous r) {C : ℝ} (hb : ∀ t, |r t| ≤ C)
    (h : ℝ) :
    1 / 2 * harmonicTail r h - deriv (harmonicTail r) h = -r h := by
  rw [(hasDerivAt_harmonicTail hr hb h).deriv]
  ring

/-! ## The frequency symbol -/

/-- The outgoing symbol `1/2 − iξ` never vanishes on the real frequency axis. -/
theorem outgoingSymbol_ne_zero (xi : ℝ) :
    (1 / 2 : ℂ) - Complex.I * (xi : ℂ) ≠ 0 := by
  intro hcon
  have hre := congrArg Complex.re hcon
  simp [Complex.sub_re, Complex.mul_re] at hre

/-- **(24.78) The two symbols multiply to `−1` at every frequency.** -/
theorem harmonicTailSymbol_mul_outgoingSymbol (xi : ℝ) :
    ((1 / 2 : ℂ) - Complex.I * (xi : ℂ)) * (-((1 / 2 : ℂ) - Complex.I * (xi : ℂ))⁻¹) = -1 := by
  rw [mul_neg, mul_inv_cancel₀ (outgoingSymbol_ne_zero xi)]

end

end RHTower
