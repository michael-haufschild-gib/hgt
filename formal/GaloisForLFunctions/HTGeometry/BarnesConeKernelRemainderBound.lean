import GaloisForLFunctions.HTGeometry.BarnesConeKernelAnalytic

/-!
# The Taylor remainder of the Barnes cone kernel is bounded on the unit interval

The extended cone kernel is continuous on `[0,1]`: at the origin by its analyticity there, and at
every positive point because the two denominators `1 - e^(-ω t)` are real and less than one.  The
same holds for the second-order Taylor remainder, which off the origin is the explicit quotient
`(A(t) - A(0) - t A'(0))/t²`.  Compactness of `[0,1]` then bounds the remainder, which is what makes
the subtracted head integral converge for `Re s > 0`.
-/

open Complex Filter Set MeasureTheory
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem one_sub_exp_neg_ofReal_ne_zero {o t : ℝ} (ho : 0 < o) (ht : 0 < t) :
    (1 : ℂ) - Complex.exp (-((o : ℂ) * (t : ℂ))) ≠ 0 := by
  have hlt : Real.exp (-o * t) < 1 := exp_neg_mul_lt_one ho ht
  have hcast : Complex.exp (-((o : ℂ) * (t : ℂ))) = ((Real.exp (-o * t) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hcast, sub_ne_zero]
  intro hcon
  have hreal : (1 : ℝ) = Real.exp (-o * t) := by exact_mod_cast hcon
  linarith

theorem continuousAt_cylKernelFactor_ofReal_pos {o t : ℝ} (ho : 0 < o) (ht : 0 < t) :
    ContinuousAt (fun u : ℝ => cylKernelFactor (o : ℂ) (u : ℂ)) t := by
  have heq : (fun u : ℝ => cylKernelFactor (o : ℂ) (u : ℂ))
      =ᶠ[𝓝 t] fun u : ℝ => (u : ℂ) / (1 - Complex.exp (-((o : ℂ) * (u : ℂ)))) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact cylKernelFactor_of_ne (Complex.ofReal_ne_zero.mpr (ne_of_gt hu))
  rw [continuousAt_congr heq]
  refine ContinuousAt.div Complex.continuous_ofReal.continuousAt ?_
    (one_sub_exp_neg_ofReal_ne_zero ho ht)
  exact continuousAt_const.sub
    ((Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).neg)).continuousAt)

theorem continuousAt_cylKernelFactor_ofReal_zero {o : ℝ} (ho : 0 < o) :
    ContinuousAt (fun u : ℝ => cylKernelFactor (o : ℂ) (u : ℂ)) 0 := by
  have hoC : (o : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ho)
  have h : ContinuousAt (cylKernelFactor (o : ℂ)) (((0 : ℝ) : ℂ)) := by
    rw [Complex.ofReal_zero]
    exact (analyticAt_cylKernelFactor hoC).continuousAt
  simpa [Function.comp_def] using h.comp Complex.continuous_ofReal.continuousAt

theorem continuousAt_barnesConeKernelAnalytic_ofReal {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (fun u : ℝ => barnesConeKernelAnalytic (o1 : ℂ) (o2 : ℂ) (x : ℂ) (u : ℂ)) t := by
  have hexp : ContinuousAt (fun u : ℝ => Complex.exp (-((x : ℂ) * (u : ℂ)))) t :=
    (Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).neg)).continuousAt
  have hk : ∀ o : ℝ, 0 < o →
      ContinuousAt (fun u : ℝ => cylKernelFactor (o : ℂ) (u : ℂ)) t := by
    intro o ho
    rcases eq_or_lt_of_le ht with h0 | h0
    · rw [← h0]
      exact continuousAt_cylKernelFactor_ofReal_zero ho
    · exact continuousAt_cylKernelFactor_ofReal_pos ho h0
  exact (hexp.mul (hk o1 h1)).mul (hk o2 h2)

theorem continuousAt_barnesConeKernelRemainder_ofReal {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousAt (fun u : ℝ => barnesConeKernelRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (u : ℂ)) t := by
  have hoC1 : (o1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt h1)
  have hoC2 : (o2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt h2)
  rcases eq_or_lt_of_le ht with h0 | h0
  · have hR : ContinuousAt (barnesConeKernelRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ))
        (((0 : ℝ) : ℂ)) := by
      rw [Complex.ofReal_zero]
      exact (analyticAt_barnesConeKernelRemainder hoC1 hoC2 (x : ℂ)).continuousAt
    have := hR.comp Complex.continuous_ofReal.continuousAt
    rw [← h0]
    simpa [Function.comp_def] using this
  · set A : ℂ → ℂ := barnesConeKernelAnalytic (o1 : ℂ) (o2 : ℂ) (x : ℂ) with hA
    have heq : (fun u : ℝ => barnesConeKernelRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (u : ℂ))
        =ᶠ[𝓝 t] fun u : ℝ => (A (u : ℂ) - A 0 - (u : ℂ) * deriv A 0) / (u : ℂ) ^ 2 := by
      filter_upwards [Ioi_mem_nhds h0] with u hu
      have hune : ((u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu)
      have := analyticSlope_two_of_ne (f := A) (c := 0) (z := (u : ℂ)) (by simpa using hune)
      simpa [barnesConeKernelRemainder, hA] using this
    rw [continuousAt_congr heq]
    have hAcont : ContinuousAt (fun u : ℝ => A (u : ℂ)) t :=
      continuousAt_barnesConeKernelAnalytic_ofReal h1 h2 x ht
    refine ContinuousAt.div ((hAcont.sub continuousAt_const).sub
      (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)) ?_ ?_
    · exact (Complex.continuous_ofReal.continuousAt).pow 2
    · exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt h0))

theorem continuousOn_barnesConeKernelRemainder_ofReal {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2)
    (x : ℝ) :
    ContinuousOn (fun u : ℝ => barnesConeKernelRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (u : ℂ))
      (Icc 0 1) := fun _ ht =>
  (continuousAt_barnesConeKernelRemainder_ofReal h1 h2 x ht.1).continuousWithinAt

/-- **The Taylor remainder of the cone kernel is bounded on the unit interval.** -/
theorem exists_bound_barnesConeKernelRemainder {o1 o2 : ℝ} (h1 : 0 < o1) (h2 : 0 < o2) (x : ℝ) :
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖barnesConeKernelRemainder (o1 : ℂ) (o2 : ℂ) (x : ℂ) (t : ℂ)‖ ≤ C :=
  (isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_barnesConeKernelRemainder_ofReal h1 h2 x))

end

end GaloisForLFunctions.HTGeometry
