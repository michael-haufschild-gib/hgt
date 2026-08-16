import GaloisForLFunctions.HTGeometry.EndpointGermAnalytic

/-!
# `(10)`: the differentiated endpoint germ decays at the boundary rate

A datum analytic in the physical boundary variable `r = e^{-L}` has, in the logarithmic variable,
derivative `G′(L) = −e^{-L}g′(e^{-L})`.  The inner factor is bounded on the closed unit disc, so the
whole derivative is `O(e^{-L})`: the constant term of the germ disappears under differentiation and
what is left already carries the boundary rate.  This is the source estimate the scale-gap theorem
feeds to the block Hardy transfer.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The datum read in the logarithmic variable. -/
def endpointGerm (g : ℂ → ℂ) (L : ℝ) : ℂ := g ((Real.exp (-L) : ℝ) : ℂ)

theorem hasDerivAt_endpointGerm {g : ℂ → ℂ} (hg : Differentiable ℂ g) (L : ℝ) :
    HasDerivAt (endpointGerm g)
      (-((Real.exp (-L) : ℝ) : ℂ) * deriv g ((Real.exp (-L) : ℝ) : ℂ)) L := by
  have h0 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-L)) L := by
    refine ((hasDerivAt_neg L).exp).congr_deriv ?_
    ring
  have hin : HasDerivAt (fun y : ℝ => ((Real.exp (-y) : ℝ) : ℂ))
      (((-Real.exp (-L) : ℝ) : ℂ)) L := h0.ofReal_comp
  have hout : HasDerivAt g (deriv g (((Real.exp (-L) : ℝ) : ℂ)))
      (((Real.exp (-L) : ℝ) : ℂ)) := (hg _).hasDerivAt
  have hcomp := hout.comp L hin
  refine (hcomp.congr_deriv ?_).congr_of_eventuallyEq ?_
  · push_cast
    ring
  · filter_upwards with y
    rfl

/-- **The germ's derivative is `O(e^{-L})` on the terminal ray.** -/
theorem exists_bound_deriv_endpointGerm {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L →
      ‖-((Real.exp (-L) : ℝ) : ℂ) * deriv g ((Real.exp (-L) : ℝ) : ℂ)‖ ≤ C * Real.exp (-L) := by
  have hcont : Continuous (deriv g) := (Differentiable.deriv hg).continuous
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun L hL => ?_⟩
  have hmem : ((Real.exp (-L) : ℝ) : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hb : ‖deriv g ((Real.exp (-L) : ℝ) : ℂ)‖ ≤ max C 0 :=
    le_trans (hC _ hmem) (le_max_left _ _)
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (-L) * ‖deriv g ((Real.exp (-L) : ℝ) : ℂ)‖
      ≤ Real.exp (-L) * max C 0 := mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = max C 0 * Real.exp (-L) := by ring

/-- **`(10)`: the differentiated germ obeys the boundary rate.** -/
theorem exists_bound_deriv_endpointGerm' {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ‖deriv (endpointGerm g) L‖ ≤ C * Real.exp (-L) := by
  obtain ⟨C, hC, hb⟩ := exists_bound_deriv_endpointGerm hg
  refine ⟨C, hC, fun L hL => ?_⟩
  rw [(hasDerivAt_endpointGerm hg L).deriv]
  exact hb L hL

end GaloisForLFunctions.HTGeometry
