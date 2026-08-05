import GaloisForLFunctions.HTGeometry.MovingCanonicalFullRankUnconditional

/-!
# Differentiated companions: why the free-order recipe stops

The closed full-rank results all use undifferentiated companions, because for those the Herglotz
positivity of the log-derivative gives a nonzero value — hence analytic order zero — at no cost.

That cannot extend.  A Cauchy transform of a positive discrete measure with real support has
critical points inside the upper half-plane: for poles at `1` and `2`, the derivative
`(1−z)^{-2} + (2−z)^{-2}` vanishes at `z = (3+i)/2`.  So no argument of the form "the derivative is
nonvanishing upstairs" is available, and the analytic order of a differentiated companion is
genuinely something to be computed rather than read off.

What survives is weaker but unconditional: a differentiated jet is *not identically zero* on the
upper half-plane, because its blow-up at a boundary zero has a nonzero leading value.  That is the
input a countability argument would need, and it is proved here.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Every jet is somewhere nonzero on the upper half-plane.**  Along a vertical approach to a
boundary zero the jet blows up with leading value `-(-1)^r r!`, so it cannot vanish identically. -/
theorem exists_ne_zero_iteratedDeriv_movingCanonicalLogDerivative
    (θ : BoundedRealSequence) (r : ℕ) :
    ∃ z : ℂ, 0 < z.im ∧ iteratedDeriv r (movingCanonicalLogDerivative θ) z ≠ 0 := by
  set tr : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with htr
  set u : ℕ → ℂ :=
    fun j => ((movingCanonicalZero θ 0 : ℂ)) + ((tr j : ℝ) : ℂ) * Complex.I with hu
  have htrpos : ∀ j, 0 < tr j := by
    intro j
    rw [htr]
    positivity
  have hupper : ∀ j, 0 < (u j).im := by
    intro j
    have him : (u j).im = tr j := by
      rw [hu]
      simp
    rw [him]
    exact htrpos j
  have hulim : Tendsto u atTop (𝓝 ((movingCanonicalZero θ 0 : ℂ))) := by
    have htr0 : Tendsto tr atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Tendsto (fun j => ((tr j : ℝ) : ℂ)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp htr0
    have hmul : Tendsto (fun j => ((tr j : ℝ) : ℂ) * Complex.I) atTop (𝓝 0) := by
      simpa using hc.mul_const Complex.I
    simpa [hu] using tendsto_const_nhds.add hmul
  have hlim := tendsto_iteratedDeriv_movingCanonicalLogDerivative_mul_pow θ 0 r hupper hulim
  by_contra hcon
  push_neg at hcon
  have hzero : ∀ j, iteratedDeriv r (movingCanonicalLogDerivative θ) (u j) *
      (u j - (movingCanonicalZero θ 0 : ℂ)) ^ (r + 1) = 0 := by
    intro j
    rw [hcon (u j) (hupper j), zero_mul]
  have hlim0 : Tendsto (fun j => iteratedDeriv r (movingCanonicalLogDerivative θ) (u j) *
      (u j - (movingCanonicalZero θ 0 : ℂ)) ^ (r + 1)) atTop (𝓝 0) := by
    simp only [hzero]
    exact tendsto_const_nhds
  exact jetLeadingValue_ne_zero r (tendsto_nhds_unique hlim hlim0)

end GaloisForLFunctions.HTGeometry
