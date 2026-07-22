import GaloisForLFunctions.RHTower.SuzukiCarlemanStieltjesFlux

/-!
# Suzuki ground-edge aperture obstruction and Robin compression

The asymmetric shift selector reduces its central sign to a ground-edge screw average.  This file
extracts two unconditional consequences which sharply relocate that source problem.

First, any continuous screw profile with `g(0)=0` stays above every fixed negative threshold on a
small neighborhood of zero.  Since a ground-edge profile on `[-a,a]` samples only `g(a-x)` with
`0 <= a-x <= 2a`, every sufficiently small aperture lies uniformly above the strictly negative
Xi curvature.  Thus a positive-mass weighted ground average cannot meet the required strict
inequality in precisely the small-aperture chamber where Suzuki proves a positive simple ground.

Second, the convolution eigen-equation `-U'' = eigenvalue * phi` for an even mode gives the exact
boundary flux law `-2 * U'(a) = eigenvalue * integral phi`.  Algebraically, the ground average is
therefore the Robin boundary ratio

`-eigenvalue * U(a) / (2 * U'(a))`.

This removes positivity from the viable conjecture: after the small-aperture obstruction, the live
source target is a signed boundary-moment crossing for one simple even mode at a non-small
aperture.  No RH premise, estimate, or numerical computation is used.
-/

open Complex Filter Topology Set GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- Screw profile sampled by the ground-edge source at aperture `a`. -/
def suzukiGroundEdgeProfile (g : ℝ → ℝ) (a x : ℝ) : ℝ :=
  g (a - x)

/-- Continuity at the screw anchor forces every sufficiently small aperture profile to lie above
any fixed negative threshold.  The factor `1/4` leaves a strict neighborhood margin at both
endpoints of `[-a,a]`. -/
theorem exists_smallAperture_suzukiGroundEdgeProfile_gt
    {g : ℝ → ℝ} {lower : ℝ}
    (hg : ContinuousAt g 0) (hg0 : g 0 = 0)
    (hlower : lower < 0) :
    ∃ a₀ > 0, ∀ a, 0 < a → a ≤ a₀ →
      ∀ x ∈ Icc (-a) a, lower < suzukiGroundEdgeProfile g a x := by
  have htarget : Ioi lower ∈ nhds (g 0) := by
    rw [hg0]
    exact Ioi_mem_nhds hlower
  have hpre : g ⁻¹' Ioi lower ∈ nhds (0 : ℝ) := hg htarget
  rcases Metric.mem_nhds_iff.mp hpre with ⟨δ, hδ, hball⟩
  refine ⟨δ / 4, by positivity, ?_⟩
  intro a ha ha₀ x hx
  have hax_nonneg : 0 ≤ a - x := by linarith [hx.2]
  have hax_lt : a - x < δ := by nlinarith [hx.1]
  have hmem : a - x ∈ Metric.ball (0 : ℝ) δ := by
    simpa [Real.dist_eq, abs_of_nonneg hax_nonneg] using hax_lt
  exact hball hmem

/-- Algebraic ground-edge weighted average.  Analytic instantiations take `moment` and `mass` to
be the corresponding screw moment and total ground-mode mass. -/
def suzukiGroundEdgeAverage (moment mass : ℝ) : ℝ :=
  moment / mass

/-- A strict lower threshold and positive mass transfer a lower moment bound to the weighted
average.  This is the exact consumer of a uniform small-aperture profile bound. -/
theorem suzukiGroundEdgeAverage_gt_of_lowerMoment
    {target lower moment mass : ℝ}
    (htarget : target < lower) (hmass : 0 < mass)
    (hmoment : lower * mass ≤ moment) :
    target < suzukiGroundEdgeAverage moment mass := by
  rw [suzukiGroundEdgeAverage, lt_div_iff₀ hmass]
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_right htarget hmass) hmoment

/-- Boundary Robin ratio forced by the even convolution eigen-equation. -/
def suzukiGroundEdgeBoundaryRatio
    (eigenvalue boundaryValue boundarySlope : ℝ) : ℝ :=
  -eigenvalue * boundaryValue / (2 * boundarySlope)

/-- **Robin compression.**  The integrated even eigen-equation converts the boundary ratio into
the original ground-edge average exactly. -/
theorem suzukiGroundEdgeBoundaryRatio_eq_average_of_flux
    {eigenvalue boundaryValue boundarySlope mass : ℝ}
    (heigenvalue : eigenvalue ≠ 0) (hmass : mass ≠ 0)
    (hflux : -2 * boundarySlope = eigenvalue * mass) :
    suzukiGroundEdgeBoundaryRatio eigenvalue boundaryValue boundarySlope =
      suzukiGroundEdgeAverage boundaryValue mass := by
  have hslope : boundarySlope ≠ 0 := by
    intro hslope
    simp only [hslope, mul_zero] at hflux
    exact mul_ne_zero heigenvalue hmass hflux.symm
  have hden : 2 * boundarySlope = -eigenvalue * mass := by
    linarith [hflux]
  rw [suzukiGroundEdgeBoundaryRatio, suzukiGroundEdgeAverage, hden]
  field_simp [heigenvalue, hmass]

/-- Exact deficit/excess classification.  Once a moment is split around a target, its weighted
average crosses below the target exactly when sublevel deficit exceeds superlevel excess. -/
theorem suzukiGroundEdgeAverage_lt_iff_deficit_gt_excess
    {target moment mass deficit excess : ℝ}
    (hmass : 0 < mass)
    (hmoment : moment = target * mass + excess - deficit) :
    suzukiGroundEdgeAverage moment mass < target ↔ excess < deficit := by
  rw [suzukiGroundEdgeAverage, div_lt_iff₀ hmass, hmoment]
  constructor <;> intro h <;> linarith

/-- The Robin crossing is equivalently one signed boundary-moment inequality.  No positivity of
the mode is required; only its oriented total mass is positive. -/
theorem suzukiGroundEdgeBoundaryRatio_lt_iff_boundaryMoment_lt
    {eigenvalue boundaryValue boundarySlope mass target : ℝ}
    (heigenvalue : eigenvalue ≠ 0) (hmass : 0 < mass)
    (hflux : -2 * boundarySlope = eigenvalue * mass) :
    suzukiGroundEdgeBoundaryRatio eigenvalue boundaryValue boundarySlope < target ↔
      boundaryValue < target * mass := by
  rw [suzukiGroundEdgeBoundaryRatio_eq_average_of_flux
    heigenvalue hmass.ne' hflux]
  rw [suzukiGroundEdgeAverage, div_lt_iff₀ hmass]

/-- Concrete Xi specialization of the uniform small-aperture exclusion. -/
theorem exists_smallAperture_XiC_curvature_half_lt_suzukiGroundEdgeProfile
    {g : ℝ → ℝ} (hg : ContinuousAt g 0) (hg0 : g 0 = 0) :
    ∃ a₀ > 0, ∀ a, 0 < a → a ≤ a₀ →
      ∀ x ∈ Icc (-a) a,
        (deriv (deriv XiC) 0 / XiC 0).re / 2 <
          suzukiGroundEdgeProfile g a x := by
  exact exists_smallAperture_suzukiGroundEdgeProfile_gt hg hg0
    (by linarith [XiC_secondDeriv_div_center_re_neg])

/-- A moment above half the negative Xi curvature has average strictly above the full Xi
curvature.  Combined with the preceding uniform profile theorem, this excludes every positive-mass
ground selector throughout a sufficiently small aperture interval. -/
theorem suzukiGroundEdgeAverage_gt_XiC_curvature_of_half_lowerMoment
    {moment mass : ℝ} (hmass : 0 < mass)
    (hmoment : (deriv (deriv XiC) 0 / XiC 0).re / 2 * mass ≤ moment) :
    (deriv (deriv XiC) 0 / XiC 0).re <
      suzukiGroundEdgeAverage moment mass := by
  apply suzukiGroundEdgeAverage_gt_of_lowerMoment _ hmass hmoment
  linarith [XiC_secondDeriv_div_center_re_neg]

end


end RHTower
