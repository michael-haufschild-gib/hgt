import GaloisForLFunctions.RHTower.SuzukiCarlemanCoordinatePhase

/-!
# Large-negative-shift obstruction to an unselected Suzuki jump colligation

For fixed aperture, the resolvents defining Suzuki's two deficiency channels enter a universal
Neumann-dominated regime as the real form shift tends to `-∞`.  After the direct linear Neumann
channel is removed by affine sewing, the normalized Euler--Gamma triangle jet has a finite limit.
Along the dyadic pair `alpha=-2*L`, `beta=-L`, its affine intercept tends to that same limit.

This module proves the exact affine-asymptotic consumer.  The paper source theorem identifies the
limit with the initial screw average

`(2*a)⁻¹ * ∫₀^(2*a) g(t) dt`.

Since `g(0)=0`, this average approaches zero at small aperture, while
`Re (XiC''(0)/XiC(0))<0`.  Hence sufficiently negative dyadic shift pairs at sufficiently small
aperture violate the necessary central Herglotz inequality.  A viable scalar jump colligation
must select shifts away from this escape cone; arbitrary admissible shifts cannot work.

No RH assumption, estimate, or numerical computation occurs here.
-/

open Complex Filter Topology GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- Value at target shift zero of the affine chord through `(alpha,q alpha)` and
`(beta,q beta)`. -/
def suzukiRealAffineZeroIntercept
    (q : ℝ → ℝ) (alpha beta : ℝ) : ℝ :=
  (beta * q alpha - alpha * q beta) / (beta - alpha)

/-- Dyadic negative-shift specialization `alpha=-2L`, `beta=-L`. -/
def suzukiDyadicNegativeShiftIntercept (q : ℝ → ℝ) (L : ℝ) : ℝ :=
  2 * q (-L) - q (-2 * L)

/-- The closed dyadic formula is exactly the affine zero-intercept whenever `L≠0`. -/
theorem suzukiRealAffineZeroIntercept_neg_two_neg_one
    (q : ℝ → ℝ) {L : ℝ} (hL : L ≠ 0) :
    suzukiRealAffineZeroIntercept q (-2 * L) (-L) =
      suzukiDyadicNegativeShiftIntercept q L := by
  rw [suzukiRealAffineZeroIntercept, suzukiDyadicNegativeShiftIntercept]
  field_simp [hL]
  ring

/-- A finite normalized edge-jet limit at `-∞` is inherited unchanged by the dyadic affine
intercept.  Linear shift channels have already disappeared from this observable. -/
theorem tendsto_suzukiDyadicNegativeShiftIntercept_atTop
    {q : ℝ → ℝ} {edgeLimit : ℝ} (hq : Tendsto q atBot (nhds edgeLimit)) :
    Tendsto (suzukiDyadicNegativeShiftIntercept q) atTop (nhds edgeLimit) := by
  have hneg : Tendsto (fun L : ℝ => -L) atTop atBot := tendsto_neg_atTop_atBot
  have hnegTwo : Tendsto (fun L : ℝ => -2 * L) atTop atBot := by
    have htwo : Tendsto (fun L : ℝ => 2 * L) atTop atTop :=
      tendsto_id.const_mul_atTop (by norm_num)
    exact (hneg.comp htwo).congr' (Eventually.of_forall (fun L => by
      simp only [Function.comp_apply]
      ring))
  have h1 := hq.comp hneg
  have h2 := hq.comp hnegTwo
  have hcomb := ((tendsto_const_nhds (x := (2 : ℝ))).mul h1).sub h2
  have hlim : 2 * edgeLimit - edgeLimit = edgeLimit := by ring
  rw [hlim] at hcomb
  exact hcomb.congr'
    (Eventually.of_forall fun _ => rfl)

/-- If the Neumann-dominated Euler--Gamma edge limit lies above the Xi curvature threshold, every
sufficiently negative dyadic shift pair violates that necessary Herglotz sign. -/
theorem eventually_XiC_curvature_lt_suzukiDyadicNegativeShiftIntercept
    {q : ℝ → ℝ} {edgeLimit : ℝ} (hq : Tendsto q atBot (nhds edgeLimit))
    (hcurvature : (deriv (deriv XiC) 0 / XiC 0).re < edgeLimit) :
    ∀ᶠ L in atTop,
      (deriv (deriv XiC) 0 / XiC 0).re <
        suzukiDyadicNegativeShiftIntercept q L := by
  have ht := tendsto_suzukiDyadicNegativeShiftIntercept_atTop hq
  exact (tendsto_order.1 ht).1 _ hcurvature

/-- Small-aperture endpoint profile: any normalized edge jet tending to zero at large negative
shift eventually lies on the forbidden side of the strictly negative Xi curvature. -/
theorem eventually_XiC_curvature_lt_suzukiDyadicNegativeShiftIntercept_of_tendsto_zero
    {q : ℝ → ℝ} (hq : Tendsto q atBot (nhds 0)) :
    ∀ᶠ L in atTop,
      (deriv (deriv XiC) 0 / XiC 0).re <
        suzukiDyadicNegativeShiftIntercept q L :=
  eventually_XiC_curvature_lt_suzukiDyadicNegativeShiftIntercept hq
    XiC_secondDeriv_div_center_re_neg

end

end RHTower
