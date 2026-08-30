import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodHomotopySeamRatioOrientation
import GaloisForLFunctions.RHTower.ThetaCuspExactCompletedC5SeamFarTail

/-!
# Theta likelihood homotopy curvature energy

The C5 seam invariant is the negative derivative of a stronger global source energy:

`E = 3 * F₃² - 2 * F₂ * F₄`.

Indeed `E' = -2 * (F₂ * F₅ - 2 * F₃ * F₄)`.  The already-closed seam invariant therefore makes
`E` strictly decreasing on every structural-tail ray.  Exact far-tail decay of the likelihood
cumulants forces `F₂`, `F₃`, and `F₄`, hence `E`, to tend to zero.  A strictly decreasing function
with zero terminal limit is strictly positive, giving

`2 * F₂ * F₄ < 3 * F₃²`.

Equivalently, the inverse square root of the positive likelihood curvature has positive ordinary
curvature.  This is the first global nonlinear shape law extracted from the local C5 seam
orientation.  It supplies the projective-curvature premise for the lower-transport determinant in
the affine likelihood homotopy.

RH chain: inverse-square-root likelihood convexity -> positive lower-transport curvature ->
positive `M'''` -> convex likelihood lift -> structural-tail direct-J orientation ->
reflection-odd rank-four/Ptolemy wall -> CLG/TTF or Weil positivity -> RH.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

/-- Projective curvature energy selected by the C5 seam invariant. -/
def thetaCuspLikelihoodHomotopyCurvatureEnergy (x : ℝ) : ℝ :=
  3 * thetaCuspLikelihoodSourceLogPartitionJetThree x ^ 2 -
    2 * thetaCuspLikelihoodSourceLogPartitionJetTwo x *
      thetaCuspLikelihoodSourceLogPartitionJetFour x

/-- Likelihood source curvature itself vanishes on the far source tail. -/
theorem tendsto_thetaCuspLikelihoodSourceLogPartitionJetTwo_atTop_zero :
    Tendsto thetaCuspLikelihoodSourceLogPartitionJetTwo atTop (nhds 0) := by
  have hv := thetaCuspC5FarTail_scaled_likelihoodVariance_source_tendsto_zero 2
  have hm := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero 1
  have h := (hv.const_mul 4).sub (hm.const_mul 4)
  convert h using 1
  · funext x
    unfold thetaCuspLikelihoodSourceLogPartitionJetTwo
    ring
  · norm_num

/-- Third likelihood source jet vanishes on the far source tail. -/
theorem tendsto_thetaCuspLikelihoodSourceLogPartitionJetThree_atTop_zero :
    Tendsto thetaCuspLikelihoodSourceLogPartitionJetThree atTop (nhds 0) := by
  have hk := thetaCuspC5FarTail_scaled_likelihoodThirdCumulant_source_tendsto_zero 3
  have hv := thetaCuspC5FarTail_scaled_likelihoodVariance_source_tendsto_zero 2
  have hm := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero 1
  have h := ((hk.const_mul (-8)).add (hv.const_mul 24)).sub (hm.const_mul 8)
  convert h using 1
  · funext x
    unfold thetaCuspLikelihoodSourceLogPartitionJetThree
    ring
  · norm_num

/-- Fourth likelihood source jet vanishes on the far source tail. -/
theorem tendsto_thetaCuspLikelihoodSourceLogPartitionJetFour_atTop_zero :
    Tendsto thetaCuspLikelihoodSourceLogPartitionJetFour atTop (nhds 0) := by
  have hk4 := thetaCuspC5FarTail_scaled_likelihoodFourthCumulant_source_tendsto_zero 4
  have hk3 := thetaCuspC5FarTail_scaled_likelihoodThirdCumulant_source_tendsto_zero 3
  have hv := thetaCuspC5FarTail_scaled_likelihoodVariance_source_tendsto_zero 2
  have hm := thetaCuspC5FarTail_scaled_likelihoodMean_source_tendsto_zero 1
  have h := (((hk4.const_mul 16).sub (hk3.const_mul 96)).add
    (hv.const_mul 112)).sub (hm.const_mul 16)
  convert h using 1
  · funext x
    unfold thetaCuspLikelihoodSourceLogPartitionJetFour
    ring
  · norm_num

/-- The projective curvature energy has terminal value zero. -/
theorem tendsto_thetaCuspLikelihoodHomotopyCurvatureEnergy_atTop_zero :
    Tendsto thetaCuspLikelihoodHomotopyCurvatureEnergy atTop (nhds 0) := by
  have h2 := tendsto_thetaCuspLikelihoodSourceLogPartitionJetTwo_atTop_zero
  have h3 := tendsto_thetaCuspLikelihoodSourceLogPartitionJetThree_atTop_zero
  have h4 := tendsto_thetaCuspLikelihoodSourceLogPartitionJetFour_atTop_zero
  have h := ((h3.mul h3).const_mul 3).sub ((h2.mul h4).const_mul 2)
  convert h using 1
  · funext x
    unfold thetaCuspLikelihoodHomotopyCurvatureEnergy
    ring
  · norm_num

/-- Exact derivative: the C5 seam invariant is minus one half of the energy drift. -/
theorem hasDerivAt_thetaCuspLikelihoodHomotopyCurvatureEnergy
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt thetaCuspLikelihoodHomotopyCurvatureEnergy
      (-2 * (thetaCuspLikelihoodSourceLogPartitionJetTwo x *
          thetaCuspLikelihoodSourceLogPartitionJetFive x -
        2 * thetaCuspLikelihoodSourceLogPartitionJetThree x *
          thetaCuspLikelihoodSourceLogPartitionJetFour x)) x := by
  have hB := thetaCuspLikelihoodCoordinate_pos hx
  have h2 := hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetTwo hB
  have h3 := hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetThree hB
  have h4 := hasDerivAt_thetaCuspLikelihoodSourceLogPartitionJetFour hB
  have hraw := ((h3.mul h3).const_mul 3).sub ((h2.mul h4).const_mul 2)
  refine (hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · unfold thetaCuspLikelihoodHomotopyCurvatureEnergy
    simp only [Pi.mul_apply, Pi.sub_apply]
    ring
  · ring

private theorem thetaCuspSingleAtomReflectionScale_one_mono
    {x y : ℝ} (hxy : x ≤ y) :
    thetaCuspSingleAtomReflectionScale 1 x ≤
      thetaCuspSingleAtomReflectionScale 1 y := by
  unfold thetaCuspSingleAtomReflectionScale
  norm_num
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith)) Real.pi_pos.le

/-- Energy strictly decreases after any structural-tail entrance point. -/
theorem strictAntiOn_thetaCuspLikelihoodHomotopyCurvatureEnergy_of_scale
    {x₀ : ℝ} (hx₀ : 0 ≤ x₀)
    (hscale₀ : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x₀) :
    StrictAntiOn thetaCuspLikelihoodHomotopyCurvatureEnergy (Ici x₀) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici x₀)
  · intro x hx
    exact (hasDerivAt_thetaCuspLikelihoodHomotopyCurvatureEnergy
      (hx₀.trans hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 ≤ x := hx₀.trans hx.le
    have hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x :=
      hscale₀.trans (thetaCuspSingleAtomReflectionScale_one_mono hx.le)
    rw [(hasDerivAt_thetaCuspLikelihoodHomotopyCurvatureEnergy hx0).deriv]
    nlinarith [thetaCuspLikelihoodHomotopyC5SeamInvariant_pos hx0 hscale]

/-- **Global C5 projective-curvature law.** The energy is strictly positive throughout the
structural source tail. -/
theorem thetaCuspLikelihoodHomotopyCurvatureEnergy_pos
    {x : ℝ} (hx : 0 ≤ x)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    0 < thetaCuspLikelihoodHomotopyCurvatureEnergy x := by
  let y := x + 1
  have hxy : x < y := by dsimp [y]; linarith
  have hanti := strictAntiOn_thetaCuspLikelihoodHomotopyCurvatureEnergy_of_scale hx hscale
  have hy_mem : y ∈ Ici x := hxy.le
  have htail : ∀ᶠ z : ℝ in atTop,
      thetaCuspLikelihoodHomotopyCurvatureEnergy z ≤
        thetaCuspLikelihoodHomotopyCurvatureEnergy y := by
    filter_upwards [eventually_ge_atTop y] with z hz
    by_cases hzy : y = z
    · exact hzy ▸ le_rfl
    · exact (hanti hy_mem (hy_mem.trans hz) (lt_of_le_of_ne hz hzy)).le
  have hy_nonneg : 0 ≤ thetaCuspLikelihoodHomotopyCurvatureEnergy y :=
    le_of_tendsto tendsto_thetaCuspLikelihoodHomotopyCurvatureEnergy_atTop_zero htail
  exact lt_of_le_of_lt hy_nonneg (hanti (Set.mem_Ici.mpr le_rfl) hy_mem hxy)

/-- Division-free inverse-square-root convexity inequality for likelihood curvature. -/
theorem three_mul_sq_thetaCuspLikelihoodSourceLogPartitionJetThree_gt
    {x : ℝ} (hx : 0 ≤ x)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    2 * thetaCuspLikelihoodSourceLogPartitionJetTwo x *
        thetaCuspLikelihoodSourceLogPartitionJetFour x <
      3 * thetaCuspLikelihoodSourceLogPartitionJetThree x ^ 2 := by
  exact sub_pos.mp (thetaCuspLikelihoodHomotopyCurvatureEnergy_pos hx hscale)

end

end RHTower
