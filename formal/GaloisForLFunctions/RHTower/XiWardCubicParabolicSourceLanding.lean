import GaloisForLFunctions.HTGeometry.ParabolicCauchyAveraging
import GaloisForLFunctions.RHTower.XiWardCubicPositiveShiftAveragedMultiplicity

/-!
# Cubic multiplicity from the actual parabolically averaged source current

The positive-shift germ average extracts residues before averaging. Here both operations are
performed on the actual continued source: horizontal shifts have width `h`, and their common
endpoint is displaced vertically by `i h^2`. Multiplication by `i h^2` retains the endpoint
residue, whereas the moving predecessor pole disappears under the atomless shift average.

The resulting limit is the full Xi multiplicity times the cubic tensor norm square. No zero,
simplicity, separation, or sign assumption enters the theorem. On the Euler chamber the same
current is literally the completed pole--Gamma--von-Mangoldt increment average.
-/

open Complex Filter Topology MeasureTheory Set

namespace RHTower
noncomputable section

open GaloisForLFunctions.HTGeometry.ParabolicCauchyAveraging

/-- A fixed transverse approach, chosen independently of the Xi divisor. -/
def xiWardParabolicPoint (z : ℂ) (h : ℝ) : ℂ := z + I * (h : ℂ) ^ 2

/-- Transversely normalized actual shift average. No residue or divisor enters its definition. -/
def xiWardParabolicSourceAverage (W : ℂ × ℝ → ℂ) (z : ℂ) (h : ℝ) : ℂ :=
  I * (h : ℂ) ^ 2 *
    xiWardCubicShiftEndpointWeightedContinuedAverage (xiWardParabolicPoint z h) 0 h
      (fun eps => W (xiWardParabolicPoint z h, eps))

/-- The cubic reporter is inserted into the actual source average before taking any limit. -/
def xiWardCubicParabolicSourceCurrent (z : ℂ) (h r : ℝ) : ℂ :=
  xiWardParabolicSourceAverage
    (fun p => xiWardCubicPositiveShiftBichamberWeight p.1 p.2 r) z h

private theorem mul_continued_transgression (z : ℂ) (eps : ℝ) :
    (eps : ℂ) * xiWardCubicPositiveShiftDivisorTransgression z eps =
      logDeriv xi z - logDeriv xi (z - (eps : ℂ)) := by
  by_cases heps : eps = 0
  · subst eps
    simp
  · unfold xiWardCubicPositiveShiftDivisorTransgression xiFluxShiftDifference seamFluxCochain
    field_simp [ofReal_ne_zero.mpr heps]
    ring

/-- Fixed-interval normal form of the literal continued covariance average. -/
theorem xiWardParabolicSourceAverage_eq_incrementIntegral
    (W : ℂ × ℝ → ℂ) (z : ℂ) {h : ℝ} (hh : 0 < h) :
    xiWardParabolicSourceAverage W z h =
      ∫ u : ℝ in 0..1,
        (I * (h : ℂ) ^ 2 *
          (logDeriv xi (xiWardParabolicPoint z h) -
            logDeriv xi (xiWardParabolicPoint z h - (h * u : ℂ)))) *
          W (xiWardParabolicPoint z h, h * u) := by
  let f : ℝ → ℂ := fun eps =>
    (eps : ℂ) * xiWardCubicPositiveShiftDivisorTransgression (xiWardParabolicPoint z h) eps *
      W (xiWardParabolicPoint z h, eps)
  have hs := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) f hh.ne'
  simp only [mul_zero, mul_one, Complex.real_smul] at hs
  unfold xiWardParabolicSourceAverage xiWardCubicShiftEndpointWeightedContinuedAverage
  simp only [sub_zero]
  change I * (h : ℂ) ^ 2 * (((h⁻¹ : ℝ) : ℂ) * ∫ eps in 0..h, f eps) = _
  rw [← hs, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only [f]
  rw [mul_continued_transgression]
  push_cast
  ring

/-- On the absolute-Euler chamber the same object is the pre-divisor arithmetic average. -/
theorem xiWardParabolicSourceAverage_eq_arithmetic
    (W : ℂ × ℝ → ℂ) {z : ℂ} {h : ℝ} (hh : 0 < h) (hz : 1 + h < z.re) :
    xiWardParabolicSourceAverage W z h =
      I * (h : ℂ) ^ 2 *
        xiWardCubicShiftEndpointWeightedArithmeticAverage (xiWardParabolicPoint z h) 0 h
          (fun eps => W (xiWardParabolicPoint z h, eps)) := by
  unfold xiWardParabolicSourceAverage
  rw [xiWardCubicShiftEndpointWeightedArithmeticAverage_eq_continued _ (le_refl 0) hh]
  simp [xiWardParabolicPoint, ← ofReal_pow]
  linarith

private theorem measurable_xi_logDeriv : Measurable (logDeriv xi) := by
  have hd : Continuous (deriv xi) := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (xi_differentiable.analyticAt z).deriv.continuousAt
  simpa only [logDeriv, Pi.div_apply] using hd.measurable.div xi_differentiable.continuous.measurable

private theorem measurable_completedFluxGermAt (rho : ℂ) :
    Measurable (completedFluxGermAt rho) := by
  unfold completedFluxGermAt seamFluxCochain
  apply Measurable.ite (measurableSet_singleton 0) measurable_const
  exact measurable_id.mul (measurable_xi_logDeriv.comp (by fun_prop)).neg

private theorem continuous_bichamberWeight (r : ℝ) :
    Continuous (fun p : ℂ × ℝ => xiWardCubicPositiveShiftBichamberWeight p.1 p.2 r) := by
  unfold xiWardCubicPositiveShiftBichamberWeight xiWardCubicBichamberFeatureProduct
    xiWardCubicBichamberLeftFeature xiWardCubicBichamberRightFeature
  fun_prop

private theorem parabolic_increment_ne_zero {h : ℝ} (hh : 0 < h) (u : ℝ) :
    -(h * u : ℂ) + I * (h : ℂ) ^ 2 ≠ 0 := by
  intro hz
  have hi := congrArg Complex.im hz
  simp [← ofReal_pow] at hi
  nlinarith

private theorem parabolic_endpoint_germ (rho : ℂ) {h : ℝ} (hh : 0 < h) :
    -completedFluxGermAt rho (I * (h : ℂ) ^ 2) =
      I * (h : ℂ) ^ 2 * logDeriv xi (xiWardParabolicPoint rho h) := by
  have hn : I * (h : ℂ) ^ 2 ≠ 0 :=
    mul_ne_zero I_ne_zero (pow_ne_zero _ (ofReal_ne_zero.mpr hh.ne'))
  simp [completedFluxGermAt, hn, seamFluxCochain, xiWardParabolicPoint]

private theorem parabolic_moving_germ (rho : ℂ) {h : ℝ} (hh : 0 < h) (u : ℝ) :
    ratio h u * -completedFluxGermAt rho (-(h * u : ℂ) + I * (h : ℂ) ^ 2) =
      I * (h : ℂ) ^ 2 *
        logDeriv xi (rho + (-(h * u : ℂ) + I * (h : ℂ) ^ 2)) := by
  have hn := parabolic_increment_ne_zero hh u
  have hd : -(u : ℂ) + I * (h : ℂ) ≠ 0 := by
    intro hz
    have hi := congrArg Complex.im hz
    simp at hi
    linarith
  simp only [completedFluxGermAt, if_neg hn, seamFluxCochain, mul_neg, neg_neg]
  unfold ratio
  field_simp [hd]

/-- Multiplicity extraction commutes with the actual parabolic average of a measurable weight
continuous at the landing point. Moving translated poles are controlled inside the integral. -/
theorem tendsto_xiWardParabolicSourceAverage_of_continuousAt
    (W : ℂ × ℝ → ℂ) (hWm : Measurable W) (rho : ℂ)
    (hW : ContinuousAt W (rho, 0)) :
    Tendsto (xiWardParabolicSourceAverage W rho) (𝓝[>] 0)
      (𝓝 ((((analyticOrderAt xi rho).toNat : ℕ) : ℂ) * W (rho, 0))) := by
  let F : ℝ × ℝ → ℂ := fun p =>
    -completedFluxGermAt rho (I * (p.1 : ℂ) ^ 2) *
      W (xiWardParabolicPoint rho p.1, p.2)
  let G : ℝ × ℝ → ℂ := fun p =>
    -completedFluxGermAt rho (-(p.2 : ℂ) + I * (p.1 : ℂ) ^ 2) *
      W (xiWardParabolicPoint rho p.1, p.2)
  have ha : Continuous (fun p : ℝ × ℝ => (xiWardParabolicPoint rho p.1, p.2)) := by
    unfold xiWardParabolicPoint
    fun_prop
  have hweightm := hWm.comp ha.measurable
  have hweight : ContinuousAt
      (fun p : ℝ × ℝ => W (xiWardParabolicPoint rho p.1, p.2)) (0, 0) :=
    hW.comp_of_eq ha.continuousAt (by simp [xiWardParabolicPoint])
  have hp : Continuous (fun p : ℝ × ℝ => I * (p.1 : ℂ) ^ 2) := by fun_prop
  have hq : Continuous (fun p : ℝ × ℝ => -(p.2 : ℂ) + I * (p.1 : ℂ) ^ 2) := by fun_prop
  have hFm : Measurable F := by
    exact ((measurable_completedFluxGermAt rho).comp hp.measurable).neg.mul hweightm
  have hGm : Measurable G := by
    exact ((measurable_completedFluxGermAt rho).comp hq.measurable).neg.mul hweightm
  have hFc : ContinuousAt F (0, 0) := by
    apply ContinuousAt.mul _ hweight
    have hg : ContinuousAt (fun x => -completedFluxGermAt rho x) 0 :=
      (completedFluxGermAt_analyticAt_zero rho).continuousAt.neg
    exact hg.comp_of_eq hp.continuousAt (by simp)
  have hGc : ContinuousAt G (0, 0) := by
    apply ContinuousAt.mul _ hweight
    have hg : ContinuousAt (fun x => -completedFluxGermAt rho x) 0 :=
      (completedFluxGermAt_analyticAt_zero rho).continuousAt.neg
    exact hg.comp_of_eq hq.continuousAt (by simp)
  have hlim := difference_average_tendsto hFm hFc hGm hGc
  have hv : F (0, 0) = (((analyticOrderAt xi rho).toNat : ℕ) : ℂ) * W (rho, 0) := by
    simp [F, xiWardParabolicPoint]
  rw [hv] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [xiWardParabolicSourceAverage_eq_incrementIntegral W rho hh]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only [F, G]
  push_cast
  rw [parabolic_endpoint_germ rho hh, ← mul_assoc, parabolic_moving_germ rho hh u]
  have hz : xiWardParabolicPoint rho h - (h * u : ℂ) =
      rho + (-(h * u : ℂ) + I * (h : ℂ) ^ 2) := by
    unfold xiWardParabolicPoint
    ring
  rw [hz]
  ring

/-- Globally continuous source weights satisfy the local landing theorem. -/
theorem tendsto_xiWardParabolicSourceAverage
    (W : ℂ × ℝ → ℂ) (hW : Continuous W) (rho : ℂ) :
    Tendsto (xiWardParabolicSourceAverage W rho) (𝓝[>] 0)
      (𝓝 ((((analyticOrderAt xi rho).toNat : ℕ) : ℂ) * W (rho, 0))) :=
  tendsto_xiWardParabolicSourceAverage_of_continuousAt W hW.measurable rho hW.continuousAt

/-- The actual cubic source average lands on the tensor norm square with linear multiplicity,
unconditionally at every complex point. -/
theorem tendsto_xiWardCubicParabolicSourceCurrent (rho : ℂ) (r : ℝ) :
    Tendsto (fun h : ℝ => xiWardCubicParabolicSourceCurrent rho h r)
      (𝓝[>] 0)
      (𝓝 ((((analyticOrderAt xi rho).toNat : ℕ) : ℂ) *
        (Complex.normSq (xiWardCubicTensorConormalFeature (star rho) r) : ℂ))) := by
  simpa only [xiWardCubicParabolicSourceCurrent, xiWardCubicPositiveShiftBichamberWeight_zero]
    using tendsto_xiWardParabolicSourceAverage _ (continuous_bichamberWeight r) rho

end
end RHTower
