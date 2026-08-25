import GaloisForLFunctions.HTGeometry.HolomorphicBallMeanSq
import GaloisForLFunctions.RHTower.PolynomialFockAdaptedBregman
import GaloisForLFunctions.RHTower.PolynomialFockLocalBregman
import GaloisForLFunctions.RHTower.PolynomialMomentFockKernelLower
import GaloisForLFunctions.RHTower.PolynomialMomentFockNorm

/-!
# Local weighted evaluation for the polynomial moment Fock carrier

An explicit radius makes the local upper Bregman remainder at most one.  Gauging an entire
function by the holomorphic tangent exponential and applying the planar mean-square inequality then
controls point evaluation by weighted mass on that local ball.
-/

open MeasureTheory Set Metric
open scoped Real

namespace RHTower

noncomputable section

/-- Exact local quadratic scale from the upper Bregman estimate. -/
def polynomialFockLocalScale (m x : ℝ) : ℝ :=
  polynomialFockLocalBregmanConstant m * (1 + x ^ 2) ^ (m / 2 - 1)

/-- Radius on which the explicit upper Bregman remainder is at most one. -/
def polynomialFockLocalRadius (m x : ℝ) : ℝ :=
  (Real.sqrt (polynomialFockLocalScale m x))⁻¹

theorem one_le_polynomialFockLocalScale
    {m x : ℝ} (hm : 4 ≤ m) : 1 ≤ polynomialFockLocalScale m x := by
  have hCpos := polynomialFockLocalBregmanConstant_pos hm
  have hC : 1 ≤ polynomialFockLocalBregmanConstant m := by
    unfold polynomialFockLocalBregmanConstant
    have hterm : 0 ≤ 6 * (m / 2) * (m / 2 - 1) * 3 ^ (m / 2 - 2) := by
      have : 0 ≤ m / 2 - 1 := by linarith
      positivity
    linarith
  have hA : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hβ : 0 ≤ m / 2 - 1 := by linarith
  have hpow : 1 ≤ (1 + x ^ 2) ^ (m / 2 - 1) := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hA hβ
  unfold polynomialFockLocalScale
  nlinarith [mul_le_mul hC hpow (by norm_num : (0 : ℝ) ≤ 1) hCpos.le]

theorem polynomialFockLocalRadius_pos
    {m x : ℝ} (hm : 4 ≤ m) : 0 < polynomialFockLocalRadius m x := by
  unfold polynomialFockLocalRadius
  exact inv_pos.mpr (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one
    (one_le_polynomialFockLocalScale hm)))

theorem polynomialFockLocalRadius_le_one
    {m x : ℝ} (hm : 4 ≤ m) : polynomialFockLocalRadius m x ≤ 1 := by
  have hsqrt : 1 ≤ Real.sqrt (polynomialFockLocalScale m x) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (one_le_polynomialFockLocalScale hm)
  unfold polynomialFockLocalRadius
  exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hsqrt)).2 hsqrt

theorem polynomialFockLocalScale_mul_radius_sq
    {m x : ℝ} (hm : 4 ≤ m) :
    polynomialFockLocalScale m x * polynomialFockLocalRadius m x ^ 2 = 1 := by
  have hscale : 0 < polynomialFockLocalScale m x :=
    lt_of_lt_of_le zero_lt_one (one_le_polynomialFockLocalScale hm)
  have hsqrt : Real.sqrt (polynomialFockLocalScale m x) ≠ 0 :=
    (Real.sqrt_pos.2 hscale).ne'
  unfold polynomialFockLocalRadius
  rw [inv_pow]
  field_simp [hsqrt]
  exact (Real.sq_sqrt hscale.le).symm

/-- On the explicit local radius, the tangent upper remainder is at most one. -/
theorem polynomialFockPotential_bregman_upper_local
    {m x : ℝ} (hm : 4 ≤ m) (hx : 0 ≤ x) (w : ℂ)
    (hw : ‖w‖ ≤ polynomialFockLocalRadius m x) :
    polynomialFockPotential m ‖(x : ℂ) + w‖ ≤
      polynomialFockPotential m x + polynomialFockRadialSlope m x * w.re + 1 := by
  have hunit : ‖w‖ ≤ 1 := hw.trans (polynomialFockLocalRadius_le_one hm)
  have hbase := polynomialFockPotential_bregman_upper_unit hm hx w hunit
  have hscale0 : 0 ≤ polynomialFockLocalScale m x :=
    (one_le_polynomialFockLocalScale hm).trans' zero_le_one
  have hsq : ‖w‖ ^ 2 ≤ polynomialFockLocalRadius m x ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (polynomialFockLocalRadius_pos hm).le).2 hw
  have hrem : polynomialFockLocalScale m x * ‖w‖ ^ 2 ≤ 1 := by
    calc
      polynomialFockLocalScale m x * ‖w‖ ^ 2 ≤
          polynomialFockLocalScale m x * polynomialFockLocalRadius m x ^ 2 :=
        mul_le_mul_of_nonneg_left hsq hscale0
      _ = 1 := polynomialFockLocalScale_mul_radius_sq hm
  unfold polynomialFockLocalScale at hrem
  linarith

/-- Holomorphic tangent gauge used to cancel first-order weight variation. -/
def polynomialFockTangentGauge (m x : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  F z * Complex.exp (-(polynomialFockRadialSlope m x : ℂ) * (z - x))

theorem differentiable_polynomialFockTangentGauge
    (m x : ℝ) (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    Differentiable ℂ (polynomialFockTangentGauge m x F) := by
  unfold polynomialFockTangentGauge
  fun_prop

theorem normSq_polynomialFockTangentGauge
    (m x : ℝ) (F : ℂ → ℂ) (z : ℂ) :
    ‖polynomialFockTangentGauge m x F z‖ ^ 2 =
      ‖F z‖ ^ 2 * Real.exp (-2 * polynomialFockRadialSlope m x * (z.re - x)) := by
  unfold polynomialFockTangentGauge
  rw [norm_mul, Complex.norm_exp, mul_pow]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  simp
  ring

/-- Pointwise comparison of the gauged density with the original weighted density. -/
theorem normSq_polynomialFockTangentGauge_le_weighted
    {m x : ℝ} (hm : 4 ≤ m) (hx : 0 ≤ x) (F : ℂ → ℂ) (z : ℂ)
    (hz : z ∈ Metric.ball (x : ℂ) (polynomialFockLocalRadius m x)) :
    ‖polynomialFockTangentGauge m x F z‖ ^ 2 ≤
      Real.exp (2 * polynomialFockPotential m x + 2) *
        (‖F z‖ ^ 2 * Real.exp (-2 * polynomialFockPotential m ‖z‖)) := by
  let w : ℂ := z - x
  have hw : ‖w‖ ≤ polynomialFockLocalRadius m x := by
    exact le_of_lt (by simpa [w, Metric.mem_ball, dist_eq_norm] using hz)
  have hzadd : (x : ℂ) + w = z := by dsimp [w]; abel
  have hphi := polynomialFockPotential_bregman_upper_local hm hx w hw
  rw [hzadd] at hphi
  have hexp :
      -2 * polynomialFockRadialSlope m x * (z.re - x) ≤
        2 * polynomialFockPotential m x + 2 - 2 * polynomialFockPotential m ‖z‖ := by
    have hwre : w.re = z.re - x := by simp [w]
    rw [hwre] at hphi
    linarith
  rw [normSq_polynomialFockTangentGauge]
  calc
    ‖F z‖ ^ 2 * Real.exp (-2 * polynomialFockRadialSlope m x * (z.re - x)) ≤
        ‖F z‖ ^ 2 * Real.exp
          (2 * polynomialFockPotential m x + 2 - 2 * polynomialFockPotential m ‖z‖) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (sq_nonneg _)
    _ = Real.exp (2 * polynomialFockPotential m x + 2) *
        (‖F z‖ ^ 2 * Real.exp (-2 * polynomialFockPotential m ‖z‖)) := by
      rw [show 2 * polynomialFockPotential m x + 2 -
          2 * polynomialFockPotential m ‖z‖ =
        (2 * polynomialFockPotential m x + 2) +
          (-2 * polynomialFockPotential m ‖z‖) by ring, Real.exp_add]
      ring

/-- Local weighted mean-value estimate at every nonnegative real center. -/
theorem polynomialFock_local_weighted_mean
    {m x : ℝ} (hm : 4 ≤ m) (hx : 0 ≤ x) (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    Real.pi * polynomialFockLocalRadius m x ^ 2 * ‖F (x : ℂ)‖ ^ 2 ≤
      Real.exp (2 * polynomialFockPotential m x + 2) *
        ∫ z in Metric.ball (x : ℂ) (polynomialFockLocalRadius m x),
          ‖F z‖ ^ 2 * Real.exp (-2 * polynomialFockPotential m ‖z‖) := by
  let G : ℂ → ℂ := polynomialFockTangentGauge m x F
  have hG := differentiable_polynomialFockTangentGauge m x F hF
  have hmean := GaloisForLFunctions.HTGeometry.normSq_value_mul_area_le_integral_ball
    (R := polynomialFockLocalRadius m x) G hG (x : ℂ)
      (polynomialFockLocalRadius_pos (m := m) (x := x) hm)
  have hGx : G (x : ℂ) = F (x : ℂ) := by simp [G, polynomialFockTangentGauge]
  rw [hGx] at hmean
  let W : ℂ → ℝ := fun z =>
    Real.exp (2 * polynomialFockPotential m x + 2) *
      (‖F z‖ ^ 2 * Real.exp (-2 * polynomialFockPotential m ‖z‖))
  have hGint : IntegrableOn (fun z => ‖G z‖ ^ 2)
      (Metric.ball (x : ℂ) (polynomialFockLocalRadius m x)) := by
    apply ((hG.continuous.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (x : ℂ) (polynomialFockLocalRadius m x))).mono_set
    exact Metric.ball_subset_closedBall
  have hWcont : Continuous W := by
    unfold W
    exact continuous_const.mul ((hF.continuous.norm.pow 2).mul
      (Real.continuous_exp.comp
        (continuous_const.mul
          ((continuous_polynomialFockPotential m).comp continuous_norm))))
  have hWint : IntegrableOn W
      (Metric.ball (x : ℂ) (polynomialFockLocalRadius m x)) := by
    apply (hWcont.continuousOn.integrableOn_compact
      (isCompact_closedBall (x : ℂ) (polynomialFockLocalRadius m x))).mono_set
    exact Metric.ball_subset_closedBall
  have hint :
      (∫ z in Metric.ball (x : ℂ) (polynomialFockLocalRadius m x), ‖G z‖ ^ 2) ≤
        ∫ z in Metric.ball (x : ℂ) (polynomialFockLocalRadius m x), W z := by
    change Integrable (fun z => ‖G z‖ ^ 2)
      (volume.restrict (Metric.ball (x : ℂ) (polynomialFockLocalRadius m x))) at hGint
    change Integrable W
      (volume.restrict (Metric.ball (x : ℂ) (polynomialFockLocalRadius m x))) at hWint
    apply MeasureTheory.integral_mono_ae hGint hWint
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact normSq_polynomialFockTangentGauge_le_weighted hm hx F z hz
  calc
    Real.pi * polynomialFockLocalRadius m x ^ 2 * ‖F (x : ℂ)‖ ^ 2 ≤
        ∫ z in Metric.ball (x : ℂ) (polynomialFockLocalRadius m x), ‖G z‖ ^ 2 := hmean
    _ ≤ ∫ z in Metric.ball (x : ℂ) (polynomialFockLocalRadius m x), W z := hint
    _ = Real.exp (2 * polynomialFockPotential m x + 2) *
        ∫ z in Metric.ball (x : ℂ) (polynomialFockLocalRadius m x),
          ‖F z‖ ^ 2 * Real.exp (-2 * polynomialFockPotential m ‖z‖) := by
      rw [MeasureTheory.integral_const_mul]

/-! ## Exact tangent-radius and normalized-kernel form -/

theorem normSq_inner_normalizedMomentFockKernel_mul_kernelNormSq
    (d : MomentFockData) (z : ℂ) (f : MomentFock) :
    ‖inner ℂ (normalizedMomentFockKernel d z) f‖ ^ 2 * ‖momentFockKernel d z‖ ^ 2 =
      ‖momentFockEvaluation d z f‖ ^ 2 := by
  have hK : ‖momentFockKernel d z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (momentFockKernel_ne_zero d z)
  rw [normalizedMomentFockKernel, inner_smul_left]
  simp only [map_inv₀, Complex.conj_ofReal, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [momentFockEvaluation_apply]
  field_simp

theorem polynomialFockPotential_bregman_upper_tangentRadius'
    {m x : ℝ} (hm : 4 ≤ m) (hx : 0 ≤ x) {z : ℂ}
    (hz : z ∈ Metric.ball (x : ℂ) (polynomialFockTangentRadius m x)) :
    polynomialFockPotential m ‖z‖ ≤
      polynomialFockPotential m x + polynomialFockRadialSlope m x * (z.re - x) +
        polynomialFockLocalBregmanConstant m / m := by
  let w : ℂ := z - x
  have hw : ‖w‖ ≤ polynomialFockTangentRadius m x :=
    le_of_lt (by simpa [w, Metric.mem_ball, dist_eq_norm] using hz)
  have h := polynomialFockPotential_bregman_upper_tangentRadius hm hx hw
  have hzadd : (x : ℂ) + w = z := by dsimp [w]; abel
  have hwre : w.re = z.re - x := by simp [w]
  rw [hzadd, hwre] at h
  linarith

theorem normSq_polynomialFockTangentGauge_le_weighted_tangentRadius
    {m x : ℝ} (hm : 4 ≤ m) (hx : 0 ≤ x) (F : ℂ → ℂ) (z : ℂ)
    (hz : z ∈ Metric.ball (x : ℂ) (polynomialFockTangentRadius m x)) :
    ‖polynomialFockTangentGauge m x F z‖ ^ 2 ≤
      Real.exp (2 * polynomialFockPotential m x +
          2 * (polynomialFockLocalBregmanConstant m / m)) *
        (‖F z‖ ^ 2 * Real.exp (-2 * polynomialFockPotential m ‖z‖)) := by
  have hphi := polynomialFockPotential_bregman_upper_tangentRadius' hm hx hz
  have hexp :
      -2 * polynomialFockRadialSlope m x * (z.re - x) ≤
        2 * polynomialFockPotential m x +
          2 * (polynomialFockLocalBregmanConstant m / m) -
            2 * polynomialFockPotential m ‖z‖ := by
    linarith
  rw [normSq_polynomialFockTangentGauge]
  calc
    ‖F z‖ ^ 2 * Real.exp (-2 * polynomialFockRadialSlope m x * (z.re - x)) ≤
        ‖F z‖ ^ 2 * Real.exp
          (2 * polynomialFockPotential m x +
            2 * (polynomialFockLocalBregmanConstant m / m) -
              2 * polynomialFockPotential m ‖z‖) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (sq_nonneg _)
    _ = Real.exp (2 * polynomialFockPotential m x +
          2 * (polynomialFockLocalBregmanConstant m / m)) *
        (‖F z‖ ^ 2 * Real.exp (-2 * polynomialFockPotential m ‖z‖)) := by
      rw [show 2 * polynomialFockPotential m x +
          2 * (polynomialFockLocalBregmanConstant m / m) -
            2 * polynomialFockPotential m ‖z‖ =
        (2 * polynomialFockPotential m x +
          2 * (polynomialFockLocalBregmanConstant m / m)) +
            (-2 * polynomialFockPotential m ‖z‖) by ring, Real.exp_add]
      ring

theorem polynomialFock_tangentRadius_weighted_mean
    {m x : ℝ} (hm : 4 ≤ m) (hx : 0 ≤ x) (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    Real.pi * polynomialFockTangentRadius m x ^ 2 * ‖F (x : ℂ)‖ ^ 2 ≤
      Real.exp (2 * polynomialFockPotential m x +
        2 * (polynomialFockLocalBregmanConstant m / m)) *
        ∫ z in Metric.ball (x : ℂ) (polynomialFockTangentRadius m x),
          ‖F z‖ ^ 2 * Real.exp (-2 * polynomialFockPotential m ‖z‖) := by
  let G : ℂ → ℂ := polynomialFockTangentGauge m x F
  have hG := differentiable_polynomialFockTangentGauge m x F hF
  have hmean := GaloisForLFunctions.HTGeometry.normSq_value_mul_area_le_integral_ball
    (R := polynomialFockTangentRadius m x) G hG (x : ℂ)
      (polynomialFockTangentRadius_pos (by linarith))
  have hGx : G (x : ℂ) = F (x : ℂ) := by simp [G, polynomialFockTangentGauge]
  rw [hGx] at hmean
  let W : ℂ → ℝ := fun z =>
    Real.exp (2 * polynomialFockPotential m x +
      2 * (polynomialFockLocalBregmanConstant m / m)) *
      (‖F z‖ ^ 2 * Real.exp (-2 * polynomialFockPotential m ‖z‖))
  have hGint : IntegrableOn (fun z => ‖G z‖ ^ 2)
      (Metric.ball (x : ℂ) (polynomialFockTangentRadius m x)) := by
    apply ((hG.continuous.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (x : ℂ) (polynomialFockTangentRadius m x))).mono_set
    exact Metric.ball_subset_closedBall
  have hWcont : Continuous W := by
    unfold W
    exact continuous_const.mul ((hF.continuous.norm.pow 2).mul
      (Real.continuous_exp.comp
        (continuous_const.mul
          ((continuous_polynomialFockPotential m).comp continuous_norm))))
  have hWint : IntegrableOn W
      (Metric.ball (x : ℂ) (polynomialFockTangentRadius m x)) := by
    apply (hWcont.continuousOn.integrableOn_compact
      (isCompact_closedBall (x : ℂ) (polynomialFockTangentRadius m x))).mono_set
    exact Metric.ball_subset_closedBall
  have hint :
      (∫ z in Metric.ball (x : ℂ) (polynomialFockTangentRadius m x), ‖G z‖ ^ 2) ≤
        ∫ z in Metric.ball (x : ℂ) (polynomialFockTangentRadius m x), W z := by
    change Integrable (fun z => ‖G z‖ ^ 2)
      (volume.restrict (Metric.ball (x : ℂ) (polynomialFockTangentRadius m x))) at hGint
    change Integrable W
      (volume.restrict (Metric.ball (x : ℂ) (polynomialFockTangentRadius m x))) at hWint
    apply MeasureTheory.integral_mono_ae hGint hWint
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact normSq_polynomialFockTangentGauge_le_weighted_tangentRadius hm hx F z hz
  calc
    Real.pi * polynomialFockTangentRadius m x ^ 2 * ‖F (x : ℂ)‖ ^ 2 ≤
        ∫ z in Metric.ball (x : ℂ) (polynomialFockTangentRadius m x), ‖G z‖ ^ 2 := hmean
    _ ≤ ∫ z in Metric.ball (x : ℂ) (polynomialFockTangentRadius m x), W z := hint
    _ = Real.exp (2 * polynomialFockPotential m x +
        2 * (polynomialFockLocalBregmanConstant m / m)) *
        ∫ z in Metric.ball (x : ℂ) (polynomialFockTangentRadius m x),
          ‖F z‖ ^ 2 * Real.exp (-2 * polynomialFockPotential m ‖z‖) := by
      rw [MeasureTheory.integral_const_mul]

/-- A normalized polynomial-moment Fock evaluation is controlled by one exact adapted ball. -/
theorem normSq_inner_normalizedPolynomialMomentFockKernel_le_localIntegral
    {m x : ℝ} (hm : 4 ≤ m) (hx : 0 ≤ x) (f : MomentFock) :
    ‖inner ℂ (normalizedMomentFockKernel
        (polynomialMomentFockData m (by linarith)) (x : ℂ)) f‖ ^ 2 ≤
      Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
        ∫ z in Metric.ball (x : ℂ) (polynomialFockTangentRadius m x),
          polynomialMomentFockWeightedNormSq m (by linarith) f z := by
  let hm2 : 2 ≤ m := by linarith
  let d : MomentFockData := polynomialMomentFockData m hm2
  let a : ℝ := ‖inner ℂ (normalizedMomentFockKernel d (x : ℂ)) f‖ ^ 2
  let K : ℝ := ‖momentFockKernel d (x : ℂ)‖ ^ 2
  let E : ℝ := Real.exp (2 * polynomialFockPotential m x)
  let C : ℝ := Real.exp (2 * (polynomialFockLocalBregmanConstant m / m))
  let I : ℝ := ∫ z in Metric.ball (x : ℂ) (polynomialFockTangentRadius m x),
    polynomialMomentFockWeightedNormSq m hm2 f z
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hKpos : 0 < K := by
    dsimp [K, d]
    exact sq_pos_of_pos (norm_pos_iff.mpr (momentFockKernel_ne_zero _ _))
  have hE : 0 < E := by dsimp [E]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hI : 0 ≤ I := by
    dsimp [I]
    apply MeasureTheory.integral_nonneg
    intro z
    unfold polynomialMomentFockWeightedNormSq
    positivity
  have hid : a * K = ‖polynomialMomentFockEvaluation m hm2 (x : ℂ) f‖ ^ 2 := by
    dsimp [a, K, d]
    exact normSq_inner_normalizedMomentFockKernel_mul_kernelNormSq _ _ _
  have hmean := polynomialFock_tangentRadius_weighted_mean hm hx
    (polynomialMomentFockFunction m hm2 f)
    (differentiable_polynomialMomentFockFunction m hm2 f)
  have hmean' :
      Real.pi * polynomialFockTangentRadius m x ^ 2 *
          ‖polynomialMomentFockEvaluation m hm2 (x : ℂ) f‖ ^ 2 ≤ E * C * I := by
    rw [polynomialMomentFockFunction_eq_evaluation] at hmean
    have hdensity : (fun z =>
        ‖polynomialMomentFockFunction m hm2 f z‖ ^ 2 *
          Real.exp (-2 * polynomialFockPotential m ‖z‖)) =
        polynomialMomentFockWeightedNormSq m hm2 f := by
      funext z
      rfl
    rw [hdensity] at hmean
    simpa [E, C, I, Real.exp_add] using hmean
  have hkernel := normSq_polynomialMomentFockKernel_lower hm2 x
  have hradius := polynomialFockTangentRadius_sq (m := m) (x := x) (by linarith)
  have hscale : 0 < m * (1 + x ^ 2) ^ (m / 2 - 1) := by positivity
  have hden : E ≤ Real.pi * polynomialFockTangentRadius m x ^ 2 * K := by
    dsimp [E, K, d]
    rw [hradius]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    calc
      Real.exp (2 * polynomialFockPotential m x) =
          Real.pi * (m * (1 + x ^ 2) ^ (m / 2 - 1))⁻¹ *
            (Real.exp (2 * polynomialFockPotential m x) *
              (m * (1 + x ^ 2) ^ (m / 2 - 1) / Real.pi)) := by
        field_simp
      _ ≤ Real.pi * (m * (1 + x ^ 2) ^ (m / 2 - 1))⁻¹ *
          ‖momentFockKernel (polynomialMomentFockData m hm2) (x : ℂ)‖ ^ 2 := by
        gcongr
  have hleft : E * a ≤
      Real.pi * polynomialFockTangentRadius m x ^ 2 * K * a := by
    exact mul_le_mul_of_nonneg_right hden ha
  have hright :
      Real.pi * polynomialFockTangentRadius m x ^ 2 * K * a ≤ E * C * I := by
    calc
      Real.pi * polynomialFockTangentRadius m x ^ 2 * K * a =
          Real.pi * polynomialFockTangentRadius m x ^ 2 * (a * K) := by ring
      _ = Real.pi * polynomialFockTangentRadius m x ^ 2 *
          ‖polynomialMomentFockEvaluation m hm2 (x : ℂ) f‖ ^ 2 := by rw [hid]
      _ ≤ E * C * I := hmean'
  have hcancel : E * a ≤ E * (C * I) := by
    calc
      E * a ≤ Real.pi * polynomialFockTangentRadius m x ^ 2 * K * a := hleft
      _ ≤ E * C * I := hright
      _ = E * (C * I) := by ring
  exact le_of_mul_le_mul_left hcancel hE

end

end RHTower
