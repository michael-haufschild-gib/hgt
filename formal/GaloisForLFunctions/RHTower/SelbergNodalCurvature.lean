import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact nodal curvature surviving integration

For the local real profile h(x)=x, the regularized amplitude sqrt(x²+e²) has
curvature e²/(x²+e²)^(3/2). Actual FTC gives its integral on [-1,1]; the integral
tends to two while the curvature tends to zero almost everywhere. The positive
survivor is an exact nodal curvature formula, not an assertion about an actual
Maass eigenform. This profile is not periodic, modular invariant, or cuspidal.
-/

open Set Filter Topology MeasureTheory
namespace GaloisForLFunctions.RHTower.SelbergNodalCurvature
noncomputable section

/-- Exact regularized amplitude of the local real nodal profile h(x)=x. -/
def radius (e x : ℝ) : ℝ := Real.sqrt (x ^ (2 : ℕ) + e ^ (2 : ℕ))

/-- Its inverse-amplitude weighted regularized residual. -/
def curvature (e x : ℝ) : ℝ := e ^ (2 : ℕ) / radius e x ^ (3 : ℕ)

/-- Exact square of the local regularized amplitude. -/
theorem radius_sq (e x : ℝ) : radius e x ^ (2 : ℕ) = x ^ (2 : ℕ) + e ^ (2 : ℕ) :=
  Real.sq_sqrt (add_nonneg (sq_nonneg x) (sq_nonneg e))

/-- Positive regularization removes the node from the denominator. -/
theorem radius_pos {e : ℝ} (he : 0 < e) (x : ℝ) : 0 < radius e x :=
  Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos he))

/-- The actual first derivative of the regularized nodal amplitude. -/
theorem radius_hasDerivAt {e : ℝ} (he : 0 < e) (x : ℝ) :
    HasDerivAt (radius e) (x / radius e x) x := by
  have h := (((hasDerivAt_id x).fun_pow 2).add_const (e ^ (2 : ℕ))).sqrt
    (add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_pos he)).ne'
  convert h using 1
  · rfl
  · simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, radius]
    ring

/-- The curvature density is the actual derivative of the normalized nodal flux. -/
theorem curvature_hasPrimitive {e : ℝ} (he : 0 < e) (x : ℝ) :
    HasDerivAt (fun t => t / radius e t) (curvature e x) x := by
  have h := (hasDerivAt_id x).div (radius_hasDerivAt he x) (radius_pos he x).ne'
  apply h.congr_deriv
  simp only [id_eq, one_mul]
  unfold curvature
  have hr := (radius_pos he x).ne'
  field_simp
  nlinarith [radius_sq e x]

/-- The curvature is the literal second derivative, not a postulated nodal charge. -/
theorem curvature_eq_second_derivative {e : ℝ} (he : 0 < e) (x : ℝ) :
    curvature e x = deriv (deriv (radius e)) x := by
  have hd : deriv (radius e) = fun t => t / radius e t := funext (fun t => (radius_hasDerivAt he t).deriv)
  rw [hd]
  exact (curvature_hasPrimitive he x).deriv.symm

/-- Exact relation with the source's regularized derivative-energy remainder. -/
theorem curvature_eq_weighted_energy {e : ℝ} (he : 0 < e) (x : ℝ) :
    curvature e x = (1 - deriv (radius e) x ^ (2 : ℕ)) / radius e x := by
  rw [(radius_hasDerivAt he x).deriv]
  unfold curvature
  have hr := (radius_pos he x).ne'
  field_simp
  nlinarith [radius_sq e x]

/-- The nodal curvature is genuinely integrable on each compact interval. -/
theorem curvature_intervalIntegrable {e : ℝ} (he : 0 < e) (a b : ℝ) :
    IntervalIntegrable (curvature e) volume a b := by
  apply Continuous.intervalIntegrable
  unfold curvature radius
  apply continuous_const.div (Real.continuous_sqrt.comp (continuous_id.pow 2 |>.add continuous_const) |>.pow 3)
  intro x
  exact pow_ne_zero 3 (radius_pos he x).ne'

/-- Exact total curvature of the regularized nodal profile on the symmetric unit interval. -/
theorem integral_curvature {e : ℝ} (he : 0 < e) :
    (∫ x in (-1 : ℝ)..1, curvature e x) = 2 / Real.sqrt (1 + e ^ (2 : ℕ)) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => curvature_hasPrimitive he x)
    (curvature_intervalIntegrable he _ _)]
  norm_num [radius]
  ring

/-- Exact curvature on every oriented compact interval, including an endpoint at the node. -/
theorem integral_curvature_endpoints {e : ℝ} (he : 0 < e) (a b : ℝ) :
    (∫ x in a..b, curvature e x) = b / radius e b - a / radius e a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => curvature_hasPrimitive he x)
    (curvature_intervalIntegrable he a b)

/-- Normalized nodal flux tends to the sign quotient, with the exact zero value at the node. -/
theorem flux_tendsto (x : ℝ) :
    Tendsto (fun e : ℝ => x / radius e x) (𝓝 0) (𝓝 (x / |x|)) := by
  by_cases hx : x = 0
  · simp only [hx, zero_div]
    exact tendsto_const_nhds
  · have hc : ContinuousAt (fun e : ℝ => x / radius e x) 0 := by
      apply continuousAt_const.div
        ((continuous_const.add (continuous_id.pow 2)).sqrt.continuousAt)
      simpa [radius, Real.sqrt_sq_eq_abs] using abs_ne_zero.mpr hx
    simpa [radius, Real.sqrt_sq_eq_abs] using hc.tendsto

/-- Complete oriented-interval classification of the surviving nodal curvature. -/
theorem integral_curvature_tendsto_endpoints (a b : ℝ) :
    Tendsto (fun e : ℝ => ∫ x in a..b, curvature e x) (𝓝[>] 0)
      (𝓝 (b / |b| - a / |a|)) := by
  apply (((flux_tendsto b).sub (flux_tendsto a)).mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with e he
  exact (integral_curvature_endpoints he a b).symm

/-- The pointwise curvature vanishes in the zero-regulator limit away from the node. -/
theorem curvature_tendsto_zero {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun e : ℝ => curvature e x) (𝓝 0) (𝓝 0) := by
  have hd : Real.sqrt (x ^ (2 : ℕ) + (0 : ℝ) ^ (2 : ℕ)) ^ (3 : ℕ) ≠ 0 := by
    apply pow_ne_zero 3
    apply (Real.sqrt_pos.mpr ?_).ne'
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using sq_pos_of_ne_zero hx
  have hc : ContinuousAt (fun e : ℝ => curvature e x) 0 := by
    unfold curvature radius
    exact (continuousAt_id.pow 2).div
      (((continuous_const.add (continuous_id.pow 2)).sqrt.pow 3).continuousAt) hd
  simpa [curvature] using hc.tendsto

/-- Nevertheless the actual compact curvature integral tends to the nonzero nodal charge two. -/
theorem integral_curvature_tendsto :
    Tendsto (fun e : ℝ => ∫ x in (-1 : ℝ)..1, curvature e x) (𝓝[>] 0) (𝓝 2) := by
  have hc : ContinuousAt (fun e : ℝ => 2 / Real.sqrt (1 + e ^ (2 : ℕ))) 0 := by
    apply continuousAt_const.div
      ((continuous_const.add (continuous_id.pow 2)).sqrt.continuousAt)
    norm_num
  have hlim : Tendsto (fun e : ℝ => 2 / Real.sqrt (1 + e ^ (2 : ℕ))) (𝓝[>] 0) (𝓝 2) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with e he
  exact (integral_curvature he).symm

/-- Exact failure of discarding a nodal term by pointwise almost-everywhere convergence. -/
theorem nodal_curvature_survives_integration :
    (∀ᵐ x : ℝ ∂volume, Tendsto (fun e : ℝ => curvature e x) (𝓝[>] 0) (𝓝 0)) ∧
      Tendsto (fun e : ℝ => ∫ x in (-1 : ℝ)..1, curvature e x) (𝓝[>] 0) (𝓝 2) := by
  refine ⟨?_, integral_curvature_tendsto⟩
  filter_upwards [(Set.countable_singleton (0 : ℝ)).ae_notMem volume] with x hx
  exact (curvature_tendsto_zero hx).mono_left nhdsWithin_le_nhds

end
end GaloisForLFunctions.RHTower.SelbergNodalCurvature
