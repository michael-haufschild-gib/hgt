import GaloisForLFunctions.RHTower.XiSliceDenseGaussianTail
import GaloisForLFunctions.RHTower.XiSliceGaussianTailRealBounds
import GaloisForLFunctions.RHTower.XiSliceHeatGaussianSharpThreshold
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Gaussian heat of the actual Xi tail

Reflection pairing makes the radius tail positive on the real axis. Its global
fourth-moment Gaussian bound proves heat integrability and an explicit one-sided
comparison with the Gaussian heat background. At height `exp(u⁴)`, cutoff `u³`,
and scaled heat `κ/a` with `0 < κ < 1/2`, the normalized heat integral converges
to one uniformly on bounded real intervals.
-/

open MeasureTheory Filter Topology
namespace RHTower.DeBruijn
noncomputable section

/-- The literal Gaussian heat integral of the real, positively oriented Xi tail. -/
def xiSliceGaussianTailHeat (t R lam x : ℝ) : ℝ :=
  ∫ u : ℝ, gaussDensity (lam / 2) u *
    (xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) ((x + u : ℝ) : ℂ)).re

/-- The exact Gaussian heat background with the tail's oriented quadratic coefficient. -/
def xiSliceGaussianTailHeatReference (t R lam x : ℝ) : ℝ :=
  let a := (xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R)).re
  gaussianModelScale a lam ^ (-(1 / 2 : ℝ)) *
    Real.exp (a / gaussianModelScale a lam * x ^ 2)

private theorem measurable_gaussianTail_real (t R : ℝ) :
    Measurable (fun x : ℝ => xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) (x : ℂ)) := by
  unfold xiSliceGaussianTail
  apply Measurable.tprod
  intro q
  fun_prop

private theorem gaussianTail_real_re_eq_norm (t : ℝ) {R : ℝ} (hR : 4 ≤ R) (x : ℝ) :
    (xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) (x : ℂ)).re =
      ‖xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) (x : ℂ)‖ := by
  simpa only [Complex.ofReal_re] using congrArg Complex.re
    (xiSliceGaussianTail_real_eq_norm t hR x)

private theorem gaussian_background_heat {a lam : ℝ} (hlam : 0 < lam)
    (hconv : 2 * a * lam < 1) (x : ℝ) :
    Integrable (fun u : ℝ => gaussDensity (lam / 2) u * Real.exp (a * (x + u) ^ 2)) ∧
    (∫ u : ℝ, gaussDensity (lam / 2) u * Real.exp (a * (x + u) ^ 2)) =
      gaussianModelScale a lam ^ (-(1 / 2 : ℝ)) *
        Real.exp (a / gaussianModelScale a lam * x ^ 2) := by
  have hvar : 0 < (lam / gaussianModelScale a lam) / 2 := by
    have hm := gaussianModelScale_pos hconv
    positivity
  have hi : Integrable (fun u : ℝ => gaussDensity ((lam / gaussianModelScale a lam) / 2) u) := by
    simpa only [pow_zero, mul_one] using integrable_gaussDensity_mul_pow hvar 0
  have hv : (∫ u : ℝ, gaussDensity ((lam / gaussianModelScale a lam) / 2) u) = 1 := by
    simpa only [mul_zero, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one] using
      integral_gaussDensity_mul_pow_even hvar 0
  constructor
  · simp_rw [gaussDensity_mul_exp_sq_mehler hlam hconv]
    exact (hi.comp_sub_right _).const_mul _
  · simp_rw [gaussDensity_mul_exp_sq_mehler hlam hconv]
    rw [integral_const_mul, integral_sub_right_eq_self, hv, mul_one]

private theorem gaussianTail_real_gap (t : ℝ) {R : ℝ} (hR : 4 ≤ R) (y : ℝ) :
    let a := (xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R)).re
    let B := xiSliceGaussianTailFourth t (xiSliceGaussianRadiusHead t R)
    0 ≤ Real.exp (a * y ^ 2) -
      (xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) (y : ℂ)).re ∧
    Real.exp (a * y ^ 2) -
      (xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) (y : ℂ)).re ≤
        B * y ^ 4 * Real.exp (a * y ^ 2) := by
  dsimp only
  rw [gaussianTail_real_re_eq_norm t hR y]
  let a := (xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R)).re
  let B := xiSliceGaussianTailFourth t (xiSliceGaussianRadiusHead t R)
  have hb := norm_xiSliceGaussianTail_real_bounds t hR y
  change Real.exp (y ^ 2 * a - y ^ 4 * B) ≤ _ ∧ _ ≤ Real.exp (y ^ 2 * a) at hb
  rw [mul_comm (y ^ 2) a, mul_comm (y ^ 4) B] at hb
  refine ⟨sub_nonneg.mpr hb.2, ?_⟩
  have hlow : Real.exp (a * y ^ 2) * (1 - B * y ^ 4) ≤
      ‖xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) (y : ℂ)‖ := by
    calc
      _ ≤ Real.exp (a * y ^ 2) * Real.exp (-(B * y ^ 4)) :=
        mul_le_mul_of_nonneg_left (by linarith only [Real.add_one_le_exp (-(B * y ^ 4))])
          (Real.exp_pos _).le
      _ = Real.exp (a * y ^ 2 - B * y ^ 4) := (Real.exp_add _ _).symm
      _ ≤ _ := hb.1
  nlinarith only [hlow]

/-- The actual Xi tail is integrable against the heat kernel throughout its Gaussian chamber. -/
theorem integrable_xiSliceGaussianTailHeat (t : ℝ) {R lam : ℝ} (hR : 4 ≤ R)
    (hlam : 0 < lam)
    (hconv : 2 * (xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R)).re * lam < 1)
    (x : ℝ) :
    Integrable (fun u : ℝ => gaussDensity (lam / 2) u *
      (xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) ((x + u : ℝ) : ℂ)).re) := by
  have hg := (gaussian_background_heat hlam hconv x).1
  have hm : Measurable (fun u : ℝ => gaussDensity (lam / 2) u *
      (xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) ((x + u : ℝ) : ℂ)).re) := by
    have htail := Complex.continuous_re.measurable.comp (measurable_gaussianTail_real t R)
    have hd : Measurable (fun u : ℝ => gaussDensity (lam / 2) u) := by
      unfold gaussDensity
      fun_prop
    exact hd.mul (htail.comp (measurable_const.add measurable_id))
  apply hg.mono' hm.aestronglyMeasurable
  filter_upwards [] with u
  have hd : 0 ≤ gaussDensity (lam / 2) u := by unfold gaussDensity; positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hd, gaussianTail_real_re_eq_norm t hR,
    abs_of_nonneg (norm_nonneg _)]
  have hbound := (norm_xiSliceGaussianTail_real_bounds t hR (x + u)).2
  rw [mul_comm ((x + u) ^ 2)] at hbound
  exact mul_le_mul_of_nonneg_left hbound hd

/-- The Gaussian reference overestimates the actual heated tail by an explicit fourth moment. -/
theorem xiSliceGaussianTailHeat_bounds (t : ℝ) {R lam : ℝ} (hR : 4 ≤ R)
    (hlam : 0 < lam)
    (hconv : 2 * (xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R)).re * lam < 1)
    (x : ℝ) :
    0 ≤ xiSliceGaussianTailHeatReference t R lam x - xiSliceGaussianTailHeat t R lam x ∧
    xiSliceGaussianTailHeatReference t R lam x - xiSliceGaussianTailHeat t R lam x ≤
      xiSliceGaussianTailFourth t (xiSliceGaussianRadiusHead t R) *
        gaussianModelHeat 0 (xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R)).re lam x := by
  let a := (xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R)).re
  let B := xiSliceGaussianTailFourth t (xiSliceGaussianRadiusHead t R)
  let E : ℝ → ℝ := fun u => gaussDensity (lam / 2) u *
    (Real.exp (a * (x + u) ^ 2) -
      (xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) ((x + u : ℝ) : ℂ)).re)
  obtain ⟨hg, hgval⟩ := gaussian_background_heat hlam hconv x
  have hf := integrable_xiSliceGaussianTailHeat t hR hlam hconv x
  have hE : Integrable E := (hg.sub hf).congr (Eventually.of_forall fun u => by
    dsimp only [E, Pi.sub_apply]
    ring)
  have hEval : (∫ u, E u) = xiSliceGaussianTailHeatReference t R lam x -
      xiSliceGaussianTailHeat t R lam x := by
    have heq : E = fun u => gaussDensity (lam / 2) u * Real.exp (a * (x + u) ^ 2) -
        gaussDensity (lam / 2) u *
          (xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) ((x + u : ℝ) : ℂ)).re := by
      funext u
      dsimp only [E]
      ring
    rw [heq, integral_sub hg hf, hgval]
    rfl
  have hmajor := (integrable_and_integral_gaussianModel hlam hconv 0 x).1.const_mul B
  rw [← hEval]
  constructor
  · apply integral_nonneg
    intro u
    exact mul_nonneg (by unfold gaussDensity; positivity) (gaussianTail_real_gap t hR (x + u)).1
  · have hle : (∫ u, E u) ≤ ∫ u, B * (gaussDensity (lam / 2) u * gaussianModel 0 a (x + u)) := by
      apply integral_mono hE hmajor
      intro u
      have h := mul_le_mul_of_nonneg_left (gaussianTail_real_gap t hR (x + u)).2
        (show 0 ≤ gaussDensity (lam / 2) u by unfold gaussDensity; positivity)
      calc
        E u ≤ gaussDensity (lam / 2) u * (B * (x + u) ^ 4 * Real.exp (a * (x + u) ^ 2)) := h
        _ = B * (gaussDensity (lam / 2) u * gaussianModel 0 a (x + u)) := by
          dsimp only [gaussianModel]
          ring
    rw [integral_const_mul] at hle
    exact hle

/-- The actual heated tail has an explicit relative error bounded by the Gaussian fourth moment. -/
theorem abs_xiSliceGaussianTailHeat_relative_error_le (t : ℝ) {R lam : ℝ} (hR : 4 ≤ R)
    (hlam : 0 < lam)
    (hconv : 2 * (xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R)).re * lam < 1)
    (x : ℝ) :
    let a := (xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R)).re
    |xiSliceGaussianTailHeat t R lam x / xiSliceGaussianTailHeatReference t R lam x - 1| ≤
      xiSliceGaussianTailFourth t (xiSliceGaussianRadiusHead t R) *
        coshModelQuartic 0 (lam / gaussianModelScale a lam) (x / gaussianModelScale a lam) := by
  dsimp only
  let a := (xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R)).re
  let G := xiSliceGaussianTailHeatReference t R lam x
  have hG : 0 < G := by
    dsimp only [G, xiSliceGaussianTailHeatReference]
    have hm := gaussianModelScale_pos hconv
    positivity
  have hb := xiSliceGaussianTailHeat_bounds t hR hlam hconv x
  rw [gaussianModelHeat_eq hlam hconv] at hb
  have hF : xiSliceGaussianTailHeat t R lam x ≤ G := sub_nonneg.mp hb.1
  have hn : xiSliceGaussianTailHeat t R lam x / G - 1 ≤ 0 := by
    apply sub_nonpos.mpr
    exact (div_le_one hG).2 hF
  rw [abs_of_nonpos hn]
  have heq : -(xiSliceGaussianTailHeat t R lam x / G - 1) =
      (G - xiSliceGaussianTailHeat t R lam x) / G := by
        field_simp [hG.ne']
        ring
  rw [heq]
  apply (div_le_iff₀ hG).2
  simpa only [G, xiSliceGaussianTailHeatReference, mul_assoc, mul_comm, mul_left_comm] using hb.2

private theorem dense_gaussian_fourth_tendsto_zero :
    Tendsto (fun u : ℝ => xiSliceGaussianTailFourth (Real.exp (u ^ 4))
      (xiSliceGaussianRadiusHead (Real.exp (u ^ 4)) (u ^ 3))) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => tsum_nonneg (fun _ => sq_nonneg _)))
    ?_ tendsto_xiSliceDenseGaussianFourth_mul_coefficient_sq
  filter_upwards [tendsto_xiSliceDenseGaussianCoefficient_atTop.eventually_ge_atTop 1]
    with u hu
  exact le_mul_of_one_le_right (tsum_nonneg (fun _ => sq_nonneg _)) (one_le_pow₀ hu)

/-- Heat of the dense source tail, divided by its exact Gaussian heat reference. -/
def xiSliceDenseGaussianHeatNormalized (κ u x : ℝ) : ℝ :=
  xiSliceGaussianTailHeat (Real.exp (u ^ 4)) (u ^ 3)
      (κ / xiSliceDenseGaussianCoefficient u) x /
    xiSliceGaussianTailHeatReference (Real.exp (u ^ 4)) (u ^ 3)
      (κ / xiSliceDenseGaussianCoefficient u) x

/-- The actual dense Gaussian background remains Gaussian after heat at every fixed
subcritical scaled time, uniformly on bounded real intervals. -/
theorem tendstoUniformlyOn_xiSliceDenseGaussianHeatNormalized
    {κ : ℝ} (hκ : 0 < κ) (hκhalf : κ < 1 / 2) (M : ℝ) :
    TendstoUniformlyOn (fun u x : ℝ => xiSliceDenseGaussianHeatNormalized κ u x)
      (fun _ => 1) atTop (Metric.closedBall 0 M) := by
  let μ := 1 - 2 * κ
  let K := max M 0
  let Q := (K / μ) ^ 4 + 6 * (κ / μ) * (K / μ) ^ 2 + 3 * (κ / μ) ^ 2
  have hμ : 0 < μ := by dsimp only [μ]; linarith only [hκhalf]
  have hK : 0 ≤ K := le_max_right _ _
  have hlim : Tendsto (fun u : ℝ =>
      xiSliceGaussianTailFourth (Real.exp (u ^ 4))
        (xiSliceGaussianRadiusHead (Real.exp (u ^ 4)) (u ^ 3)) * Q) atTop (𝓝 0) := by
    simpa only [zero_mul] using dense_gaussian_fourth_tendsto_zero.mul_const Q
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [tendsto_xiSliceDenseGaussianCoefficient_atTop.eventually_ge_atTop 1,
    (tendsto_pow_atTop (by decide : 3 ≠ 0)).eventually_ge_atTop (4 : ℝ),
    hlim.eventually (gt_mem_nhds hε)] with u ha1 hR hsmall
  intro x hx
  let a := xiSliceDenseGaussianCoefficient u
  have ha : 0 < a := zero_lt_one.trans_le ha1
  have hheat : 0 < κ / a := div_pos hκ ha
  have hprod : 2 * a * (κ / a) = 2 * κ := by field_simp [ha.ne']
  have hconv : 2 * a * (κ / a) < 1 := by rw [hprod]; linarith only [hκhalf]
  have hscale : gaussianModelScale a (κ / a) = μ := by
    rw [gaussianModelScale, hprod]
  have hxK : |x| ≤ K := by
    have h : ‖x‖ ≤ K := (mem_closedBall_zero_iff.mp hx).trans (le_max_left M 0)
    simpa only [Real.norm_eq_abs] using h
  have hy : |x / μ| ≤ K / μ := by
    rw [abs_div, abs_of_pos hμ]
    exact div_le_div_of_nonneg_right hxK hμ.le
  have hysq : (x / μ) ^ 2 ≤ (K / μ) ^ 2 := by
    apply sq_le_sq.mpr
    simpa only [abs_of_nonneg (div_nonneg hK hμ.le)] using hy
  have hyfourth : (x / μ) ^ 4 ≤ (K / μ) ^ 4 := by
    nlinarith only [mul_self_le_mul_self (sq_nonneg (x / μ)) hysq]
  have hv0 : 0 ≤ (κ / a) / μ := (div_pos hheat hμ).le
  have hv : (κ / a) / μ ≤ κ / μ :=
    div_le_div_of_nonneg_right (div_le_self hκ.le ha1) hμ.le
  have hQ : coshModelQuartic 0 ((κ / a) / μ) (x / μ) ≤ Q := by
    have hmid := mul_le_mul (mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 6))
      hysq (sq_nonneg _) (by positivity : 0 ≤ 6 * (κ / μ))
    have hlast := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv0 hv 2) (by norm_num : (0 : ℝ) ≤ 3)
    dsimp only [coshModelQuartic, Q]
    nlinarith only [hyfourth, hmid, hlast]
  have he := abs_xiSliceGaussianTailHeat_relative_error_le (Real.exp (u ^ 4)) hR hheat hconv x
  change |xiSliceDenseGaussianHeatNormalized κ u x - 1| ≤
    xiSliceGaussianTailFourth (Real.exp (u ^ 4))
      (xiSliceGaussianRadiusHead (Real.exp (u ^ 4)) (u ^ 3)) *
        coshModelQuartic 0 ((κ / a) / gaussianModelScale a (κ / a))
          (x / gaussianModelScale a (κ / a)) at he
  rw [hscale] at he
  have hB : 0 ≤ xiSliceGaussianTailFourth (Real.exp (u ^ 4))
      (xiSliceGaussianRadiusHead (Real.exp (u ^ 4)) (u ^ 3)) := tsum_nonneg (fun _ => sq_nonneg _)
  rw [dist_eq_norm, norm_sub_rev, Real.norm_eq_abs]
  exact he.trans_lt ((mul_le_mul_of_nonneg_left hQ hB).trans_lt hsmall)

end
end RHTower.DeBruijn

