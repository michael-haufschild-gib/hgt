import GaloisForLFunctions.RHTower.BesselKZeroMoments
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Logarithmic bounds for the actual Bessel boundary kernel

The integral definition gives `exp (-r) ≤ r K₁(r) ≤ 1`. Hence `K₀(r) + log r`
has derivative in `[0,1]` on the positive half-line. These estimates supply
domination for the infinite Fourier boundary trace; no pole expansion is assumed.
This is a classical analytic bridge, not a sparse-deficit rigidity theorem.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open RHTower.BesselKZero

namespace RHTower.WeilHigherDenominator

private lemma sinh_kernel_integral {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t => Real.cosh t * Real.exp (-(r * Real.sinh t))) (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), Real.cosh t * Real.exp (-(r * Real.sinh t))) = 1 / r := by
  have hd : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun t => -Real.exp (-(r * Real.sinh t)) / r)
        (Real.cosh t * Real.exp (-(r * Real.sinh t))) t := by
    intro t _
    refine ((((((Real.hasDerivAt_sinh t).const_mul r).neg).exp).neg).div_const r).congr_deriv ?_
    dsimp
    field_simp [hr.ne']
  have hp : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ Real.cosh t * Real.exp (-(r * Real.sinh t)) := by
    intro t _
    exact mul_nonneg (Real.cosh_pos t).le (Real.exp_nonneg _)
  have he : Tendsto (fun t : ℝ => Real.exp (-(r * Real.sinh t))) atTop (𝓝 0) := by
    have ht : Tendsto (fun t : ℝ => Real.exp (-(r * t))) atTop (𝓝 0) := by
      apply Real.tendsto_exp_atBot.comp
      simpa only [id, neg_mul] using tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hr)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht ?_ ?_
    · exact Filter.Eventually.of_forall fun t => Real.exp_nonneg _
    · filter_upwards [eventually_ge_atTop 0] with t ht
      exact Real.exp_le_exp.mpr (by nlinarith [Real.self_le_sinh_iff.mpr ht])
  have hg : Tendsto (fun t : ℝ => -Real.exp (-(r * Real.sinh t)) / r) atTop (𝓝 0) := by
    simpa using he.neg.div_const r
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hp hg, ?_⟩
  simpa [div_eq_mul_inv] using integral_Ioi_of_hasDerivAt_of_nonneg' hd hp hg

/-- A global sandwich for the first Bessel moment, directly from its integral. -/
theorem kMoment_one_mul_bounds {r : ℝ} (hr : 0 < r) :
    Real.exp (-r) ≤ r * kMoment 1 r ∧ r * kMoment 1 r ≤ 1 := by
  obtain ⟨hi, he⟩ := sinh_kernel_integral hr
  have hc (t : ℝ) : Real.sinh t ≤ Real.cosh t := by
    rw [Real.sinh_eq, Real.cosh_eq]
    linarith [Real.exp_pos (-t)]
  have hc' {t : ℝ} (ht : 0 ≤ t) : Real.cosh t ≤ Real.sinh t + 1 := by
    have hex : Real.exp (-t) ≤ 1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr ht)
    rw [Real.sinh_eq, Real.cosh_eq]
    linarith
  have hu : kMoment 1 r ≤ 1 / r := by
    rw [← he, kMoment_eq]
    refine setIntegral_mono_on (integrableOn_kIntegrand 1 hr) hi measurableSet_Ioi ?_
    intro t _
    simp only [kIntegrand, pow_one]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [hc t]))
      (Real.cosh_pos t).le
  have hl : Real.exp (-r) / r ≤ kMoment 1 r := by
    rw [div_eq_mul_inv, ← one_div r, ← he, ← integral_const_mul, kMoment_eq]
    refine setIntegral_mono_on (hi.const_mul _) (integrableOn_kIntegrand 1 hr)
      measurableSet_Ioi ?_
    intro t ht
    simp only [kIntegrand, pow_one]
    calc
      Real.exp (-r) * (Real.cosh t * Real.exp (-(r * Real.sinh t))) =
          Real.cosh t * Real.exp (-r - r * Real.sinh t) := by
        rw [sub_eq_add_neg, Real.exp_add]
        ring
      _ ≤ Real.cosh t * Real.exp (-(r * Real.cosh t)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [hc' ht.le]))
          (Real.cosh_pos t).le
  constructor
  · simpa only [mul_comm] using (div_le_iff₀ hr).mp hl
  · simpa only [mul_comm] using (le_div_iff₀ hr).mp hu

/-- The logarithmic singularity has a bounded, monotone remainder. -/
def besselLogRemainder (r : ℝ) : ℝ := kMoment 0 r + Real.log r

theorem hasDerivAt_besselLogRemainder {r : ℝ} (hr : 0 < r) :
    HasDerivAt besselLogRemainder (-kMoment 1 r + r⁻¹) r := by
  exact (hasDerivAt_kMoment 0 hr).add (Real.hasDerivAt_log hr.ne')

theorem besselLogRemainder_deriv_bounds {r : ℝ} (hr : 0 < r) :
    0 ≤ deriv besselLogRemainder r ∧ deriv besselLogRemainder r ≤ 1 := by
  rw [(hasDerivAt_besselLogRemainder hr).deriv]
  obtain ⟨hl, hu⟩ := kMoment_one_mul_bounds hr
  have hinv : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  constructor
  · nlinarith
  · nlinarith [Real.add_one_le_exp (-r)]

theorem besselLogRemainder_monotone : MonotoneOn besselLogRemainder (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · exact fun r hr => (hasDerivAt_besselLogRemainder hr).continuousAt.continuousWithinAt
  · intro r hr
    exact (hasDerivAt_besselLogRemainder (interior_subset hr)).differentiableAt.differentiableWithinAt
  · intro r hr
    exact (besselLogRemainder_deriv_bounds (interior_subset hr)).1

/-- A uniform Lipschitz bound survives all positive boundary scales. -/
theorem besselLogRemainder_lipschitz {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    |besselLogRemainder t - besselLogRemainder r| ≤ |t - r| := by
  have hb : ∀ x ∈ Ioi (0 : ℝ), ‖deriv besselLogRemainder x‖ ≤ 1 := by
    intro x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (besselLogRemainder_deriv_bounds hx).1]
    exact (besselLogRemainder_deriv_bounds hx).2
  simpa only [Real.norm_eq_abs, one_mul] using
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x hx => (hasDerivAt_besselLogRemainder hx).differentiableAt) hb
      (convex_Ioi 0) hr ht

/-- Bounded logarithmic remainder at zero, with an explicit constant. -/
theorem abs_besselLogRemainder_le {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    |besselLogRemainder r| ≤ kMoment 0 1 + 1 := by
  have h := besselLogRemainder_lipschitz (by norm_num : (0 : ℝ) < 1) hr
  have he : besselLogRemainder 1 = kMoment 0 1 := by simp [besselLogRemainder]
  rw [he, abs_of_nonpos (by linarith : r - 1 ≤ 0)] at h
  apply abs_le.mpr
  constructor <;> nlinarith [(abs_le.mp h).1, (abs_le.mp h).2, kMoment_nonneg 0 1]

/-- Monotonicity of the undifferentiated kernel on its full positive domain. -/
theorem kMoment_zero_antitone {r t : ℝ} (hr : 0 < r) (hrt : r ≤ t) :
    kMoment 0 t ≤ kMoment 0 r := by
  refine (kMoment_le_exp_mul 0 hr hrt).trans ?_
  have he : Real.exp (-(t - r)) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (show -(t - r) ≤ 0 by linarith)
  simpa using mul_le_mul_of_nonneg_right he (kMoment_nonneg 0 r)

/-- The logarithmic bound used to dominate all Fourier frequencies at once. -/
theorem kMoment_zero_le_log {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    kMoment 0 r ≤ kMoment 0 1 - Real.log r := by
  have h := besselLogRemainder_monotone hr (by norm_num : (0 : ℝ) < 1) hr1
  simp only [besselLogRemainder, Real.log_one, add_zero] at h
  linarith

/-- A single majorant controls arbitrarily large frequencies `r ≥ c*y`. -/
theorem kMoment_zero_div_log_bound {c y r : ℝ} (hc : 0 < c) (hy : 0 < y)
    (hcy : c * y ≤ 1) (hlog : Real.log y ≤ -1) (hr : c * y ≤ r) :
    |kMoment 0 r / Real.log y| ≤ kMoment 0 1 + |Real.log c| + 1 := by
  have hlow := mul_pos hc hy
  have hk := (kMoment_zero_antitone hlow hr).trans (kMoment_zero_le_log hlow hcy)
  rw [Real.log_mul hc.ne' hy.ne'] at hk
  rw [abs_div, abs_of_nonneg (kMoment_nonneg 0 r), abs_of_nonpos (by linarith : Real.log y ≤ 0)]
  apply (div_le_iff₀ (by linarith : 0 < -Real.log y)).mpr
  have hbase : 0 ≤ kMoment 0 1 + |Real.log c| :=
    add_nonneg (kMoment_nonneg 0 1) (abs_nonneg _)
  have hmul : kMoment 0 1 + |Real.log c| ≤
      (kMoment 0 1 + |Real.log c|) * (-Real.log y) := by nlinarith
  nlinarith [neg_le_abs (Real.log c)]

private lemma tendsto_besselLogRemainder_div_log {c : ℝ} (hc : 0 < c) :
    Tendsto (fun y : ℝ => besselLogRemainder (c * y) / Real.log y)
      (𝓝[>] 0) (𝓝 0) := by
  have hi := tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero
  have hy0 : Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hcy : Tendsto (fun y : ℝ => c * y) (𝓝[>] 0) (𝓝 0) := by
    simpa only [id, mul_zero] using hy0.const_mul c
  have hb : Tendsto (fun y : ℝ => (kMoment 0 1 + 1) * ‖(Real.log y)⁻¹‖)
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_apply, norm_zero, mul_zero] using hi.norm.const_mul (kMoment 0 1 + 1)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Filter.Eventually.of_forall fun y => norm_nonneg _) ?_ hb
  filter_upwards [self_mem_nhdsWithin,
    hcy.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with y hy hy1
  have h := abs_besselLogRemainder_le (mul_pos hc hy) hy1.le
  simpa only [div_eq_mul_inv, norm_mul, Real.norm_eq_abs] using
    mul_le_mul_of_nonneg_right h (norm_nonneg ((Real.log y)⁻¹))

/-- The actual kernel has the logarithmic trace at every fixed positive scale. -/
theorem tendsto_kMoment_zero_mul_div_log {c : ℝ} (hc : 0 < c) :
    Tendsto (fun y : ℝ => kMoment 0 (c * y) / Real.log y) (𝓝[>] 0) (𝓝 (-1)) := by
  have hi := tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero
  have hd : Tendsto (fun y : ℝ => Real.log c / Real.log y) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Function.comp_apply, div_eq_mul_inv, mul_zero] using hi.const_mul (Real.log c)
  have h : Tendsto (fun y : ℝ => besselLogRemainder (c * y) / Real.log y -
      Real.log c / Real.log y - 1) (𝓝[>] 0) (𝓝 (-1)) := by
    simpa using ((tendsto_besselLogRemainder_div_log hc).sub hd).sub_const 1
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ y : ℝ in 𝓝[>] 0, y < 1 from
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))] with y hy hy1
  have hl : Real.log y ≠ 0 := (Real.log_neg hy hy1).ne
  simp only [besselLogRemainder, Real.log_mul hc.ne' hy.ne']
  field_simp [hl]
  ring

/-- A global bound for the weighted zeroth moment, including large arguments. -/
theorem sq_mul_kMoment_zero_le {r : ℝ} (hr : 0 < r) :
    r ^ 2 * kMoment 0 r ≤ 1 + 2 * Real.exp 1 * kMoment 0 1 := by
  by_cases hr1 : r ≤ 1
  · have hk : kMoment 0 r ≤ kMoment 1 r := by
      rw [kMoment_eq, kMoment_eq]
      refine setIntegral_mono_on (integrableOn_kIntegrand 0 hr)
        (integrableOn_kIntegrand 1 hr) measurableSet_Ioi fun t _ => ?_
      simp only [kIntegrand, pow_zero, pow_one, one_mul]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (Real.one_le_cosh t) (Real.exp_nonneg (-(r * Real.cosh t)))
    have hsq : r ^ 2 ≤ r := by nlinarith
    have h₁ := mul_le_mul_of_nonneg_right hsq (kMoment_nonneg 0 r)
    have h₂ := mul_le_mul_of_nonneg_left hk hr.le
    have h₃ := (kMoment_one_mul_bounds hr).2
    have hpos : 0 ≤ 2 * Real.exp 1 * kMoment 0 1 :=
      mul_nonneg (by positivity) (kMoment_nonneg 0 1)
    linarith
  · have hk := kMoment_le_exp_mul 0 (by norm_num : (0 : ℝ) < 1) (le_of_not_ge hr1)
    have hp : r ^ 2 ≤ 2 * Real.exp r := by
      have h := Real.pow_div_factorial_le_exp r hr.le 2
      norm_num at h
      linarith
    have he : r ^ 2 * Real.exp (-(r - 1)) ≤ 2 * Real.exp 1 := by
      rw [show -(r - 1) = 1 - r by ring, Real.exp_sub, ← mul_div_assoc]
      apply (div_le_iff₀ (Real.exp_pos r)).mpr
      nlinarith [Real.exp_pos 1]
    calc
      r ^ 2 * kMoment 0 r ≤ r ^ 2 * (Real.exp (-(r - 1)) * kMoment 0 1) :=
        mul_le_mul_of_nonneg_left hk (sq_nonneg r)
      _ = (r ^ 2 * Real.exp (-(r - 1))) * kMoment 0 1 := by ring
      _ ≤ (2 * Real.exp 1) * kMoment 0 1 :=
        mul_le_mul_of_nonneg_right he (kMoment_nonneg 0 1)
      _ ≤ 1 + 2 * Real.exp 1 * kMoment 0 1 := by linarith

/-- The second weighted derivative is uniformly controlled for moving boundary tests. -/
theorem sq_mul_kMoment_two_le {r : ℝ} (hr : 0 < r) :
    r ^ 2 * kMoment 2 r ≤ 2 + 2 * Real.exp 1 * kMoment 0 1 := by
  have he : r ^ 2 * kMoment 2 r = r ^ 2 * kMoment 0 r + r * kMoment 1 r := by
    linear_combination r * kMoment_ode hr
  rw [he]
  linarith [sq_mul_kMoment_zero_le hr, (kMoment_one_mul_bounds hr).2]

end RHTower.WeilHigherDenominator
