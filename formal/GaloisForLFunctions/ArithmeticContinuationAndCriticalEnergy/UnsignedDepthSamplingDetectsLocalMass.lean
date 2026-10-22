import GaloisForLFunctions.SquareRootThreshold.TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarBumpSources
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Unsigned conjugate-difference sampling detects local depth mass

A source-uniform bound at one positive aperture already controls squared depths
on every unit-height window. The probes are literal complex smooth interior
sources. This concerns unsigned difference energy, not the signed Weil floor.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower RHTower.CCMParityQuartet
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
noncomputable section
set_option autoImplicit false

/-- The unscaled difference energy is four times the negative paired energy. -/
def UnsignedDepthSamplingBound (a : SuzukiPositiveAperture) (B : ℝ) : Prop :=
  ∀ u : CCMComplexSmoothInteriorSource a, ∀ s : Finset XiZeroCopy,
    (∑ q ∈ s, ‖testTransform u (-xiSpectralPoint q) -
      testTransform u (-(starRingEnd ℂ) (xiSpectralPoint q))‖ ^ 2) ≤
        B * ∫ x, ‖u x‖ ^ 2

private def udsScale (a : SuzukiPositiveAperture) : ℝ := min (a.1 / 4) (1 / 8)

private theorem udsScale_pos (a : SuzukiPositiveAperture) : 0 < udsScale a :=
  lt_min (by dsimp; linarith [a.2]) (by norm_num)

private theorem udsScale_support (a : SuzukiPositiveAperture) :
    Metric.closedBall (2 * udsScale a) (udsScale a) ⊆ Ioo (-a.1) a.1 := by
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  have hb := udsScale_pos a
  have hbA : udsScale a ≤ a.1 / 4 := min_le_left _ _
  constructor <;> linarith [a.2]

private def udsBump (a : SuzukiPositiveAperture) : ContDiffBump (2 * udsScale a) :=
  polarBumpFn (2 * udsScale a) (udsScale a) (udsScale_pos a)

private theorem udsBump_support {a : SuzukiPositiveAperture} {x : ℝ}
    (hx : udsBump a x ≠ 0) : udsScale a ≤ x ∧ x ≤ 3 * udsScale a := by
  have h : x ∈ Metric.ball (2 * udsScale a) (udsBump a).rOut := by
    rw [← (udsBump a).support_eq]
    exact hx
  change x ∈ Metric.ball (2 * udsScale a) (udsScale a) at h
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at h
  constructor <;> linarith

private def udsModulate {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (T : ℝ) : CCMComplexSmoothInteriorSource a where
  toFun x := u x * Complex.exp (Complex.I * T * x)
  smooth := u.smooth.mul (Complex.contDiff_exp.comp
    ((contDiff_const.mul contDiff_const).mul Complex.ofRealCLM.contDiff))
  hasCompactSupport := u.hasCompactSupport.mul_right
  tsupport_subset := (tsupport_mul_subset_left (f := (u : ℝ → ℂ))
    (g := fun x : ℝ => Complex.exp (Complex.I * T * x))).trans u.tsupport_subset

private def udsProbe (a : SuzukiPositiveAperture) (T : ℝ) : CCMComplexSmoothInteriorSource a :=
  udsModulate (bumpInteriorSource a (2 * udsScale a) (udsScale a)
    (udsScale_pos a) (udsScale_support a)) T

private theorem udsProbe_apply (a : SuzukiPositiveAperture) (T x : ℝ) :
    udsProbe a T x = (udsBump a x : ℂ) * Complex.exp (Complex.I * T * x) := rfl

private theorem udsProbe_norm (a : SuzukiPositiveAperture) (T x : ℝ) :
    ‖udsProbe a T x‖ = udsBump a x := by
  rw [udsProbe_apply, norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, mul_one, Real.exp_zero,
    Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (udsBump a).nonneg

private theorem udsProbe_integrand_re (a : SuzukiPositiveAperture) (T x : ℝ) (z : ℂ) :
    (udsProbe a T x * Complex.exp (Complex.I * (-z) * x)).re =
      udsBump a x * Real.exp (z.im * x) * Real.cos ((T - z.re) * x) := by
  rw [udsProbe_apply, mul_assoc, ← Complex.exp_add]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_re, Complex.add_re, Complex.add_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
  congr 1 <;> ring

private theorem udsProbe_difference_re (a : SuzukiPositiveAperture) (T : ℝ) (z : ℂ) :
    (testTransform (udsProbe a T) (-z) -
      testTransform (udsProbe a T) (-(starRingEnd ℂ) z)).re =
        ∫ x, udsBump a x * (Real.exp (z.im * x) - Real.exp (-z.im * x)) *
          Real.cos ((T - z.re) * x) := by
  have h1 := integrable_testTransform_integrand (udsProbe a T).continuous
    (udsProbe a T).hasCompactSupport (-z)
  have h2 := integrable_testTransform_integrand (udsProbe a T).continuous
    (udsProbe a T).hasCompactSupport (-(starRingEnd ℂ) z)
  unfold testTransform
  rw [← integral_sub h1 h2, ← integral_re (h1.sub h2)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Complex.sub_re, udsProbe_integrand_re, udsProbe_integrand_re]
  simp only [Complex.conj_re, Complex.conj_im]
  ring

private theorem udsProbe_lower_nonneg (a : SuzukiPositiveAperture) (T : ℝ) (z : ℂ)
    (hT : |z.re - T| ≤ 1) (hy : 0 ≤ z.im) :
    (udsScale a * ∫ x, udsBump a x) * z.im ≤
      ‖testTransform (udsProbe a T) (-z) -
        testTransform (udsProbe a T) (-(starRingEnd ℂ) z)‖ := by
  have hp := (udsBump a).continuous
  have hpI := hp.integrable_of_hasCompactSupport (udsBump a).hasCompactSupport
  have hF : Integrable (fun x : ℝ => udsBump a x *
      (Real.exp (z.im * x) - Real.exp (-z.im * x)) * Real.cos ((T - z.re) * x)) :=
    ((hp.mul ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).sub
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)))).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
        ((udsBump a).hasCompactSupport.mul_right.mul_right)
  have hpoint : ∀ x : ℝ, udsBump a x * (udsScale a * z.im) ≤
      udsBump a x * (Real.exp (z.im * x) - Real.exp (-z.im * x)) *
        Real.cos ((T - z.re) * x) := by
    intro x
    by_cases h0 : udsBump a x = 0
    · simp [h0]
    have hx := udsBump_support h0
    have hx0 : 0 ≤ x := (udsScale_pos a).le.trans hx.1
    have hb : udsScale a ≤ 1 / 8 := min_le_right _ _
    have harg : |(T - z.re) * x| ≤ 1 := by
      calc
        |(T - z.re) * x| = |z.re - T| * x := by
          rw [abs_mul, abs_sub_comm T z.re, abs_of_nonneg hx0]
        _ ≤ 1 * (3 * udsScale a) := mul_le_mul hT hx.2 hx0 (by norm_num)
        _ ≤ 1 := by linarith
    have harg2 : ((T - z.re) * x) ^ 2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) harg 2
    have hcos : 1 / 2 ≤ Real.cos ((T - z.re) * x) := by
      linarith [Real.one_sub_sq_div_two_le_cos ((T - z.re) * x)]
    have hsinh := Real.self_le_sinh_iff.mpr (mul_nonneg hy hx0)
    rw [Real.sinh_eq, ← neg_mul] at hsinh
    have hexp : 2 * (udsScale a * z.im) ≤
        Real.exp (z.im * x) - Real.exp (-z.im * x) := by
      nlinarith [mul_le_mul_of_nonneg_left hx.1 hy]
    have hexp0 : 0 ≤ Real.exp (z.im * x) - Real.exp (-z.im * x) := by
      nlinarith [mul_nonneg (udsScale_pos a).le hy]
    have hprod : udsScale a * z.im ≤
        (Real.exp (z.im * x) - Real.exp (-z.im * x)) * Real.cos ((T - z.re) * x) := by
      nlinarith [mul_le_mul_of_nonneg_left hcos hexp0]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hprod (udsBump a).nonneg
  have hInt := integral_mono (hpI.mul_const (udsScale a * z.im)) hF hpoint
  rw [integral_mul_const] at hInt
  calc
    (udsScale a * ∫ x, udsBump a x) * z.im =
        (∫ x, udsBump a x) * (udsScale a * z.im) := by ring
    _ ≤ _ := hInt
    _ = (testTransform (udsProbe a T) (-z) -
        testTransform (udsProbe a T) (-(starRingEnd ℂ) z)).re :=
      (udsProbe_difference_re a T z).symm
    _ ≤ _ := Complex.re_le_norm _

private theorem udsProbe_lower (a : SuzukiPositiveAperture) (T : ℝ) (z : ℂ)
    (hT : |z.re - T| ≤ 1) :
    (udsScale a * ∫ x, udsBump a x) * |z.im| ≤
      ‖testTransform (udsProbe a T) (-z) -
        testTransform (udsProbe a T) (-(starRingEnd ℂ) z)‖ := by
  by_cases hy : 0 ≤ z.im
  · simpa only [abs_of_nonneg hy] using udsProbe_lower_nonneg a T z hT hy
  · have hy' : 0 ≤ ((starRingEnd ℂ) z).im := by simp only [Complex.conj_im]; linarith
    have h := udsProbe_lower_nonneg a T ((starRingEnd ℂ) z)
      (by simpa only [Complex.conj_re] using hT) hy'
    simpa only [Complex.conj_im, map_neg, starRingEnd_self_apply,
      abs_of_nonpos (le_of_not_ge hy), norm_sub_rev] using h

/-- Literal smooth probes detect depths uniformly across height windows. No strip bound is needed. -/
theorem exists_uniform_depth_detecting_smooth_sources (a : SuzukiPositiveAperture) :
    ∃ c N : ℝ, 0 < c ∧ 0 ≤ N ∧ ∀ T : ℝ,
      ∃ u : CCMComplexSmoothInteriorSource a, (∫ x, ‖u x‖ ^ 2) = N ∧
        ∀ z : ℂ, |z.re - T| ≤ 1 →
          c * |z.im| ≤ ‖testTransform u (-z) - testTransform u (-(starRingEnd ℂ) z)‖ := by
  refine ⟨udsScale a * ∫ x, udsBump a x, ∫ x, (udsBump a x) ^ 2,
    mul_pos (udsScale_pos a) (udsBump a).integral_pos,
    integral_nonneg (fun x => sq_nonneg _), ?_⟩
  intro T
  refine ⟨udsProbe a T, ?_, fun z hz => udsProbe_lower a T z hz⟩
  simp_rw [udsProbe_norm]

/-- A bound for unsigned sampling at one aperture forces a height-independent local depth bound. -/
theorem exists_offLineDepthLocallyBounded_of_unsignedDepthSamplingBound
    {a : SuzukiPositiveAperture} {B : ℝ} (hB : UnsignedDepthSamplingBound a B) :
    ∃ W : ℝ, OffLineDepthLocallyBounded W := by
  obtain ⟨c, N, hc, _hN, hprobe⟩ := exists_uniform_depth_detecting_smooth_sources a
  refine ⟨B * N / c ^ 2, ?_⟩
  intro T s hs
  obtain ⟨u, hu, hdet⟩ := hprobe T
  have hlo : c ^ 2 * (∑ q ∈ s, (xiSpectralPoint q).im ^ 2) ≤
      ∑ q ∈ s, ‖testTransform u (-xiSpectralPoint q) -
        testTransform u (-(starRingEnd ℂ) (xiSpectralPoint q))‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have h := pow_le_pow_left₀ (mul_nonneg hc.le (abs_nonneg _))
      (hdet (xiSpectralPoint q) (hs q hq)) 2
    simpa only [mul_pow, sq_abs] using h
  have hbound := hlo.trans (hB u s)
  rw [hu] at hbound
  exact (le_div_iff₀ (sq_pos_of_pos hc)).mpr (by simpa only [mul_comm] using hbound)

/-- Existing depth-weighted sampling gives the matching upper bound, with exact factor four. -/
theorem unsignedDepthSamplingBound_of_offLineDepthLocallyBounded
    {W : ℝ} (hW : OffLineDepthLocallyBounded W) (a : SuzukiPositiveAperture) :
    UnsignedDepthSamplingBound a (4 * depthFloorConst W a.1) := by
  intro u s
  have hWs : ∀ T : ℝ, ∀ t : Finset XiZeroCopy, t ⊆ s →
      (∀ q ∈ t, |-(xiSpectralPoint q).re - T| ≤ 1) →
      ∑ q ∈ t, (-(xiSpectralPoint q).im) ^ 2 ≤ W := by
    intro T t _ ht
    simp_rw [neg_sq]
    apply hW (-T) t
    intro q hq
    have h := ht q hq
    rwa [show -(xiSpectralPoint q).re - T = -((xiSpectralPoint q).re - -T) by ring,
      abs_neg] at h
  have hdepth : ∀ q : XiZeroCopy, |-(xiSpectralPoint q).im| ≤ zetaZeroWidth := fun q => by
    rw [abs_neg]
    exact abs_im_xiSpectralPoint_le_zetaZeroWidth q
  have e1 : ∀ q : XiZeroCopy, -xiSpectralPoint q =
      ((-(xiSpectralPoint q).re : ℝ) : ℂ) + ((-(xiSpectralPoint q).im : ℝ) : ℂ) * I :=
    fun q => by apply Complex.ext <;> simp
  have e2 : ∀ q : XiZeroCopy, -(starRingEnd ℂ) (xiSpectralPoint q) =
      ((-(xiSpectralPoint q).re : ℝ) : ℂ) - ((-(xiSpectralPoint q).im : ℝ) : ℂ) * I :=
    fun q => by apply Complex.ext <;> simp
  have h := sum_norm_sq_testTransform_sub_conj_le_of_depthWeighted' a.2
    (smoothSource_intervalSource u)
    (fun q => -(xiSpectralPoint q).re) (fun q => -(xiSpectralPoint q).im)
    zetaZeroWidth_nonneg hdepth s hWs
  simp_rw [e1, e2]
  exact h.trans (le_of_eq (by unfold depthFloorConst; ring))

/-- At any fixed positive aperture, unsigned sampling is bounded exactly when local depth mass is. -/
theorem exists_unsignedDepthSamplingBound_iff (a : SuzukiPositiveAperture) :
    (∃ B : ℝ, 0 ≤ B ∧ UnsignedDepthSamplingBound a B) ↔
      ∃ W : ℝ, OffLineDepthLocallyBounded W := by
  constructor
  · rintro ⟨B, _, hB⟩
    exact exists_offLineDepthLocallyBounded_of_unsignedDepthSamplingBound hB
  · rintro ⟨W, hW⟩
    refine ⟨4 * depthFloorConst W a.1, ?_,
      unsignedDepthSamplingBound_of_offLineDepthLocallyBounded hW a⟩
    have hW0 := hW.nonneg
    have ha := a.2
    unfold depthFloorConst
    positivity

end
end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
