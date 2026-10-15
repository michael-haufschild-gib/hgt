import GaloisForLFunctions.RHTower.LogSineQuantileNonrealZeros
import GaloisForLFunctions.RHTower.LogSineQuantileEndpoint
import GaloisForLFunctions.RHTower.HedenmalmPinnedVolterraBoundaryDefect

/-!
# Nonreal modes of the literal singular quantile inverse

At a zero z of the logarithmic sine quantile transform, the explicit primitive
  g(t) = -exp(-i*z*Q(t)) integral_0^t exp(i*z*Q(s)) ds
has derivative f-1, where f=-i*z*q*g. The actual endpoint coefficient t*q(t)
tends to zero. A half-power phase bound proves g=O(t), hence f tends to zero at0;
reflection and the transform zero handle1. Both functions are continuous on[0,1].
The fundamental theorem gives mean(f)=1 and C f=g for the literal pinned primitive.

The resulting nonzero vector in complex L2(0,1) satisfies i*q*C f=(-1/z)*f.
The final theorem supplies such a nonreal mode for every sufficiently small positive
regularization, together with strict concavity, positive conductances and all finite
shifted Hankel inequalities of the same profile. Every endpoint/domain condition of
this L2 equation is proved. Global boundedness/compactness of i*M_q*C and theta-specific
spectral rigidity are separate claims, not asserted here.
-/

open MeasureTheory Set Filter Topology
namespace RHTower
noncomputable section

/-- Literal Fourier phase in the original quantile coordinate. -/
def logSineQuantilePhase (δ : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * z * (logSineQuantileClock δ t : ℂ))

private theorem integrable_clock_phase {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    Integrable (fun u : ℝ => Complex.exp (Complex.I * z * (logSineClock δ u : ℂ)) /
      (Real.cosh u : ℂ)) := by
  apply (integrable_logSineClock_exponential hδ (norm_nonneg z)).mono'
  · have hc : Continuous (fun u : ℝ => Complex.exp (Complex.I * z * (logSineClock δ u : ℂ)) /
        (Real.cosh u : ℂ)) := by
      exact (Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_logSineClock hδ.le)))).div
        (Complex.continuous_ofReal.comp Real.continuous_cosh)
        (fun u => Complex.ofReal_ne_zero.mpr (Real.cosh_pos u).ne')
    exact hc.aestronglyMeasurable
  · filter_upwards with u
    rw [norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.cosh_pos u)]
    apply div_le_div_of_nonneg_right _ (Real.cosh_pos u).le
    apply Real.exp_le_exp.mpr
    have he : (Complex.I * z * (logSineClock δ u : ℂ)).re =
        -(z.im * logSineClock δ u) := by simp [Complex.mul_re, Complex.mul_im]
    rw [he]
    calc
      _ ≤ |z.im * logSineClock δ u| := neg_le_abs _
      _ = |z.im| * |logSineClock δ u| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (abs_nonneg _)

theorem integrableOn_logSineQuantilePhase {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    IntegrableOn (logSineQuantilePhase δ z) (Ioo (0 : ℝ) 1) := by
  have hs := integrableOn_image_iff_integrableOn_abs_deriv_smul (f := logSineBaseCoordinate)
    (f' := fun u => 1 / (Real.pi * Real.cosh u)) MeasurableSet.univ
    (fun u _ => (hasDerivAt_logSineBaseCoordinate u).hasDerivWithinAt)
    logSineBaseCoordinate_injective.injOn (logSineQuantilePhase δ z)
  rw [logSineBaseCoordinate_image_univ, integrableOn_univ] at hs
  apply hs.mpr
  have hi := (integrable_clock_phase hδ (z / Real.pi)).const_mul (Real.pi : ℂ)⁻¹
  apply hi.congr
  filter_upwards with u
  unfold logSineQuantilePhase
  rw [abs_of_pos (by positivity), logSineQuantileClock_baseCoordinate hδ.le,
    Complex.real_smul]
  push_cast
  have hexp : Complex.I * z * ((logSineClock δ u : ℂ) / Real.pi) =
      Complex.I * (z / Real.pi) * (logSineClock δ u : ℂ) := by ring
  rw [hexp]
  ring

theorem intervalIntegrable_logSineQuantilePhase {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    IntervalIntegrable (logSineQuantilePhase δ z) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
    (integrableOn_logSineQuantilePhase hδ z)

theorem continuousAt_logSineQuantilePhase {δ t : ℝ} (hδ : 0 ≤ δ) (z : ℂ)
    (ht : t ∈ Ioo (0 : ℝ) 1) : ContinuousAt (logSineQuantilePhase δ z) t := by
  exact Complex.continuous_exp.continuousAt.comp
    (continuousAt_const.mul ((hasDerivAt_logSineQuantileClock hδ ht).continuousAt.ofReal))

/-- The primitive whose derivative is the normalized pinned-inverse mode minus one. -/
def logSineModePrimitive (δ : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  -Complex.exp (-(Complex.I * z * (logSineQuantileClock δ t : ℂ))) *
    ∫ s in (0 : ℝ)..t, logSineQuantilePhase δ z s

private theorem half_ratio_eq (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    (t / s) ^ (1 / 2 : ℝ) = t ^ (1 / 2 : ℝ) * s ^ (-(1 / 2) : ℝ) := by
  rw [Real.div_rpow ht hs, Real.rpow_neg hs, div_eq_mul_inv]

private theorem intervalIntegrable_half_ratio {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s : ℝ => (t / s) ^ (1 / 2 : ℝ)) volume 0 t := by
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := t)
    (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul (t ^ (1 / 2 : ℝ))
  apply hi.congr
  intro s hs
  rw [uIoc_of_le ht] at hs
  exact (half_ratio_eq t s ht hs.1.le).symm

private theorem integral_half_ratio {t : ℝ} (ht : 0 < t) :
    (∫ s in (0 : ℝ)..t, (t / s) ^ (1 / 2 : ℝ)) = 2 * t := by
  have he : (∫ s in (0 : ℝ)..t, (t / s) ^ (1 / 2 : ℝ)) =
      t ^ (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..t, s ^ (-(1 / 2) : ℝ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.le] at hs
    exact half_ratio_eq t s ht.le hs.1
  rw [he, integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2)))]
  norm_num only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), sub_zero]
  have hp : t ^ (1 / 2 : ℝ) * t ^ (1 / 2 : ℝ) = t := by
    rw [← Real.rpow_add ht, show (1 / 2 : ℝ) + 1 / 2 = 1 by ring, Real.rpow_one]
  nlinarith

private theorem logSineModePrimitive_eq_phase_difference (δ : ℝ) (z : ℂ) (t : ℝ) :
    logSineModePrimitive δ z t =
      -(∫ s in (0 : ℝ)..t, Complex.exp
        (Complex.I * z * ((logSineQuantileClock δ s - logSineQuantileClock δ t : ℝ) : ℂ))) := by
  unfold logSineModePrimitive
  rw [neg_mul, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only [logSineQuantilePhase]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The singular endpoint estimate for the literal mode, with no transform-zero assumption. -/
theorem exists_logSineModePrimitive_endpoint_bound {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    ∃ a : ℝ, 0 < a ∧ a < 1 / 2 ∧ ∀ t : ℝ, 0 < t → t ≤ a →
      ‖logSineModePrimitive δ z t‖ ≤ 2 * t := by
  let ε : ℝ := 1 / (2 * (1 + |z.im|))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεb : |z.im| * ε ≤ 1 / 2 := by
    dsimp [ε]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  obtain ⟨a, ha, ha1, hq⟩ := exists_logSineQuantileSpeed_endpoint_small hδ hε
  refine ⟨a, ha, ha1, fun t ht hta => ?_⟩
  rw [logSineModePrimitive_eq_phase_difference, norm_neg]
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, (t / s) ^ (1 / 2 : ℝ) := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht.le _ (intervalIntegrable_half_ratio ht.le)
      filter_upwards with s hs
      apply logSineQuantile_phase_difference_bound hδ.le hs.1 hs.2
        (by linarith) z hεb
      intro v hv
      exact hq v (hs.1.trans_le hv.1) (hv.2.trans hta)
    _ = _ := integral_half_ratio ht

/-- The normalized right mode of the literal pinned inverse. -/
def logSineQuantileMode (δ : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  -(Complex.I * z) * (logSineQuantileSpeed δ t : ℂ) * logSineModePrimitive δ z t

private theorem intervalIntegrable_quantilePhase_prefix {δ t : ℝ} (hδ : 0 < δ)
    (z : ℂ) (ht : t ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (logSineQuantilePhase δ z) volume 0 t := by
  apply (intervalIntegrable_logSineQuantilePhase hδ z).mono_set
  rw [uIcc_of_le zero_le_one, uIcc_of_le ht.1]
  exact Icc_subset_Icc le_rfl ht.2

private theorem hasDerivAt_quantilePhase_prefix {δ t : ℝ} (hδ : 0 < δ)
    (z : ℂ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, logSineQuantilePhase δ z s)
      (logSineQuantilePhase δ z t) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_quantilePhase_prefix hδ z ⟨ht.1.le, ht.2.le⟩)
    (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
      (fun _ hs => continuousAt_logSineQuantilePhase hδ.le z hs) t ht)
    (continuousAt_logSineQuantilePhase hδ.le z ht)

theorem hasDerivAt_logSineModePrimitive {δ t : ℝ} (hδ : 0 < δ) (z : ℂ)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (logSineModePrimitive δ z) (logSineQuantileMode δ z t - 1) t := by
  have hq := hasDerivAt_logSineQuantileClock hδ.le ht
  have hE := ((hq.ofReal_comp.const_mul (Complex.I * z)).neg).cexp
  have hJ := hasDerivAt_quantilePhase_prefix hδ z ht
  have hid : Complex.exp (-(Complex.I * z * (logSineQuantileClock δ t : ℂ))) *
      logSineQuantilePhase δ z t = 1 := by
    unfold logSineQuantilePhase
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  convert! hE.neg.mul hJ using 1
  unfold logSineQuantileMode logSineModePrimitive
  dsimp only [Pi.neg_apply]
  linear_combination hid

theorem logSineModePrimitive_zero (δ : ℝ) (z : ℂ) : logSineModePrimitive δ z 0 = 0 := by
  simp [logSineModePrimitive]

theorem logSineQuantileMode_zero (δ : ℝ) (z : ℂ) : logSineQuantileMode δ z 0 = 0 := by
  rw [logSineQuantileMode, logSineModePrimitive_zero, mul_zero]

theorem tendsto_logSineModePrimitive_zero {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    Tendsto (logSineModePrimitive δ z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨a, ha, _, hb⟩ := exists_logSineModePrimitive_endpoint_bound hδ z
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖logSineModePrimitive δ z t‖ ≤ 2 * t := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with t ht hta
    exact hb t ht hta.le
  apply squeeze_zero_norm' hbound
  simpa only [Pi.mul_apply, id_eq, mul_zero] using!
    (((continuous_const.mul continuous_id).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds :
      Tendsto (fun t : ℝ => 2 * t) (𝓝[>] 0) (𝓝 (2 * 0)))

theorem tendsto_logSineQuantileMode_zero {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    Tendsto (logSineQuantileMode δ z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨a, ha, ha1, hb⟩ := exists_logSineModePrimitive_endpoint_bound hδ z
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ‖logSineQuantileMode δ z t‖ ≤ (2 * ‖z‖) * (t * logSineQuantileSpeed δ t) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with t ht hta
    have hq := logSineQuantileSpeed_pos hδ.le ⟨ht, by linarith⟩
    rw [logSineQuantileMode, norm_mul, norm_mul, norm_neg, norm_mul, Complex.norm_I,
      one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
    calc
      _ ≤ (‖z‖ * logSineQuantileSpeed δ t) * (2 * t) :=
        mul_le_mul_of_nonneg_left (hb t ht hta.le) (by positivity)
      _ = _ := by ring
  apply squeeze_zero_norm' hbound
  simpa only [mul_zero] using (tendsto_logSineQuantileSpeed_endpoint hδ).const_mul (2 * ‖z‖)

theorem logSineQuantilePhase_one_sub (δ : ℝ) (z : ℂ) (t : ℝ) :
    logSineQuantilePhase δ z (1 - t) = logSineQuantilePhase δ (-z) t := by
  unfold logSineQuantilePhase
  rw [logSineQuantileClock_one_sub]
  congr 1
  push_cast
  ring

theorem integral_logSineQuantilePhase (δ : ℝ) (z : ℂ) :
    (∫ t in (0 : ℝ)..1, logSineQuantilePhase δ z t) = logSineQuantileTransform δ z := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rfl

theorem logSineModePrimitive_one_sub {δ : ℝ} (hδ : 0 < δ) (z : ℂ)
    (hz : logSineQuantileTransform δ z = 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    logSineModePrimitive δ z (1 - t) = -logSineModePrimitive δ (-z) t := by
  have hu : 1 - t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
  have hi := intervalIntegrable_logSineQuantilePhase hδ z
  have hiu : IntervalIntegrable (logSineQuantilePhase δ z) volume (1 - t) 1 := by
    apply hi.mono_set
    rw [uIcc_of_le zero_le_one, uIcc_of_le hu.2]
    exact Icc_subset_Icc hu.1 le_rfl
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_quantilePhase_prefix hδ z hu) hiu
  rw [integral_logSineQuantilePhase, hz] at hsum
  have hs := intervalIntegral.integral_comp_sub_left (logSineQuantilePhase δ z)
    (a := 0) (b := t) 1
  simp_rw [logSineQuantilePhase_one_sub] at hs
  simp only [sub_zero] at hs
  rw [← hs] at hsum
  have hJ := eq_neg_of_add_eq_zero_left hsum
  have hE : Complex.exp (-(Complex.I * z * (logSineQuantileClock δ (1 - t) : ℂ))) =
      Complex.exp (-(Complex.I * (-z) * (logSineQuantileClock δ t : ℂ))) := by
    rw [logSineQuantileClock_one_sub]
    congr 1
    push_cast
    ring
  unfold logSineModePrimitive
  rw [hE, hJ]
  ring

theorem logSineQuantileMode_one_sub {δ : ℝ} (hδ : 0 < δ) (z : ℂ)
    (hz : logSineQuantileTransform δ z = 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    logSineQuantileMode δ z (1 - t) = logSineQuantileMode δ (-z) t := by
  unfold logSineQuantileMode
  rw [logSineQuantileSpeed_one_sub, logSineModePrimitive_one_sub hδ z hz ht]
  ring

private theorem continuousWithinAt_modePrimitive_left {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    ContinuousWithinAt (logSineModePrimitive δ z) (Ici 0) 0 := by
  rw [← Ioi_insert]
  apply ContinuousWithinAt.insert
  simpa only [ContinuousWithinAt, logSineModePrimitive_zero] using tendsto_logSineModePrimitive_zero hδ z

private theorem continuousWithinAt_quantileMode_left {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    ContinuousWithinAt (logSineQuantileMode δ z) (Ici 0) 0 := by
  rw [← Ioi_insert]
  apply ContinuousWithinAt.insert
  simpa only [ContinuousWithinAt, logSineQuantileMode_zero] using tendsto_logSineQuantileMode_zero hδ z

private theorem continuousWithinAt_right_of_reflection {f g : ℝ → ℂ}
    (hg : ContinuousWithinAt g (Ici 0) 0)
    (hr : ∀ t ∈ Icc (0 : ℝ) 1, f t = g (1 - t)) :
    ContinuousWithinAt f (Icc (0 : ℝ) 1) 1 := by
  have hm : MapsTo (fun t : ℝ => 1 - t) (Icc (0 : ℝ) 1) (Ici 0) := by
    intro t ht
    exact sub_nonneg.mpr ht.2
  have hc := hg.comp_of_eq (x := (1 : ℝ)) (f := fun t : ℝ => 1 - t)
    (continuous_const.sub continuous_id).continuousWithinAt hm (by norm_num)
  exact hc.congr hr (hr 1 ⟨zero_le_one, le_rfl⟩)

theorem continuousOn_logSineModePrimitive {δ : ℝ} (hδ : 0 < δ) (z : ℂ)
    (hz : logSineQuantileTransform δ z = 0) :
    ContinuousOn (logSineModePrimitive δ z) (Icc (0 : ℝ) 1) := by
  intro t ht
  by_cases h0 : t = 0
  · subst t
    exact (continuousWithinAt_modePrimitive_left hδ z).mono Icc_subset_Ici_self
  by_cases h1 : t = 1
  · subst t
    apply continuousWithinAt_right_of_reflection (continuousWithinAt_modePrimitive_left hδ (-z)).neg
    intro t ht
    have hu : 1 - t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
    have he := logSineModePrimitive_one_sub hδ z hz hu
    rw [show 1 - (1 - t) = t by ring] at he
    exact he
  exact (hasDerivAt_logSineModePrimitive hδ z
    ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩).continuousAt.continuousWithinAt

theorem continuousOn_logSineQuantileMode {δ : ℝ} (hδ : 0 < δ) (z : ℂ)
    (hz : logSineQuantileTransform δ z = 0) :
    ContinuousOn (logSineQuantileMode δ z) (Icc (0 : ℝ) 1) := by
  intro t ht
  by_cases h0 : t = 0
  · subst t
    exact (continuousWithinAt_quantileMode_left hδ z).mono Icc_subset_Ici_self
  by_cases h1 : t = 1
  · subst t
    apply continuousWithinAt_right_of_reflection (continuousWithinAt_quantileMode_left hδ (-z))
    intro t ht
    have hu : 1 - t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
    have he := logSineQuantileMode_one_sub hδ z hz hu
    rw [show 1 - (1 - t) = t by ring] at he
    exact he
  have htI : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩
  exact (continuousAt_const.mul (continuousAt_logSineQuantileSpeed hδ.le htI).ofReal |>.mul
    (hasDerivAt_logSineModePrimitive hδ z htI).continuousAt).continuousWithinAt

theorem logSineModePrimitive_one {δ : ℝ} (hδ : 0 < δ) (z : ℂ)
    (hz : logSineQuantileTransform δ z = 0) : logSineModePrimitive δ z 1 = 0 := by
  simpa only [sub_zero, logSineModePrimitive_zero, neg_zero] using
    logSineModePrimitive_one_sub hδ z hz (t := 0) ⟨le_rfl, zero_le_one⟩

/-- The actual mode is normalized, so it cannot vanish in L2. -/
theorem integral_logSineQuantileMode {δ : ℝ} (hδ : 0 < δ) (z : ℂ)
    (hz : logSineQuantileTransform δ z = 0) :
    (∫ t in (0 : ℝ)..1, logSineQuantileMode δ z t) = 1 := by
  have hf : IntervalIntegrable (logSineQuantileMode δ z) volume 0 1 :=
    (continuousOn_logSineQuantileMode hδ z hz).intervalIntegrable_of_Icc zero_le_one
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (continuousOn_logSineModePrimitive hδ z hz)
    (fun t ht => hasDerivAt_logSineModePrimitive hδ z ht) (hf.sub intervalIntegrable_const)
  rw [intervalIntegral.integral_sub hf intervalIntegrable_const,
    logSineModePrimitive_one hδ z hz, logSineModePrimitive_zero] at hi
  have hi' : (∫ t in (0 : ℝ)..1, logSineQuantileMode δ z t) - 1 = 0 := by simpa using hi
  exact sub_eq_zero.mp hi'

/-- The primitive agrees with the literal pinned prefix on the complete interval. -/
theorem logSineModePrimitive_eq_pinnedIntegral {δ : ℝ} (hδ : 0 < δ) (z : ℂ)
    (hz : logSineQuantileTransform δ z = 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    logSineModePrimitive δ z t = (∫ s in (0 : ℝ)..t, logSineQuantileMode δ z s) - t := by
  have hf : IntervalIntegrable (logSineQuantileMode δ z) volume 0 t :=
    ((continuousOn_logSineQuantileMode hδ z hz).mono
    (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  have hg := (continuousOn_logSineModePrimitive hδ z hz).mono (Icc_subset_Icc le_rfl ht.2)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hg
    (fun s hs => hasDerivAt_logSineModePrimitive hδ z ⟨hs.1, hs.2.trans_le ht.2⟩)
    (hf.sub intervalIntegrable_const)
  rw [intervalIntegral.integral_sub hf intervalIntegrable_const,
    logSineModePrimitive_zero] at hi
  simpa using hi.symm

/-- The explicit normalized mode belongs to the actual quantile Hilbert space. -/
theorem memLp_logSineQuantileMode {δ : ℝ} (hδ : 0 < δ) (z : ℂ)
    (hz : logSineQuantileTransform δ z = 0) :
    MemLp (logSineQuantileMode δ z) 2 unitIntervalMeasure := by
  have hc := continuousOn_logSineQuantileMode hδ z hz
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine MemLp.of_bound (μ := unitIntervalMeasure) ?_ C ?_
  · exact hc.aestronglyMeasurable measurableSet_Icc
  · exact (ae_restrict_mem measurableSet_Icc).mono (fun t ht => hC t ht)

/-- The literal L2 vector, with its endpoint and integrability obligations discharged. -/
def logSineModeVector {δ : ℝ} (hδ : 0 < δ) (z : ℂ)
    (hz : logSineQuantileTransform δ z = 0) : H :=
  (memLp_logSineQuantileMode hδ z hz).toLp (logSineQuantileMode δ z)

theorem logSineModeVector_coeFn {δ : ℝ} (hδ : 0 < δ) (z : ℂ)
    (hz : logSineQuantileTransform δ z = 0) :
    (logSineModeVector hδ z hz : ℝ → ℂ) =ᵐ[unitIntervalMeasure] logSineQuantileMode δ z :=
  (memLp_logSineQuantileMode hδ z hz).coeFn_toLp

theorem pinnedMean_logSineModeVector {δ : ℝ} (hδ : 0 < δ) (z : ℂ)
    (hz : logSineQuantileTransform δ z = 0) : pinnedMean (logSineModeVector hδ z hz) = 1 := by
  rw [pinnedMean, integral_congr_ae (logSineModeVector_coeFn hδ z hz)]
  change (∫ t in Icc (0 : ℝ) 1, logSineQuantileMode δ z t) = 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  exact integral_logSineQuantileMode hδ z hz

theorem logSineModeVector_ne_zero {δ : ℝ} (hδ : 0 < δ) (z : ℂ)
    (hz : logSineQuantileTransform δ z = 0) : logSineModeVector hδ z hz ≠ 0 := by
  intro hzero
  have h := norm_pinnedMean_le (logSineModeVector hδ z hz)
  rw [pinnedMean_logSineModeVector hδ z hz, hzero, norm_zero, norm_one] at h
  norm_num at h

theorem pinnedVolterraFun_logSineModeVector {δ : ℝ} (hδ : 0 < δ) (z : ℂ)
    (hz : logSineQuantileTransform δ z = 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pinnedVolterraFun (logSineModeVector hδ z hz) t = logSineModePrimitive δ z t := by
  have hae := logSineModeVector_coeFn hδ z hz
  have hs : uIoc (0 : ℝ) t ⊆ Icc (0 : ℝ) 1 := by
    rw [uIoc_of_le ht.1]
    intro s hs
    exact ⟨hs.1.le, hs.2.trans ht.2⟩
  have hlocal : (logSineModeVector hδ z hz : ℝ → ℂ) =ᵐ[volume.restrict (uIoc 0 t)]
      logSineQuantileMode δ z :=
    hae.filter_mono (ae_mono (Measure.restrict_mono_set volume hs))
  rw [pinnedVolterraFun, pinnedMean_logSineModeVector hδ z hz, mul_one,
    pinnedPrefix_eq_intervalIntegral _ ht, intervalIntegral.integral_congr_ae_restrict hlocal,
    logSineModePrimitive_eq_pinnedIntegral hδ z hz ht]

theorem logSineQuantileTransform_zero (δ : ℝ) : logSineQuantileTransform δ 0 = 1 := by
  norm_num [logSineQuantileTransform]

/-- The genuine L2 mode satisfies the literal singular pinned-inverse equation. -/
theorem logSineModeVector_root {δ : ℝ} (hδ : 0 < δ) (z : ℂ)
    (hz : logSineQuantileTransform δ z = 0) :
    (fun t => Complex.I * (logSineQuantileSpeed δ t : ℂ) *
        (pinnedVolterra (logSineModeVector hδ z hz)) t) =ᵐ[unitIntervalMeasure]
      fun t => (-z⁻¹) * (logSineModeVector hδ z hz) t := by
  have hz0 : z ≠ 0 := by
    intro he
    rw [he, logSineQuantileTransform_zero] at hz
    exact one_ne_zero hz
  have hmem : ∀ᵐ t ∂unitIntervalMeasure, t ∈ Icc (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Icc
  filter_upwards [pinnedVolterra_coeFn (logSineModeVector hδ z hz),
    logSineModeVector_coeFn hδ z hz, hmem] with t hv hf ht
  rw [hv, pinnedVolterraFun_logSineModeVector hδ z hz ht, hf, logSineQuantileMode]
  field_simp

/-- Nonreal modes survive strict concavity and all shifted conductance Hankel inequalities. -/
theorem logSine_positive_hankel_nonreal_pinned_mode :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η →
      StrictConcaveOn ℝ (Ioo (0 : ℝ) 1) (logSineProfile δ) ∧
      (∀ n : ℕ, 0 < logSineConductance δ (n + 1)) ∧
      (∀ (shift : ℕ) (F : Finset ℕ) (c : ℕ → ℝ),
        0 ≤ ∑ m ∈ F, ∑ n ∈ F, c m * c n * logSineConductance δ (m + n + shift + 1)) ∧
      ∃ (lam : ℂ) (f : H), lam.im ≠ 0 ∧ f ≠ 0 ∧ pinnedMean f = 1 ∧
        (fun t => Complex.I * (logSineQuantileSpeed δ t : ℂ) * (pinnedVolterra f) t)
          =ᵐ[unitIntervalMeasure] fun t => lam * f t := by
  obtain ⟨η, hη, hzero⟩ := exists_nonreal_zero_logSineQuantileTransform
  refine ⟨η, hη, fun δ hδ hsmall => ⟨strictConcaveOn_logSineProfile hδ.le,
    logSineConductance_succ_pos hδ.le, logSineConductance_hankel_nonneg hδ.le, ?_⟩⟩
  obtain ⟨z, hz, hzim⟩ := hzero δ hδ hsmall
  have hz0 : z ≠ 0 := by intro he; exact hzim (by rw [he]; rfl)
  refine ⟨-z⁻¹, logSineModeVector hδ z hz, ?_, logSineModeVector_ne_zero hδ z hz,
    pinnedMean_logSineModeVector hδ z hz, logSineModeVector_root hδ z hz⟩
  rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
  exact div_ne_zero hzim (Complex.normSq_pos.mpr hz0).ne'

end
end RHTower
