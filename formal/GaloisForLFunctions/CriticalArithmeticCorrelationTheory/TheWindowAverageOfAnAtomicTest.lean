import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheGammaFormPaysEveryFrequencyAboveAThreshold
import GaloisForLFunctions.RHTower.WeilFullConeHerglotzRightHalfPlane
import GaloisForLFunctions.RHTower.EvenSectorFarBumpPoleFreeCombination
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheArchimedeanCrossKernel

/-!
# The window average of an atomic test

Averaging the bump `g` over a window of length `h`, `g_h = h⁻¹ (g ∗ 1_{[0,h)})` (`smoothedBump`),
multiplies its transform by `m_h(r) = h⁻¹ ∫_0^h e^{irs} ds` (`paperFT_smoothedBump`), with
`|1 − m_h(r)| ≤ |r| h` and `|1 − m_h(r)| ≤ 2`. For an atomic test `f_V = Σ_n V(n) g(· − log n)`
the difference `f_V − f_V^{(h)}` therefore has low Fourier mass at most `(T h)² ∫ f_V²` below `T`
and high Fourier mass at most `4 ∫ f_V²` (`lowFourierMass_atomicTest_sub_smoothedBump_le`,
`highFourierMass_atomicTest_sub_smoothedBump_le`).

The average itself is the bump convolved with the window sums
`W_V(s) = Σ_{log n ∈ (s − h, s]} V(n)` (`atomicTest_smoothedBump_eq`), so for a nonnegative bump
`∫ (f_V^{(h)})² ≤ (∫ g)² h⁻² ∫ W_V²` (`integral_sq_atomicTest_smoothedBump_le`): below the
frequency `1/h` an atomic test sees only the sums of its coefficients over windows of
logarithmic length `h`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Zeta23 RHTower
open scoped ComplexConjugate

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open ArithmeticCastelnuovoSeveri ArithmeticPositivityTheory SpacingScaleHarmonicAnalysis
  ArithmeticElectrostatics

variable {g : ℝ → ℝ} {h : ℝ}

/-- The indicator of the averaging window `[0, h)`. -/
def windowKernel (h : ℝ) : ℝ → ℝ := (Ico 0 h).indicator fun _ => 1

theorem windowKernel_nonneg (h s : ℝ) : 0 ≤ windowKernel h s := by
  unfold windowKernel; exact indicator_nonneg (fun _ _ => zero_le_one) s

theorem windowKernel_le_one (h s : ℝ) : windowKernel h s ≤ 1 := by
  unfold windowKernel; exact indicator_le_self' (fun _ _ => zero_le_one) s

theorem measurable_windowKernel (h : ℝ) : Measurable (windowKernel h) :=
  measurable_const.indicator measurableSet_Ico

theorem integrable_windowKernel (h : ℝ) : Integrable (windowKernel h) := by
  unfold windowKernel
  exact (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const measure_Ico_lt_top.ne)

theorem hasCompactSupport_windowKernel (h : ℝ) : HasCompactSupport (windowKernel h) := by
  refine HasCompactSupport.intro (K := Icc 0 h) isCompact_Icc fun s hs => ?_
  unfold windowKernel
  exact indicator_of_notMem (fun h' => hs (Ico_subset_Icc_self h')) _

/-- The bump averaged over a window of length `h`: `g_h = h⁻¹ (g ∗ 1_{[0,h)})`. -/
def smoothedBump (g : ℝ → ℝ) (h : ℝ) (v : ℝ) : ℝ :=
  h⁻¹ * convolution g (windowKernel h) (ContinuousLinearMap.mul ℝ ℝ) volume v

theorem smoothedBump_apply (g : ℝ → ℝ) (h v : ℝ) :
    smoothedBump g h v = h⁻¹ * ∫ t, g t * windowKernel h (v - t) := by
  rw [smoothedBump, convolution_def]; rfl

theorem contDiff_smoothedBump (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (h : ℝ) :
    ContDiff ℝ 2 (smoothedBump g h) :=
  contDiff_const.mul (hgc.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hg
    (integrable_windowKernel h).locallyIntegrable)

theorem smoothedBump_eq_zero {w : ℝ} (hgsupp : ∀ u, u ∉ Icc 0 w → g u = 0) {v : ℝ}
    (hv : v ∉ Icc 0 (w + h)) : smoothedBump g h v = 0 := by
  rw [smoothedBump_apply]
  have : ∀ t, g t * windowKernel h (v - t) = 0 := by
    intro t
    by_cases ht : t ∈ Icc 0 w
    · have hk : v - t ∉ Ico 0 h := by
        intro hk
        exact hv ⟨by linarith [hk.1, ht.1], by linarith [hk.2, ht.2]⟩
      rw [windowKernel, indicator_of_notMem hk, mul_zero]
    · rw [hgsupp t ht, zero_mul]
  simp [this]

/-- The Fourier multiplier of the window average: `h⁻¹ ∫_0^h e^{irs} ds`. -/
def windowMultiplier (h r : ℝ) : ℂ := (h⁻¹ : ℂ) * paperFT (cx (windowKernel h)) r

theorem paperFT_windowKernel (h r : ℝ) :
    paperFT (cx (windowKernel h)) r = ∫ s in Ico 0 h, Complex.exp (Complex.I * r * s) := by
  rw [paperFT_def, ← integral_indicator measurableSet_Ico]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  by_cases hs : s ∈ Ico 0 h
  · simp [cx, windowKernel, indicator_of_mem hs]
  · simp [cx, windowKernel, indicator_of_notMem hs]

theorem norm_one_sub_windowMultiplier_le (hh : 0 < h) (r : ℝ) :
    ‖1 - windowMultiplier h r‖ ≤ |r| * h := by
  have hvol : volume.real (Ico (0 : ℝ) h) = h := by
    rw [measureReal_def, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]; ring
  have hint : IntegrableOn (fun s : ℝ => Complex.exp (Complex.I * r * s)) (Ico 0 h) :=
    (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ico_subset_Icc_self
  have h1int : IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Ico 0 h) :=
    integrableOn_const measure_Ico_lt_top.ne
  have hone : (1 : ℂ) = (h⁻¹ : ℂ) * ∫ s in Ico 0 h, (1 : ℂ) := by
    rw [setIntegral_const, Complex.real_smul, hvol, mul_one,
      inv_mul_cancel₀ (by exact_mod_cast hh.ne')]
  rw [windowMultiplier, paperFT_windowKernel, hone, ← mul_sub,
    ← integral_sub (h1int : Integrable (fun _ : ℝ => (1 : ℂ)) (volume.restrict (Ico 0 h))) hint,
    norm_mul]
  have hb : ‖∫ s in Ico 0 h, ((1 : ℂ) - Complex.exp (Complex.I * r * s))‖ ≤ (|r| * h) * h := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ico (0 : ℝ) h)
      (C := |r| * h) measure_Ico_lt_top (f := fun s : ℝ => (1 : ℂ) - Complex.exp (Complex.I * r * s))
      (fun s hs => by
        rw [norm_sub_rev, show Complex.I * (r : ℂ) * (s : ℂ) = Complex.I * ((r * s : ℝ) : ℂ) by
          push_cast; ring]
        refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg hs.1]; exact hs.2.le) (abs_nonneg r))
    rwa [hvol] at this
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  calc h⁻¹ * ‖∫ s in Ico 0 h, ((1 : ℂ) - Complex.exp (Complex.I * r * s))‖
      ≤ h⁻¹ * ((|r| * h) * h) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hh.le)
    _ = |r| * h := by field_simp

theorem norm_windowMultiplier_le (hh : 0 < h) (r : ℝ) : ‖windowMultiplier h r‖ ≤ 1 := by
  have hvol : volume.real (Ico (0 : ℝ) h) = h := by
    rw [measureReal_def, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]; ring
  rw [windowMultiplier, paperFT_windowKernel, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hh]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ico (0 : ℝ) h) (C := 1)
    measure_Ico_lt_top (f := fun s : ℝ => Complex.exp (Complex.I * r * s))
    (fun s _ => by
      rw [show Complex.I * (r : ℂ) * (s : ℂ) = ((r * s : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact (Complex.norm_exp_ofReal_mul_I _).le)
  rw [hvol, one_mul] at hb
  calc h⁻¹ * ‖∫ s in Ico 0 h, Complex.exp (Complex.I * r * s)‖ ≤ h⁻¹ * h :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hh.le)
    _ = 1 := inv_mul_cancel₀ hh.ne'

theorem norm_one_sub_windowMultiplier_le_two (hh : 0 < h) (r : ℝ) :
    ‖1 - windowMultiplier h r‖ ≤ 2 := by
  have := norm_sub_le (1 : ℂ) (windowMultiplier h r)
  have h1 := norm_windowMultiplier_le hh r
  rw [norm_one] at this
  linarith

/-- **The window average multiplies the transform by `h⁻¹ ∫_0^h e^{irs} ds`.** -/
theorem paperFT_smoothedBump (hg : Continuous g) (hgc : HasCompactSupport g) (h r : ℝ) :
    paperFT (cx (smoothedBump g h)) r = paperFT (cx g) r * windowMultiplier h r := by
  have hconv : cx (smoothedBump g h) = fun v => (h⁻¹ : ℂ) *
      convolution (cx g) (cx (windowKernel h)) (ContinuousLinearMap.mul ℝ ℂ) volume v := by
    funext v
    simp only [cx, smoothedBump_apply, convolution_def, ContinuousLinearMap.mul_apply']
    push_cast
    rw [← integral_complex_ofReal]
    push_cast
    rfl
  have hfc := WeilHerglotz.paperFT_convolution (f := cx g) (g := cx (windowKernel h))
    (hg.integrable_of_hasCompactSupport hgc).ofReal
    (integrable_windowKernel h).ofReal
    (hgc.comp_left Complex.ofReal_zero) ((hasCompactSupport_windowKernel h).comp_left
      Complex.ofReal_zero) r
  rw [hconv, paperFT_const_mul, hfc, windowMultiplier]
  ring

/-! ### The atomic test minus its window average -/

theorem hasCompactSupport_of_support_Icc {w : ℝ} (hgsupp : ∀ u, u ∉ Icc 0 w → g u = 0) :
    HasCompactSupport g :=
  HasCompactSupport.intro isCompact_Icc fun u hu => hgsupp u hu

theorem atomicTest_sub_smoothedBump (B : ℕ) (V : ℕ → ℝ) (g : ℝ → ℝ) (h u : ℝ) :
    atomicTest B V g u - atomicTest B V (smoothedBump g h) u =
      atomicTest B V (fun v => g v - smoothedBump g h v) u := by
  unfold atomicTest
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **Removing the window average multiplies the transform by `1 − m_h`.** -/
theorem paperFT_atomicTest_sub_smoothedBump (hg : ContDiff ℝ 2 g) {w : ℝ}
    (hgsupp : ∀ u, u ∉ Icc 0 w → g u = 0) (B : ℕ) (V : ℕ → ℝ) (h r : ℝ) :
    paperFT (cx fun u => atomicTest B V g u - atomicTest B V (smoothedBump g h) u) r =
      (1 - windowMultiplier h r) * paperFT (cx (atomicTest B V g)) r := by
  have hgc := hasCompactSupport_of_support_Icc hgsupp
  have hsc : HasCompactSupport (smoothedBump g h) :=
    HasCompactSupport.intro (K := Icc 0 (w + h)) isCompact_Icc fun v hv =>
      smoothedBump_eq_zero hgsupp hv
  have hsC := (contDiff_smoothedBump hg hgc h).continuous
  have hdc : Continuous fun v => g v - smoothedBump g h v := hg.continuous.sub hsC
  have hdcs : HasCompactSupport fun v => g v - smoothedBump g h v := hgc.sub hsc
  have hfun : (fun u => atomicTest B V g u - atomicTest B V (smoothedBump g h) u) =
      atomicTest B V (fun v => g v - smoothedBump g h v) :=
    funext fun u => atomicTest_sub_smoothedBump B V g h u
  have hlin : paperFT (cx fun v => g v - smoothedBump g h v) r =
      paperFT (cx g) r - paperFT (cx (smoothedBump g h)) r := by
    have := EvenSector.paperFT_ofReal_add_smul hg.continuous hgc hsC hsc 1 (-1) r
    have hf : (fun u => (((1 : ℝ) * g u + (-1 : ℝ) * smoothedBump g h u : ℝ) : ℂ)) =
        cx fun v => g v - smoothedBump g h v := by
      funext u; simp only [cx]; push_cast; ring
    rw [hf] at this
    rw [this]
    show _ = paperFT (fun u => (g u : ℂ)) r - paperFT (fun u => (smoothedBump g h u : ℂ)) r
    push_cast
    ring
  rw [hfun, paperFT_atomicTest hdc hdcs, hlin, paperFT_smoothedBump hg.continuous hgc,
    paperFT_atomicTest hg.continuous hgc]
  ring

theorem lowFourierMass_le_integral_sq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (T : ℝ) : lowFourierMass f T ≤ ∫ u, f u ^ 2 := by
  have := lowFourierMass_add_highFourierMass hf hfc T
  have := highFourierMass_nonneg f T
  linarith

theorem highFourierMass_le_integral_sq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (T : ℝ) : highFourierMass f T ≤ ∫ u, f u ^ 2 := by
  have := lowFourierMass_add_highFourierMass hf hfc T
  have := lowFourierMass_nonneg f T
  linarith

/-- **Below `T` the window average is accurate to `T h`.** -/
theorem lowFourierMass_atomicTest_sub_smoothedBump_le (hg : ContDiff ℝ 2 g) {w : ℝ}
    (hgsupp : ∀ u, u ∉ Icc 0 w → g u = 0) (hh : 0 < h) (B : ℕ) (V : ℕ → ℝ) (T : ℝ) :
    lowFourierMass (fun u => atomicTest B V g u - atomicTest B V (smoothedBump g h) u) T ≤
      (T * h) ^ 2 * ∫ u, atomicTest B V g u ^ 2 := by
  have hgc := hasCompactSupport_of_support_Icc hgsupp
  have hsc : HasCompactSupport (smoothedBump g h) :=
    HasCompactSupport.intro (K := Icc 0 (w + h)) isCompact_Icc fun v hv =>
      smoothedBump_eq_zero hgsupp hv
  have hF := contDiff_atomicTest hg B V
  have hFc := hasCompactSupport_atomicTest hgsupp B V
  have hFh := contDiff_atomicTest (contDiff_smoothedBump hg hgc h) B V
  have hFhc : HasCompactSupport (atomicTest B V (smoothedBump g h)) :=
    hasCompactSupport_atomicTest (w := w + h) (fun v hv => smoothedBump_eq_zero hgsupp hv) B V
  have hD : ContDiff ℝ 2 fun u => atomicTest B V g u - atomicTest B V (smoothedBump g h) u :=
    hF.sub hFh
  have hDc : HasCompactSupport fun u => atomicTest B V g u - atomicTest B V (smoothedBump g h) u :=
    hFc.sub hFhc
  have hiD : Integrable fun r : ℝ =>
      ‖paperFT (cx fun u => atomicTest B V g u - atomicTest B V (smoothedBump g h) u) r‖ ^ 2 :=
    integrable_normSq_paperFT_ofReal hD hDc
  have hiF : Integrable fun r : ℝ => ‖paperFT (cx (atomicTest B V g)) r‖ ^ 2 :=
    integrable_normSq_paperFT_ofReal hF hFc
  have hmono : ∫ r in (highFrequencies T)ᶜ,
      ‖paperFT (cx fun u => atomicTest B V g u - atomicTest B V (smoothedBump g h) u) r‖ ^ 2 ≤
      ∫ r in (highFrequencies T)ᶜ, (T * h) ^ 2 * ‖paperFT (cx (atomicTest B V g)) r‖ ^ 2 := by
    refine setIntegral_mono_on hiD.integrableOn (hiF.const_mul _).integrableOn
      (measurableSet_highFrequencies T).compl fun r hr => ?_
    have hrT : |r| < T := by
      simpa [highFrequencies] using hr
    rw [paperFT_atomicTest_sub_smoothedBump hg hgsupp, norm_mul, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    refine pow_le_pow_left₀ (norm_nonneg _) ((norm_one_sub_windowMultiplier_le hh r).trans ?_) 2
    exact mul_le_mul_of_nonneg_right hrT.le hh.le
  rw [integral_const_mul] at hmono
  have hlow := lowFourierMass_le_integral_sq hF hFc T
  unfold lowFourierMass at hlow ⊢
  have hpi : 0 ≤ 1 / (2 * Real.pi) := by positivity
  calc 1 / (2 * Real.pi) * ∫ r in (highFrequencies T)ᶜ,
        ‖paperFT (cx fun u => atomicTest B V g u - atomicTest B V (smoothedBump g h) u) r‖ ^ 2
      ≤ 1 / (2 * Real.pi) * ((T * h) ^ 2 *
          ∫ r in (highFrequencies T)ᶜ, ‖paperFT (cx (atomicTest B V g)) r‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmono hpi
    _ = (T * h) ^ 2 * (1 / (2 * Real.pi) *
          ∫ r in (highFrequencies T)ᶜ, ‖paperFT (cx (atomicTest B V g)) r‖ ^ 2) := by ring
    _ ≤ (T * h) ^ 2 * ∫ u, atomicTest B V g u ^ 2 :=
        mul_le_mul_of_nonneg_left hlow (sq_nonneg _)

/-- Above any threshold, removing the window average at most doubles the transform. -/
theorem highFourierMass_atomicTest_sub_smoothedBump_le (hg : ContDiff ℝ 2 g) {w : ℝ}
    (hgsupp : ∀ u, u ∉ Icc 0 w → g u = 0) (hh : 0 < h) (B : ℕ) (V : ℕ → ℝ) (T : ℝ) :
    highFourierMass (fun u => atomicTest B V g u - atomicTest B V (smoothedBump g h) u) T ≤
      4 * ∫ u, atomicTest B V g u ^ 2 := by
  have hgc := hasCompactSupport_of_support_Icc hgsupp
  have hF := contDiff_atomicTest hg B V
  have hFc := hasCompactSupport_atomicTest hgsupp B V
  have hFh := contDiff_atomicTest (contDiff_smoothedBump hg hgc h) B V
  have hFhc : HasCompactSupport (atomicTest B V (smoothedBump g h)) :=
    hasCompactSupport_atomicTest (w := w + h) (fun v hv => smoothedBump_eq_zero hgsupp hv) B V
  have hiD : Integrable fun r : ℝ =>
      ‖paperFT (cx fun u => atomicTest B V g u - atomicTest B V (smoothedBump g h) u) r‖ ^ 2 :=
    integrable_normSq_paperFT_ofReal (hF.sub hFh) (hFc.sub hFhc)
  have hiF : Integrable fun r : ℝ => ‖paperFT (cx (atomicTest B V g)) r‖ ^ 2 :=
    integrable_normSq_paperFT_ofReal hF hFc
  have hmono : ∫ r in highFrequencies T,
      ‖paperFT (cx fun u => atomicTest B V g u - atomicTest B V (smoothedBump g h) u) r‖ ^ 2 ≤
      ∫ r in highFrequencies T, 4 * ‖paperFT (cx (atomicTest B V g)) r‖ ^ 2 := by
    refine setIntegral_mono_on hiD.integrableOn (hiF.const_mul _).integrableOn
      (measurableSet_highFrequencies T) fun r _ => ?_
    rw [paperFT_atomicTest_sub_smoothedBump hg hgsupp, norm_mul, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have h2 := norm_one_sub_windowMultiplier_le_two hh r
    nlinarith [norm_nonneg (1 - windowMultiplier h r)]
  rw [integral_const_mul] at hmono
  have hhigh := highFourierMass_le_integral_sq hF hFc T
  unfold highFourierMass at hhigh ⊢
  have hpi : 0 ≤ 1 / (2 * Real.pi) := by positivity
  calc 1 / (2 * Real.pi) * ∫ r in highFrequencies T,
        ‖paperFT (cx fun u => atomicTest B V g u - atomicTest B V (smoothedBump g h) u) r‖ ^ 2
      ≤ 1 / (2 * Real.pi) * (4 *
          ∫ r in highFrequencies T, ‖paperFT (cx (atomicTest B V g)) r‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmono hpi
    _ = 4 * (1 / (2 * Real.pi) *
          ∫ r in highFrequencies T, ‖paperFT (cx (atomicTest B V g)) r‖ ^ 2) := by ring
    _ ≤ 4 * ∫ u, atomicTest B V g u ^ 2 := mul_le_mul_of_nonneg_left hhigh (by norm_num)

/-! ### The window average is the convolution of the bump with the window sums -/

/-- The window sum `W(s) = Σ_{log n ∈ (s − h, s]} V(n)`. -/
def windowSum (B : ℕ) (V : ℕ → ℝ) (h s : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 B, V n * windowKernel h (s - Real.log n)

theorem measurable_windowSum (B : ℕ) (V : ℕ → ℝ) (h : ℝ) : Measurable (windowSum B V h) := by
  unfold windowSum
  exact Finset.measurable_sum _ fun n _ =>
    measurable_const.mul ((measurable_windowKernel h).comp (measurable_id.sub measurable_const))

theorem abs_windowSum_le (B : ℕ) (V : ℕ → ℝ) (h s : ℝ) :
    |windowSum B V h s| ≤ ∑ n ∈ Finset.Icc 1 B, |V n| := by
  unfold windowSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [abs_mul, abs_of_nonneg (windowKernel_nonneg _ _)]
  exact mul_le_of_le_one_right (abs_nonneg _) (windowKernel_le_one _ _)

theorem integrable_windowSum (B : ℕ) (V : ℕ → ℝ) (h : ℝ) : Integrable (windowSum B V h) := by
  unfold windowSum
  refine integrable_finsetSum _ fun n _ => ((integrable_windowKernel h).comp_sub_right
    (Real.log n)).const_mul (V n)

theorem integrable_windowSum_sq (B : ℕ) (V : ℕ → ℝ) (h : ℝ) :
    Integrable fun s => windowSum B V h s ^ 2 := by
  refine ((integrable_windowSum B V h).norm.const_mul (∑ n ∈ Finset.Icc 1 B, |V n|)).mono'
    ((measurable_windowSum B V h).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_pow, sq, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_windowSum_le B V h s) (abs_nonneg _)

theorem integrable_mul_comp_sub {f k : ℝ → ℝ} (hf : Integrable f) (hk : Measurable k) {C : ℝ}
    (hkC : ∀ s, |k s| ≤ C) (a : ℝ) : Integrable fun t => f t * k (a - t) := by
  refine (hf.norm.const_mul C).mono'
    (hf.aestronglyMeasurable.mul (hk.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hkC _) (abs_nonneg _)

/-- **The smoothed atomic test is the bump convolved with the window sums.** -/
theorem atomicTest_smoothedBump_eq (hg : Continuous g) (hgc : HasCompactSupport g) (B : ℕ)
    (V : ℕ → ℝ) (h u : ℝ) :
    atomicTest B V (smoothedBump g h) u = h⁻¹ * ∫ t, g t * windowSum B V h (u - t) := by
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hkC : ∀ s, |windowKernel h s| ≤ 1 := fun s => by
    rw [abs_of_nonneg (windowKernel_nonneg h s)]; exact windowKernel_le_one h s
  unfold atomicTest windowSum
  simp_rw [smoothedBump_apply, Finset.mul_sum]
  have hint : ∀ n ∈ Finset.Icc 1 B, Integrable fun t =>
      g t * (V n * windowKernel h (u - t - Real.log n)) := fun n _ => by
    have := (integrable_mul_comp_sub hgi (measurable_windowKernel h) hkC
      (u - Real.log n)).const_mul (V n)
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [show u - Real.log n - t = u - t - Real.log n by ring]
    ring
  rw [integral_finsetSum _ hint, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have : ∀ t, g t * (V n * windowKernel h (u - t - Real.log n)) =
      V n * (g t * windowKernel h (u - Real.log n - t)) := fun t => by
    rw [show u - t - Real.log n = u - Real.log n - t by ring]; ring
  simp_rw [this, integral_const_mul]
  ring

/-- Weighted Cauchy–Schwarz: `(∫ g F)² ≤ (∫ g)(∫ g F²)` for `g ≥ 0` and bounded `F`. -/
theorem sq_integral_mul_le_weighted {g F : ℝ → ℝ} (hg0 : ∀ t, 0 ≤ g t) (hgi : Integrable g)
    (hF : Measurable F) {C : ℝ} (hFC : ∀ t, |F t| ≤ C) :
    (∫ t, g t * F t) ^ 2 ≤ (∫ t, g t) * ∫ t, g t * F t ^ 2 := by
  have hbd : ∀ {k : ℝ → ℝ}, Measurable k → ∀ {D : ℝ}, (∀ t, |k t| ≤ D) →
      Integrable fun t => g t * k t := fun {k} hk {D} hkD => by
    refine (hgi.norm.const_mul D).mono' (hgi.aestronglyMeasurable.mul hk.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs, mul_comm D]
    exact mul_le_mul_of_nonneg_left (hkD t) (abs_nonneg _)
  have i1 : Integrable fun t => g t * F t := hbd hF hFC
  have i2 : Integrable fun t => g t * F t ^ 2 := hbd (hF.pow_const 2) (D := C ^ 2) fun t => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hFC t) 2
  have hq : ∀ x : ℝ, 0 ≤ (∫ t, g t) * (x * x) + (-2 * ∫ t, g t * F t) * x +
      ∫ t, g t * F t ^ 2 := by
    intro x
    have hnn : 0 ≤ ∫ t, g t * (F t - x) ^ 2 :=
      integral_nonneg fun t => mul_nonneg (hg0 t) (sq_nonneg _)
    have e : (fun t => g t * (F t - x) ^ 2) =
        fun t => (g t * F t ^ 2 - 2 * x * (g t * F t)) + x ^ 2 * g t := by
      funext t; ring
    rw [e, integral_add (f := fun t => g t * F t ^ 2 - 2 * x * (g t * F t))
        (g := fun t => x ^ 2 * g t) (i2.sub (i1.const_mul _)) (hgi.const_mul _),
      integral_sub (f := fun t => g t * F t ^ 2) (g := fun t => 2 * x * (g t * F t)) i2
        (i1.const_mul _), integral_const_mul, integral_const_mul] at hnn
    nlinarith [hnn]
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith [hd]

/-- **The smoothed atomic test is bounded by the window sums.** For a nonnegative bump,
`∫ (f_V^{(h)})² ≤ (∫ g)² h⁻² ∫ W_V²`. -/
theorem integral_sq_atomicTest_smoothedBump_le (hg : ContDiff ℝ 2 g) {w : ℝ}
    (hgsupp : ∀ u, u ∉ Icc 0 w → g u = 0) (hg0 : ∀ u, 0 ≤ g u) (hh : 0 < h) (B : ℕ)
    (V : ℕ → ℝ) :
    ∫ u, atomicTest B V (smoothedBump g h) u ^ 2 ≤
      (∫ t, g t) ^ 2 / h ^ 2 * ∫ s, windowSum B V h s ^ 2 := by
  have hgc := hasCompactSupport_of_support_Icc hgsupp
  have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  set W := windowSum B V h
  set I := ∫ t, g t
  have hCW : ∀ s, |W s| ≤ ∑ n ∈ Finset.Icc 1 B, |V n| := abs_windowSum_le B V h
  have hW2i := integrable_windowSum_sq B V h
  have hW2C : ∀ s, |W s ^ 2| ≤ (∑ n ∈ Finset.Icc 1 B, |V n|) ^ 2 := fun s => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCW s) 2
  have hWm := measurable_windowSum B V h
  have hcs : ∀ u, (∫ t, g t * W (u - t)) ^ 2 ≤ I * ∫ t, g t * W (u - t) ^ 2 := fun u =>
    sq_integral_mul_le_weighted hg0 hgi (hWm.comp (measurable_const.sub measurable_id))
      (fun t => hCW (u - t))
  -- integrate the pointwise bound
  have hconv : ∀ u, ∫ t, g t * W (u - t) ^ 2 =
      convolution g (fun s => W s ^ 2) (ContinuousLinearMap.mul ℝ ℝ) volume u := fun u => by
    rw [convolution_def]; rfl
  have hci : Integrable (convolution g (fun s => W s ^ 2) (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    hgi.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hW2i
  have hFh : ContDiff ℝ 2 (atomicTest B V (smoothedBump g h)) :=
    contDiff_atomicTest (contDiff_smoothedBump hg hgc h) B V
  have hFhc : HasCompactSupport (atomicTest B V (smoothedBump g h)) :=
    hasCompactSupport_atomicTest (w := w + h) (fun v hv => smoothedBump_eq_zero hgsupp hv) B V
  have hFi : Integrable fun u => atomicTest B V (smoothedBump g h) u ^ 2 :=
    integrable_sq_of_continuous hFh.continuous hFhc
  have hpt : ∀ u, atomicTest B V (smoothedBump g h) u ^ 2 ≤
      h⁻¹ ^ 2 * I * convolution g (fun s => W s ^ 2) (ContinuousLinearMap.mul ℝ ℝ) volume u := by
    intro u
    rw [atomicTest_smoothedBump_eq hg.continuous hgc, mul_pow, ← hconv, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hcs u) (sq_nonneg _)
  calc ∫ u, atomicTest B V (smoothedBump g h) u ^ 2
      ≤ ∫ u, h⁻¹ ^ 2 * I *
          convolution g (fun s => W s ^ 2) (ContinuousLinearMap.mul ℝ ℝ) volume u :=
        integral_mono hFi (hci.const_mul _) hpt
    _ = h⁻¹ ^ 2 * I * (I * ∫ s, W s ^ 2) := by
        rw [integral_const_mul, integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hgi hW2i]
        rfl
    _ = I ^ 2 / h ^ 2 * ∫ s, W s ^ 2 := by field_simp

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
