import GaloisForLFunctions.«arithmetic-positivity-theory».CollaredCriticalPrimeChannelUniformBound

/-!
# Logarithmic archimedean coercivity of the collared critical source

This module has three parts.

* **Lévy calculus of a general source.** For a real source `g` whose complex lift is integrable
  and square integrable (`AdmissibleSource`), the autocorrelation is the cosine transform of
  `‖ĝ‖²/2π`. The Lévy jump energy dominates `e^{-1/2}(log R - 3)` times the spectral mass beyond
  `R`. A mass floor `∫ g² ≥ A E` and a low-frequency exclusion `‖ĝ(t)‖² ≤ (2D²/M) E` on
  `|t| ≤ πM` together give `Lévy(g) ≥ e^{-1/2}(A/2)(log M - 3 - log(1/η)) E`.
* **Collared Mellin exclusion.** The collared source `g_c = σ(e^{-x} - 1) g_b` has Mellin
  amplitude `a_c(v) = σ(v - 1) v^{-3/2}`, which vanishes at `v = 1`. One integration by parts
  against `e^{iφ}/(iφ')` then has no boundary terms, giving the oscillatory bound
  `‖∫ a_c e^{i(ωv - t log v)}‖ ≤ (2/|ω|)(‖a_c'‖₁ + ‖a_c/v²‖₁)`. Through the harmonic layers this
  yields `‖ĝ_c(t)‖² ≤ (2D_c²/M) ∑ b_n²` on `|t| ≤ πM`. The Riesz window `[2, 2 + L]` lies beyond
  the collar and gives the mass floor `∫ g_c² ≥ A_c ∑ b_n²`.
* **Collared Lévy–prime form.** Combined with the `ℓ²`-uniform collared prime channel, on every
  dyadic block `M ≤ n + 1 ≤ 2M`:
  `Lévy(g_c) - 2 P_c ≥ (s_c(log M - c_c) - 2C_c) ∑ b_n²`. It is positive definite as soon as
  `s_c(log M - c_c) > 2C_c`, with no restriction on the number of atoms.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
open _root_.Zeta23

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ### Lévy calculus of a general real source -/

/-- A real source is *admissible* when its complex lift is integrable and square integrable. -/
def AdmissibleSource (g : ℝ → ℝ) : Prop :=
  Integrable (fun x => (g x : ℂ)) ∧ MemLp (fun x => (g x : ℂ)) 2

/-- Autocorrelation `ac_g(x) = ∫ g(y) g(y - x) dy`. -/
def sourceAutocorrelation (g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y, g y * g (y - x)

/-- Lévy jump energy `∫_{x>0} (ac_g(0) - ac_g(x)) ω(x) dx`. -/
def sourceLevyEnergy (g : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioi 0, ENNReal.ofReal ((sourceAutocorrelation g 0 - sourceAutocorrelation g x) *
    BiScaleUncertainty.archLevySinhWeight x)

/-- Spectral density `‖ĝ(t)‖²`. -/
def levySourceSpectralDensity (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ‖paperFT (fun y => (g y : ℂ)) t‖ ^ 2

private theorem normSq_add_sub_mul' (a e : ℂ) :
    ‖a + e * a‖ ^ 2 - ‖a - e * a‖ ^ 2 = 4 * (‖a‖ ^ 2 * e.re) := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add, Complex.normSq_sub]
  have : (a * (starRingEnd ℂ) (e * a)).re = Complex.normSq a * e.re := by
    rw [map_mul, show a * ((starRingEnd ℂ) e * (starRingEnd ℂ) a) =
      (a * (starRingEnd ℂ) a) * (starRingEnd ℂ) e by ring, Complex.mul_conj, Complex.re_ofReal_mul,
      Complex.conj_re]
  rw [this]; ring

/-- **Spectral autocorrelation.** `ac_g(x) = (1/2π) ∫ ‖ĝ(t)‖² cos(tx) dt` for admissible `g`. -/
theorem sourceAutocorrelation_eq_spectral {g : ℝ → ℝ} (hg : AdmissibleSource g) (x : ℝ) :
    sourceAutocorrelation g x = 1 / (2 * Real.pi) * ∫ t, levySourceSpectralDensity g t * Real.cos (t * x) := by
  set u : ℝ → ℂ := fun y => (g y : ℂ)
  set w : ℝ → ℂ := fun y => u (y - x)
  obtain ⟨hu1, hu2⟩ := hg
  have hum : AEStronglyMeasurable u volume := hu1.aestronglyMeasurable
  have hw1 : Integrable w := hu1.comp_sub_right x
  have hwm : AEStronglyMeasurable w volume := hw1.aestronglyMeasurable
  have hw2 : MemLp w 2 := (memLp_two_iff_integrable_sq_norm hwm).mpr
    (((memLp_two_iff_integrable_sq_norm hum).mp hu2).comp_sub_right x)
  have hp1 : Integrable (u + (1 : ℂ) • w) := hu1.add (hw1.smul _)
  have hp2 : MemLp (u + (1 : ℂ) • w) 2 := hu2.add (hw2.const_smul _)
  have hm1 : Integrable (u + (-1 : ℂ) • w) := hu1.add (hw1.smul _)
  have hm2 : MemLp (u + (-1 : ℂ) • w) 2 := hu2.add (hw2.const_smul _)
  have hPp := RHTower.KernelStrip.integral_norm_sq_paperFT_of_memLp hp1 hp2
  have hPm := RHTower.KernelStrip.integral_norm_sq_paperFT_of_memLp hm1 hm2
  have hIp := RHTower.KernelStrip.integrable_norm_sq_paperFT hp1 hp2
  have hIm := RHTower.KernelStrip.integrable_norm_sq_paperFT hm1 hm2
  have hFp (t : ℝ) : paperFT (u + (1 : ℂ) • w) t =
      paperFT u t + Complex.exp (Complex.I * t * x) * paperFT u t := by
    rw [RHTower.WeilSpectral.paperFT_add_smul_real hu1 hw1, paperFT_comp_sub_right, one_mul]
  have hFm (t : ℝ) : paperFT (u + (-1 : ℂ) • w) t =
      paperFT u t - Complex.exp (Complex.I * t * x) * paperFT u t := by
    rw [RHTower.WeilSpectral.paperFT_add_smul_real hu1 hw1, paperFT_comp_sub_right]; ring
  have hspec (t : ℝ) : ‖paperFT (u + (1 : ℂ) • w) t‖ ^ 2 - ‖paperFT (u + (-1 : ℂ) • w) t‖ ^ 2 =
      4 * (‖paperFT u t‖ ^ 2 * Real.cos (t * x)) := by
    rw [hFp, hFm, normSq_add_sub_mul',
      show Complex.I * (t : ℂ) * (x : ℂ) = ((t * x : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re]
  have hphys (y : ℝ) : ‖(u + (1 : ℂ) • w) y‖ ^ 2 - ‖(u + (-1 : ℂ) • w) y‖ ^ 2 =
      4 * (g y * g (y - x)) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, u, w, neg_one_mul]
    rw [← Complex.ofReal_add, ← Complex.ofReal_neg, ← Complex.ofReal_add, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
    ring
  have hsq1 := (memLp_two_iff_integrable_sq_norm hp1.aestronglyMeasurable).mp hp2
  have hsq2 := (memLp_two_iff_integrable_sq_norm hm1.aestronglyMeasurable).mp hm2
  have hL : ∫ t : ℝ, 4 * (‖paperFT u t‖ ^ 2 * Real.cos (t * x)) =
      2 * Real.pi * ∫ y, 4 * (g y * g (y - x)) := by
    rw [← integral_congr_ae (Eventually.of_forall hspec), integral_sub hIp hIm, hPp, hPm,
      ← mul_sub, ← integral_sub hsq1 hsq2, integral_congr_ae (Eventually.of_forall hphys)]
  rw [integral_const_mul, integral_const_mul] at hL
  have hpi : 0 < Real.pi := Real.pi_pos
  have hI : ∫ t : ℝ, ‖paperFT u t‖ ^ 2 * Real.cos (t * x) = 2 * Real.pi * ∫ y, g y * g (y - x) := by
    linarith
  unfold sourceAutocorrelation levySourceSpectralDensity
  rw [hI]
  field_simp

theorem integrable_levySourceSpectralDensity {g : ℝ → ℝ} (hg : AdmissibleSource g) :
    Integrable (levySourceSpectralDensity g) :=
  RHTower.KernelStrip.integrable_norm_sq_paperFT hg.1 hg.2

theorem continuous_levySourceSpectralDensity {g : ℝ → ℝ} (hg : AdmissibleSource g) :
    Continuous (levySourceSpectralDensity g) :=
  ((RHTower.WeilHerglotz.continuous_paperFT_real hg.1).norm).pow 2

/-- **Plancherel.** `∫ ‖ĝ‖² = 2π ∫ g²`. -/
theorem integral_levySourceSpectralDensity {g : ℝ → ℝ} (hg : AdmissibleSource g) :
    ∫ t, levySourceSpectralDensity g t = 2 * Real.pi * ∫ y, g y ^ 2 := by
  unfold levySourceSpectralDensity
  rw [RHTower.KernelStrip.integral_norm_sq_paperFT_of_memLp hg.1 hg.2]
  congr 2
  funext y
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Spectral jump.** `ac_g(0) - ac_g(x) = (1/2π) ∫ ‖ĝ(t)‖² (1 - cos(tx)) dt`. -/
theorem sourceAutocorrelation_jump_eq_spectral {g : ℝ → ℝ} (hg : AdmissibleSource g) (x : ℝ) :
    sourceAutocorrelation g 0 - sourceAutocorrelation g x =
      1 / (2 * Real.pi) * ∫ t, levySourceSpectralDensity g t * (1 - Real.cos (t * x)) := by
  have hi := integrable_levySourceSpectralDensity hg
  have hic : Integrable fun t => levySourceSpectralDensity g t * Real.cos (t * x) := by
    refine hi.mono' ((continuous_levySourceSpectralDensity hg).mul (by fun_prop :
      Continuous fun t => Real.cos (t * x))).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    have h0 : 0 ≤ levySourceSpectralDensity g t := sq_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    exact mul_le_of_le_one_right h0 (Real.abs_cos_le_one _)
  rw [sourceAutocorrelation_eq_spectral hg 0, sourceAutocorrelation_eq_spectral hg x, ← mul_sub,
    ← integral_sub (hi.congr (Eventually.of_forall fun t => by simp)) hic]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [mul_zero, Real.cos_zero, mul_one]
  ring

/-- **High-band lower bound of the Lévy energy.** For `R ≥ 1`,
`Lévy(g) ≥ e^{-1/2} (log R - 3) · (1/2π) ∫_{|t|>R} ‖ĝ‖²`. -/
theorem sourceLevyEnergy_ge_highBand {g : ℝ → ℝ} (hg : AdmissibleSource g) {R : ℝ} (hR : 1 ≤ R) :
    ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ)) * (Real.log R - 3)) *
      ENNReal.ofReal (1 / (2 * Real.pi) * ∫ t in (Icc (-R) R)ᶜ, levySourceSpectralDensity g t) ≤
    sourceLevyEnergy g := by
  set m := levySourceSpectralDensity g
  set ω := BiScaleUncertainty.archLevySinhWeight
  set K := ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ)) * (Real.log R - 3))
  have hm0 (t : ℝ) : 0 ≤ m t := sq_nonneg _
  have hmi := integrable_levySourceSpectralDensity hg
  have hmc := continuous_levySourceSpectralDensity hg
  have hpi : 0 < Real.pi := Real.pi_pos
  set F : ℝ → ℝ → ℝ≥0∞ := fun x t =>
    ENNReal.ofReal (ω x / (2 * Real.pi) * (m t * (1 - Real.cos (t * x))))
  have hpt : ∀ x ∈ Ioi (0 : ℝ), ENNReal.ofReal ((sourceAutocorrelation g 0 -
      sourceAutocorrelation g x) * ω x) = ∫⁻ t, F x t := by
    intro x hx
    rw [sourceAutocorrelation_jump_eq_spectral hg]
    have hω := (BiScaleUncertainty.archLevySinhWeight_pos hx).le
    have hint : Integrable fun t => ω x / (2 * Real.pi) * (m t * (1 - Real.cos (t * x))) := by
      refine ((hmi.const_mul 2).const_mul (ω x / (2 * Real.pi))).mono'
        (by fun_prop : Continuous fun t => ω x / (2 * Real.pi) *
          (m t * (1 - Real.cos (t * x)))).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
      have h1 : 0 ≤ 1 - Real.cos (t * x) := by linarith [Real.cos_le_one (t * x)]
      have h2 : 1 - Real.cos (t * x) ≤ 2 := by linarith [Real.neg_one_le_cos (t * x)]
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := hm0 t; positivity)]
      change ω x / (2 * Real.pi) * (m t * (1 - Real.cos (t * x))) ≤ ω x / (2 * Real.pi) * (2 * m t)
      have := hm0 t
      exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun t => by
      have h1 : 0 ≤ 1 - Real.cos (t * x) := by linarith [Real.cos_le_one (t * x)]
      have := hm0 t
      show 0 ≤ ω x / (2 * Real.pi) * (m t * (1 - Real.cos (t * x)))
      positivity)]
    congr 1
    rw [integral_const_mul]; ring
  have hmeas : AEMeasurable (Function.uncurry F) ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    refine Measurable.aemeasurable ?_
    change Measurable fun p : ℝ × ℝ => ENNReal.ofReal (ω p.1 / (2 * Real.pi) *
      (m p.2 * (1 - Real.cos (p.2 * p.1))))
    refine Measurable.ennreal_ofReal ?_
    exact ((BiScaleUncertainty.measurable_archLevySinhWeight.comp measurable_fst).div_const _).mul
      ((hmc.measurable.comp measurable_snd).mul (measurable_const.sub
        (Real.continuous_cos.measurable.comp (measurable_snd.mul measurable_fst))))
  have hinner (t : ℝ) : (Icc (-R) R)ᶜ.indicator (fun t => ENNReal.ofReal (m t / (2 * Real.pi)) * K) t ≤
      ∫⁻ x in Ioi 0, F x t := by
    by_cases ht : t ∈ (Icc (-R) R)ᶜ
    · rw [indicator_of_mem ht]
      have hF : ∀ x, F x t = ENNReal.ofReal (m t / (2 * Real.pi)) *
          ENNReal.ofReal ((1 - Real.cos (t * x)) * ω x) := by
        intro x
        simp only [F]
        rw [← ENNReal.ofReal_mul (by have := hm0 t; positivity)]
        congr 1; ring
      rw [lintegral_congr fun x => hF x, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      have hRt : R < |t| := by
        by_contra hle
        exact ht (abs_le.mp (not_lt.mp hle))
      have h1 : 1 ≤ |t| := hR.trans hRt.le
      refine le_trans (ENNReal.ofReal_le_ofReal ?_)
        (ofReal_log_sub_le_lintegral_one_sub_cos_mul_archLevySinhWeight h1)
      have := Real.log_le_log (by linarith) hRt.le
      have := Real.exp_pos (-(1 / 2 : ℝ))
      nlinarith
    · rw [indicator_of_notMem ht]; exact zero_le
  have hIc : IntegrableOn m (Icc (-R) R)ᶜ := hmi.integrableOn
  calc K * ENNReal.ofReal (1 / (2 * Real.pi) * ∫ t in (Icc (-R) R)ᶜ, m t) =
        K * ∫⁻ t in (Icc (-R) R)ᶜ, ENNReal.ofReal (m t / (2 * Real.pi)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal (hIc.div_const _)
          (Eventually.of_forall fun t => by have := hm0 t; positivity), integral_div]
        congr 2; ring
    _ = ∫⁻ t, (Icc (-R) R)ᶜ.indicator (fun t => ENNReal.ofReal (m t / (2 * Real.pi)) * K) t := by
        rw [lintegral_indicator measurableSet_Icc.compl, lintegral_mul_const' _ _
          ENNReal.ofReal_ne_top, mul_comm]
    _ ≤ ∫⁻ t, ∫⁻ x in Ioi 0, F x t := lintegral_mono hinner
    _ = ∫⁻ x in Ioi 0, ∫⁻ t, F x t := (lintegral_lintegral_swap hmeas).symm
    _ = sourceLevyEnergy g := by
        unfold sourceLevyEnergy
        exact (setLIntegral_congr_fun measurableSet_Ioi hpt).symm

/-- **Logarithmic Lévy coercivity from a mass floor and low-frequency exclusion.** If
`∫ g² ≥ A E` and `‖ĝ(t)‖² ≤ (2D²/M) E` for `|t| ≤ πM` (`M ≥ 2`), then
`Lévy(g) ≥ e^{-1/2} (A/2) (log M - 3 - log(1/η)) E` with `η = η(A, D)`. -/
theorem ofReal_le_sourceLevyEnergy {g : ℝ → ℝ} (hg : AdmissibleSource g) {A D E : ℝ} (hA : 0 < A)
    (hD : 0 < D) (hE : 0 ≤ E) {M : ℕ} (hM : 2 ≤ M) (hmass : A * E ≤ ∫ y, g y ^ 2)
    (hlow : ∀ t, |t| ≤ Real.pi * M → levySourceSpectralDensity g t ≤ 2 * D ^ 2 / M * E) :
    ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ)) * (A / 2) *
      (Real.log M - (3 + Real.log (1 / lowFreqRelativeCutoff A D))) * E) ≤ sourceLevyEnergy g := by
  set η := lowFreqRelativeCutoff A D
  have hη : 0 < η := lowFreqRelativeCutoff_pos hA hD
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  set R := η * M
  have hRpos : 0 < R := mul_pos hη hMpos
  have hlogR : Real.log M - (3 + Real.log (1 / η)) = Real.log R - 3 := by
    rw [Real.log_mul hη.ne' hMpos.ne', one_div, Real.log_inv]; ring
  rw [hlogR]
  have hs : 0 < Real.exp (-(1 / 2 : ℝ)) * (A / 2) := by positivity
  rcases le_or_gt (Real.log R - 3) 0 with hneg | hpos
  · rw [ENNReal.ofReal_of_nonpos]
    · exact zero_le
    · have : Real.exp (-(1 / 2 : ℝ)) * (A / 2) * (Real.log R - 3) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hs.le hneg
      nlinarith
  have hR1 : 1 ≤ R := by
    by_contra h
    have := Real.log_nonpos hRpos.le (not_le.mp h).le
    linarith
  have hhigh := sourceLevyEnergy_ge_highBand hg hR1
  have hmi := integrable_levySourceSpectralDensity hg
  have hlowband : 1 / (2 * Real.pi) * ∫ t in Icc (-R) R, levySourceSpectralDensity g t ≤ A / 2 * E := by
    have hpt : ∀ t ∈ Icc (-R) R, levySourceSpectralDensity g t ≤ 2 * D ^ 2 / M * E := by
      intro t ht
      refine hlow t ?_
      have hηπ : η ≤ Real.pi := (min_le_right _ _).trans (min_le_left _ _)
      calc |t| ≤ R := abs_le.mpr ht
        _ ≤ Real.pi * M := mul_le_mul_of_nonneg_right hηπ hMpos.le
    have hint : (∫ t in Icc (-R) R, levySourceSpectralDensity g t) ≤ (2 * R) * (2 * D ^ 2 / M * E) := by
      calc (∫ t in Icc (-R) R, levySourceSpectralDensity g t) ≤ ∫ _t in Icc (-R) R, 2 * D ^ 2 / M * E :=
            setIntegral_mono_on hmi.integrableOn (integrableOn_const (by simp)) measurableSet_Icc hpt
        _ = (2 * R) * (2 * D ^ 2 / M * E) := by
            rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
            ring
    have hpi : 0 < 1 / (2 * Real.pi) := by positivity
    calc 1 / (2 * Real.pi) * (∫ t in Icc (-R) R, levySourceSpectralDensity g t) ≤
          1 / (2 * Real.pi) * ((2 * R) * (2 * D ^ 2 / M * E)) := mul_le_mul_of_nonneg_left hint hpi.le
      _ = (1 / (2 * Real.pi)) * (2 * η * (M : ℝ)) * (2 * D ^ 2 * E / (M : ℝ)) := by ring
      _ ≤ (A / 2) * E := low_band_plancherel_energy_le_half_arch hD hE hM
  have htot := integral_levySourceSpectralDensity hg
  have hsplit := integral_add_compl (measurableSet_Icc (a := -R) (b := R)) hmi
  have hhighmass : A / 2 * E ≤ 1 / (2 * Real.pi) * ∫ t in (Icc (-R) R)ᶜ, levySourceSpectralDensity g t := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have h1 : 1 / (2 * Real.pi) * ∫ t, levySourceSpectralDensity g t = ∫ y, g y ^ 2 := by
      rw [htot]; field_simp
    rw [← hsplit, mul_add] at h1
    linarith
  refine le_trans ?_ hhigh
  have hc0 : 0 ≤ Real.exp (-(1 / 2 : ℝ)) * (Real.log R - 3) := by positivity
  rw [show Real.exp (-(1 / 2 : ℝ)) * (A / 2) * (Real.log R - 3) * E =
      (Real.exp (-(1 / 2 : ℝ)) * (Real.log R - 3)) * (A / 2 * E) by ring, ENNReal.ofReal_mul hc0]
  gcongr

/-! ### Nonstationary phase with a flat amplitude -/

/-- **Nonstationary phase with a flat amplitude.** If `a` is differentiable on `[1, ∞)`, vanishes
at `1` and at infinity, and `a, a', a/v²` are integrable on `(1, ∞)`, then for `ω ≠ 0`,
`|t| ≤ |ω|/2`: `‖∫_{v>1} a(v) e^{i(ωv - t log v)} dv‖ ≤ (2/|ω|)(‖a'‖₁ + ‖a/v²‖₁)`. One integration
by parts against `e^{iφ}/(iφ')` has no boundary terms. -/
theorem norm_integral_Ioi_one_flat_mul_cexp_phase_le {a a' : ℝ → ℝ}
    (ha : ∀ v ∈ Ici (1 : ℝ), HasDerivAt a (a' v) v) (ha1 : a 1 = 0) (hat : Tendsto a atTop (𝓝 0))
    (hai : IntegrableOn a (Ioi 1)) (hai' : IntegrableOn a' (Ioi 1))
    (haw : IntegrableOn (fun v => a v / v ^ 2) (Ioi 1)) {ω t : ℝ} (hω : ω ≠ 0) (ht : |t| ≤ |ω| / 2) :
    IntegrableOn (fun v : ℝ => (a v : ℂ) *
        Complex.exp (Complex.I * ((ω * v - t * Real.log v : ℝ) : ℂ))) (Ioi 1) ∧
    ‖∫ v in Ioi 1, (a v : ℂ) * Complex.exp (Complex.I * ((ω * v - t * Real.log v : ℝ) : ℂ))‖ ≤
      2 / |ω| * ((∫ v in Ioi 1, |a' v|) + ∫ v in Ioi 1, |a v / v ^ 2|) := by
  have hω0 : 0 < |ω| := abs_pos.mpr hω
  set D : ℝ → ℂ := fun v => Complex.I * ((ω - t / v : ℝ) : ℂ)
  set V : ℝ → ℂ := fun v => Complex.exp (Complex.I * ((ω * v - t * Real.log v : ℝ) : ℂ))
  set u : ℝ → ℂ := fun v => (a v : ℂ) / D v
  set u' : ℝ → ℂ := fun v => (a' v : ℂ) / D v -
    (a v : ℂ) * (Complex.I * ((t / v ^ 2 : ℝ) : ℂ)) / D v ^ 2
  have hDn {v : ℝ} (hv : 1 ≤ v) : |ω| / 2 ≤ ‖D v‖ := by
    simp only [D, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |t / v| ≤ |t| := by
      rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < v)]
      exact div_le_self (abs_nonneg _) hv
    have := abs_sub_abs_le_abs_sub ω (t / v)
    linarith
  have hD0 {v : ℝ} (hv : 1 ≤ v) : D v ≠ 0 := fun h => by
    have := hDn hv; rw [h, norm_zero] at this; linarith
  have hVn (v : ℝ) : ‖V v‖ = 1 := Complex.norm_exp_I_mul_ofReal _
  have hV (v : ℝ) (hv : 0 < v) : HasDerivAt V (D v * V v) v := by
    have hp : HasDerivAt (fun y => ω * y - t * Real.log y) (ω * 1 - t * v⁻¹) v :=
      ((hasDerivAt_id v).const_mul ω).sub ((Real.hasDerivAt_log hv.ne').const_mul t)
    have := ((hp.ofReal_comp).const_mul Complex.I).cexp
    refine this.congr_deriv ?_
    simp only [D, V]
    push_cast
    ring
  have hu (v : ℝ) (hv : 1 ≤ v) : HasDerivAt u (u' v) v := by
    have hv0 : v ≠ 0 := by positivity
    have hq : HasDerivAt (fun y => ω - t / y) (t / v ^ 2) v := by
      have := (hasDerivAt_const v ω).sub ((hasDerivAt_inv hv0).const_mul t)
      refine (this.congr_deriv (by field_simp; ring)).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
      simp [div_eq_mul_inv]
    have hd : HasDerivAt D (Complex.I * ((t / v ^ 2 : ℝ) : ℂ)) v := (hq.ofReal_comp).const_mul _
    have := ((ha v hv).ofReal_comp).div hd (hD0 hv)
    refine this.congr_deriv ?_
    simp only [u']
    have := hD0 hv
    field_simp
  have hbound {v : ℝ} (hv : 1 ≤ v) : ‖u' v‖ ≤ 2 / |ω| * (|a' v| + |a v / v ^ 2|) := by
    have hv0 : 0 < v := by linarith
    have hDv := hDn hv
    have hDp : 0 < ‖D v‖ := by linarith
    have e1 : ‖(a' v : ℂ) / D v‖ = |a' v| / ‖D v‖ := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    have e2 : ‖(a v : ℂ) * (Complex.I * ((t / v ^ 2 : ℝ) : ℂ)) / D v ^ 2‖ =
        |a v| * (|t| / v ^ 2) / ‖D v‖ ^ 2 := by
      rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_I, one_mul, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_div,
        abs_of_pos (by positivity : (0 : ℝ) < v ^ 2)]
    show ‖(a' v : ℂ) / D v - (a v : ℂ) * (Complex.I * ((t / v ^ 2 : ℝ) : ℂ)) / D v ^ 2‖ ≤ _
    refine (norm_sub_le _ _).trans ?_
    rw [e1, e2, abs_div, abs_of_pos (by positivity : (0 : ℝ) < v ^ 2)]
    have h1 : |a' v| / ‖D v‖ ≤ 2 / |ω| * |a' v| := by
      rw [div_le_iff₀ hDp]
      calc |a' v| = 2 / |ω| * |a' v| * (|ω| / 2) := by field_simp
        _ ≤ 2 / |ω| * |a' v| * ‖D v‖ := by gcongr
    have h2 : |a v| * (|t| / v ^ 2) / ‖D v‖ ^ 2 ≤ 2 / |ω| * (|a v| / v ^ 2) := by
      rw [div_le_iff₀ (by positivity)]
      have hsq : (|ω| / 2) ^ 2 ≤ ‖D v‖ ^ 2 := pow_le_pow_left₀ (by positivity) hDv 2
      calc |a v| * (|t| / v ^ 2) ≤ |a v| * (|ω| / 2 / v ^ 2) := by gcongr
        _ = 2 / |ω| * (|a v| / v ^ 2) * (|ω| / 2) ^ 2 := by field_simp
        _ ≤ 2 / |ω| * (|a v| / v ^ 2) * ‖D v‖ ^ 2 := by gcongr
    linarith
  -- measurability of the pieces on `(1, ∞)`
  have hcD : ContinuousOn D (Ioi 1) := by
    refine continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn ?_)
    exact continuousOn_const.sub (continuousOn_const.div continuousOn_id fun v hv => by
      simp only [mem_Ioi] at hv; positivity)
  have hcV : ContinuousOn V (Ioi 1) := fun v hv =>
    (hV v (lt_trans one_pos hv)).continuousAt.continuousWithinAt
  have hmD := hcD.aestronglyMeasurable (μ := volume) measurableSet_Ioi
  have hmV := hcV.aestronglyMeasurable (μ := volume) measurableSet_Ioi
  have hmT : AEStronglyMeasurable (fun v : ℝ => Complex.I * ((t / v ^ 2 : ℝ) : ℂ))
      (volume.restrict (Ioi 1)) := (by fun_prop : Measurable fun v : ℝ =>
        Complex.I * ((t / v ^ 2 : ℝ) : ℂ)).aestronglyMeasurable
  have hIaV : IntegrableOn (fun v => (a v : ℂ) * V v) (Ioi 1) := by
    refine hai.abs.mono' ((hai.ofReal (𝕜 := ℂ)).aestronglyMeasurable.mul hmV)
      (Eventually.of_forall fun v => ?_)
    rw [norm_mul, hVn, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hIu'V : IntegrableOn (u' * V) (Ioi 1) := by
    refine ((hai'.abs.add haw.abs).const_mul (2 / |ω|)).mono'
      ((((hai'.ofReal (𝕜 := ℂ)).aestronglyMeasurable.div₀ hmD).sub
        (((hai.ofReal (𝕜 := ℂ)).aestronglyMeasurable.mul hmT).div₀ (hmD.pow 2))).mul hmV) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [Pi.mul_apply, norm_mul, hVn, mul_one]
    exact hbound (le_of_lt hv)
  have hIuV' : IntegrableOn (u * fun v => D v * V v) (Ioi 1) := by
    refine hIaV.congr_fun (fun v hv => ?_) measurableSet_Ioi
    have := hD0 (le_of_lt (mem_Ioi.mp hv))
    simp only [Pi.mul_apply, u]
    field_simp
  have hzero : Tendsto (u * V) (𝓝[>] 1) (𝓝 0) := by
    have h := ((hu 1 le_rfl).continuousAt.mul (hV 1 one_pos).continuousAt).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 1))
    have h0 : (u * V) 1 = 0 := by simp [u, ha1]
    rwa [h0] at h
  have hinf : Tendsto (u * V) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun v => 2 / |ω| * ‖a v‖) atTop (𝓝 0) := by
      simpa using hat.norm.const_mul (2 / |ω|)
    refine squeeze_zero' (Eventually.of_forall fun v => norm_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with v hv
    rw [Pi.mul_apply, norm_mul, hVn, mul_one, norm_div, Complex.norm_real, div_le_iff₀
      (by linarith [hDn hv] : 0 < ‖D v‖)]
    calc ‖a v‖ = 2 / |ω| * ‖a v‖ * (|ω| / 2) := by field_simp
      _ ≤ 2 / |ω| * ‖a v‖ * ‖D v‖ := by gcongr; exact hDn hv
  have e := integral_Ioi_mul_deriv_eq_deriv_mul (u := u) (v := V) (u' := u')
    (v' := fun v => D v * V v) (a' := 0) (b' := 0) (fun x hx => hu x (le_of_lt hx))
    (fun x hx => hV x (lt_trans one_pos hx)) hIuV' hIu'V hzero hinf
  have hLHS : ∫ v in Ioi 1, u v * (D v * V v) = ∫ v in Ioi 1, (a v : ℂ) * V v := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
    have := hD0 (le_of_lt (mem_Ioi.mp hv))
    simp only [u]
    field_simp
  refine ⟨hIaV, ?_⟩
  change ‖∫ v in Ioi 1, (a v : ℂ) * V v‖ ≤ _
  rw [← hLHS, e, sub_self, zero_sub, norm_neg, ← integral_add hai'.abs haw.abs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((hai'.abs.add haw.abs).const_mul _) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [norm_mul, hVn, mul_one]
  exact hbound (le_of_lt hv)

/-! ### The collar Mellin amplitude -/

/-- **Collar Mellin amplitude** `a_c(v) = σ(v - 1) v^{-3/2}`: the Mellin weight of the collared
critical source. It vanishes on `v ≤ 1` and equals `v^{-3/2}` on `v ≥ 2`. -/
def criticalCollarAmplitude (v : ℝ) : ℝ := Real.smoothTransition (v - 1) * v ^ (-(3 / 2 : ℝ))

theorem criticalCollarAmplitude_eq_zero {x : ℝ} (hx : x ≤ 1) : criticalCollarAmplitude x = 0 := by
  rw [criticalCollarAmplitude, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

theorem criticalCollarAmplitude_eq_of_two_le {x : ℝ} (hx : 2 ≤ x) :
    criticalCollarAmplitude x = 1 * x ^ (-(3 / 2 : ℝ)) := by
  rw [criticalCollarAmplitude, Real.smoothTransition.one_of_one_le (by linarith)]

theorem abs_criticalCollarAmplitude_le {x : ℝ} (hx : 0 < x) :
    |criticalCollarAmplitude x| ≤ x ^ (-(3 / 2 : ℝ)) := by
  rw [criticalCollarAmplitude, abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg _),
    abs_of_pos (Real.rpow_pos_of_pos hx _)]
  exact mul_le_of_le_one_left (Real.rpow_pos_of_pos hx _).le (Real.smoothTransition.le_one _)

theorem contDiff_criticalCollarAmplitude : ContDiff ℝ (⊤ : ℕ∞) criticalCollarAmplitude := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  rcases lt_or_ge x 1 with hx | hx
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact criticalCollarAmplitude_eq_zero (le_of_lt hy)
  · exact (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt.mul
      (Real.contDiffAt_rpow_const_of_ne (by positivity))

theorem contDiff_deriv_criticalCollarAmplitude :
    ContDiff ℝ (⊤ : ℕ∞) (deriv criticalCollarAmplitude) :=
  (contDiff_infty_iff_deriv.mp contDiff_criticalCollarAmplitude).2

theorem hasDerivAt_criticalCollarAmplitude (x : ℝ) :
    HasDerivAt criticalCollarAmplitude (deriv criticalCollarAmplitude x) x :=
  ((contDiff_infty_iff_deriv.mp contDiff_criticalCollarAmplitude).1 x).hasDerivAt

theorem deriv_criticalCollarAmplitude_of_two_lt {x : ℝ} (hx : 2 < x) :
    deriv criticalCollarAmplitude x = -(3 / 2) * x ^ (-(3 / 2 : ℝ) - 1) := by
  have he : criticalCollarAmplitude =ᶠ[𝓝 x] fun y => y ^ (-(3 / 2 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [criticalCollarAmplitude_eq_of_two_le (le_of_lt hy), one_mul]
  rw [he.deriv_eq, (Real.hasDerivAt_rpow_const (Or.inl (by positivity))).deriv]

private theorem integrableOn_Ioi_one_of_eq_rpow {g : ℝ → ℝ} (hg : Continuous g) (p : ℝ) (hp : p < -1)
    (c : ℝ) (heq : ∀ x, 2 < x → g x = c * x ^ p) : IntegrableOn g (Ioi 1) := by
  rw [← Ioc_union_Ioi_eq_Ioi one_le_two]
  refine (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self).union ?_
  exact IntegrableOn.congr_fun ((integrableOn_Ioi_rpow_of_lt hp two_pos).const_mul c)
    (fun x hx => (heq x hx).symm) measurableSet_Ioi

theorem integrableOn_criticalCollarAmplitude : IntegrableOn criticalCollarAmplitude (Ioi 1) :=
  integrableOn_Ioi_one_of_eq_rpow contDiff_criticalCollarAmplitude.continuous _ (by norm_num) 1
    fun _ hx => criticalCollarAmplitude_eq_of_two_le (le_of_lt hx)

theorem integrableOn_deriv_criticalCollarAmplitude :
    IntegrableOn (deriv criticalCollarAmplitude) (Ioi 1) :=
  integrableOn_Ioi_one_of_eq_rpow contDiff_deriv_criticalCollarAmplitude.continuous _ (by norm_num)
    (-(3 / 2)) fun _ hx => deriv_criticalCollarAmplitude_of_two_lt hx

theorem integrableOn_criticalCollarAmplitude_div_sq :
    IntegrableOn (fun v => criticalCollarAmplitude v / v ^ 2) (Ioi 1) := by
  refine integrableOn_criticalCollarAmplitude.abs.mono'
    ((integrableOn_criticalCollarAmplitude.aemeasurable.div
      (measurable_id.pow_const 2).aemeasurable).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv1 : (1 : ℝ) ≤ v ^ 2 := by nlinarith [mem_Ioi.mp hv]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < v ^ 2)]
  exact div_le_self (abs_nonneg _) hv1

theorem tendsto_criticalCollarAmplitude_atTop : Tendsto criticalCollarAmplitude atTop (𝓝 0) := by
  refine (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  rw [criticalCollarAmplitude_eq_of_two_le hx, one_mul]

/-- Phase constant `2(‖a_c'‖₁ + ‖a_c/v²‖₁)` of the collar amplitude. -/
def criticalCollarPhaseConstant : ℝ :=
  2 * ((∫ v in Ioi 1, |deriv criticalCollarAmplitude v|) +
    ∫ v in Ioi 1, |criticalCollarAmplitude v / v ^ 2|)

theorem criticalCollarPhaseConstant_nonneg : 0 ≤ criticalCollarPhaseConstant := by
  unfold criticalCollarPhaseConstant
  have h1 : 0 ≤ ∫ v in Ioi 1, |deriv criticalCollarAmplitude v| := integral_nonneg fun _ => abs_nonneg _
  have h2 : 0 ≤ ∫ v in Ioi 1, |criticalCollarAmplitude v / v ^ 2| :=
    integral_nonneg fun _ => abs_nonneg _
  positivity

/-- **Collared oscillatory bound.** For `θ ≠ 0` and `|t| ≤ |θ|/2`,
`‖∫_{v>1} a_c(v) cos(θv) e^{-it log v} dv‖ ≤ C_a/|θ|`. -/
theorem norm_integral_criticalCollarAmplitude_cos_le {θ t : ℝ} (hθ : θ ≠ 0) (ht : |t| ≤ |θ| / 2) :
    IntegrableOn (fun v : ℝ => ((criticalCollarAmplitude v * Real.cos (θ * v) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ)))) (Ioi 1) ∧
    ‖∫ v in Ioi (1 : ℝ), ((criticalCollarAmplitude v * Real.cos (θ * v) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ)))‖ ≤ criticalCollarPhaseConstant / |θ| := by
  set a := criticalCollarAmplitude
  have hθ' : -θ ≠ 0 := neg_ne_zero.mpr hθ
  have ht' : |t| ≤ |-θ| / 2 := by rwa [abs_neg]
  have hflat := @norm_integral_Ioi_one_flat_mul_cexp_phase_le a (deriv a)
    (fun v _ => hasDerivAt_criticalCollarAmplitude v) (criticalCollarAmplitude_eq_zero le_rfl)
    tendsto_criticalCollarAmplitude_atTop integrableOn_criticalCollarAmplitude
    integrableOn_deriv_criticalCollarAmplitude integrableOn_criticalCollarAmplitude_div_sq
  obtain ⟨hi1, hb1⟩ := hflat hθ ht
  obtain ⟨hi2, hb2⟩ := hflat hθ' ht'
  have hpt : ∀ v : ℝ, ((a v * Real.cos (θ * v) : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ))) =
      (1 / 2 : ℂ) * ((a v : ℂ) * Complex.exp (Complex.I * ((θ * v - t * Real.log v : ℝ) : ℂ))) +
      (1 / 2 : ℂ) * ((a v : ℂ) * Complex.exp (Complex.I * ((-θ * v - t * Real.log v : ℝ) : ℂ))) := by
    intro v
    rw [Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
    push_cast
    rw [show Complex.I * (↑θ * ↑v - ↑t * ↑(Real.log v)) =
        ↑θ * ↑v * Complex.I + -(Complex.I * (↑t * ↑(Real.log v))) by ring,
      show Complex.I * (-↑θ * ↑v - ↑t * ↑(Real.log v)) =
        -(↑θ * ↑v) * Complex.I + -(Complex.I * (↑t * ↑(Real.log v))) by ring,
      Complex.exp_add, Complex.exp_add]
    ring
  rw [funext hpt]
  refine ⟨(hi1.const_mul _).add (hi2.const_mul _), ?_⟩
  rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
  rw [abs_neg] at hb2
  have hC : criticalCollarPhaseConstant / |θ| =
      1 / 2 * (2 / |θ| * ((∫ v in Ioi 1, |deriv a v|) + ∫ v in Ioi 1, |a v / v ^ 2|)) +
      1 / 2 * (2 / |θ| * ((∫ v in Ioi 1, |deriv a v|) + ∫ v in Ioi 1, |a v / v ^ 2|)) := by
    unfold criticalCollarPhaseConstant; ring
  rw [hC]
  gcongr

/-- Collared critical Mellin kernel `a_c(v) e^{-it log v}`. -/
def criticalCollarMellinKernel (t v : ℝ) : ℂ :=
  (criticalCollarAmplitude v : ℂ) * Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ)))

theorem norm_criticalCollarMellinKernel_le {t v : ℝ} (hv : 0 < v) :
    ‖criticalCollarMellinKernel t v‖ ≤ v ^ (-3 / 2 : ℝ) := by
  unfold criticalCollarMellinKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h : -(Complex.I * ((t * Real.log v : ℝ) : ℂ)) = Complex.I * ((-(t * Real.log v) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h, Complex.norm_exp_I_mul_ofReal, mul_one, show (-3 / 2 : ℝ) = -(3 / 2) by norm_num]
  exact abs_criticalCollarAmplitude_le hv

/-- **Collared Mellin bound for one harmonic layer.** For `k ≥ 1` and `|t| ≤ π(n+1)` on the
support, `‖∫_1^∞ H_k(v) a_c(v) e^{-it log v} dv‖ ≤ ∑_n ‖b_n‖ C_a/(π k (n+1))`. -/
theorem norm_integral_factorialHarmonicLayer_criticalCollarMellinKernel_le (S : Finset ℕ)
    (b : ℕ → ℂ) {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : ∀ n ∈ S, |t| ≤ Real.pi * ((n + 1 : ℕ) : ℝ)) :
    IntegrableOn (fun v => factorialHarmonicLayer S b k v * criticalCollarMellinKernel t v) (Ioi 1) ∧
    ‖∫ v in Ioi (1 : ℝ), factorialHarmonicLayer S b k v * criticalCollarMellinKernel t v‖ ≤
      ∑ n ∈ S, ‖b n‖ * (criticalCollarPhaseConstant / (Real.pi * k * ((n + 1 : ℕ) : ℝ))) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set C := criticalCollarPhaseConstant
  have hC := criticalCollarPhaseConstant_nonneg
  set G : ℝ → ℝ → ℂ := fun θ v => ((criticalCollarAmplitude v * Real.cos (θ * v) : ℝ) : ℂ) *
    Complex.exp (-(Complex.I * ((t * Real.log v : ℝ) : ℂ))) with hG
  have hθ (n : ℕ) (hn : n ∈ S) {θ : ℝ} (hθ : 2 * Real.pi * k * ((n + 1 : ℕ) : ℝ) ≤ θ) :
      IntegrableOn (G θ) (Ioi 1) ∧ ‖∫ v in Ioi (1 : ℝ), G θ v‖ ≤
        C / (2 * Real.pi * k * ((n + 1 : ℕ) : ℝ)) := by
    have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hθ0 : 0 < θ := lt_of_lt_of_le (by positivity) hθ
    have htθ : |t| ≤ |θ| / 2 := by
      rw [abs_of_pos hθ0]
      have := ht n hn
      nlinarith [Real.pi_pos]
    obtain ⟨hi, hb⟩ := norm_integral_criticalCollarAmplitude_cos_le hθ0.ne' htθ
    refine ⟨hi, hb.trans ?_⟩
    rw [abs_of_pos hθ0]
    exact div_le_div_of_nonneg_left hC (by positivity) hθ
  have hlam (n : ℕ) : ((n + 1 : ℕ) : ℝ) ≤ factorialShiftedFreq (n + 1) := by
    have := (factorialShiftedFreq_sub_self_bounds (N := n + 1) (by omega)).1
    linarith
  have hpt : ∀ v, factorialHarmonicLayer S b k v * criticalCollarMellinKernel t v =
      ∑ n ∈ S, b n * (G (2 * Real.pi * k * factorialShiftedFreq (n + 1)) v -
        G (2 * Real.pi * k * ((n + 1 : ℕ) : ℝ)) v) := by
    intro v
    unfold factorialHarmonicLayer criticalCollarMellinKernel
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hG]
    rw [show 2 * Real.pi * k * factorialShiftedFreq (n + 1) * v =
        2 * Real.pi * k * (factorialShiftedFreq (n + 1) * v) by ring,
      show 2 * Real.pi * k * ((n + 1 : ℕ) : ℝ) * v =
        2 * Real.pi * k * (((n + 1 : ℕ) : ℝ) * v) by ring]
    push_cast
    ring
  have hint (n : ℕ) (hn : n ∈ S) : IntegrableOn (fun v => b n *
      (G (2 * Real.pi * k * factorialShiftedFreq (n + 1)) v -
        G (2 * Real.pi * k * ((n + 1 : ℕ) : ℝ)) v)) (Ioi 1) :=
    (((hθ n hn (mul_le_mul_of_nonneg_left (hlam n) (by positivity))).1).sub
      (hθ n hn le_rfl).1).const_mul _
  rw [funext hpt]
  refine ⟨integrable_finsetSum _ hint, ?_⟩
  rw [integral_finsetSum _ hint]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  obtain ⟨hiL, hbL⟩ := hθ n hn (mul_le_mul_of_nonneg_left (hlam n) (by positivity))
  obtain ⟨hiN, hbN⟩ := hθ n hn le_rfl
  rw [integral_const_mul, norm_mul, integral_sub hiL hiN]
  refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) (norm_nonneg _)
  have he : C / (2 * Real.pi * k * ((n + 1 : ℕ) : ℝ)) + C / (2 * Real.pi * k * ((n + 1 : ℕ) : ℝ)) =
      C / (Real.pi * k * ((n + 1 : ℕ) : ℝ)) := by
    field_simp
    ring
  linarith

/-! ### Low-frequency exclusion for the collared critical source -/

/-- **Mellin readout of a collared critical source.**
`ĝ_c(t) = ∫_1^∞ B_b(v) a_c(v) e^{-it log v} dv`. -/
theorem paperFT_criticalCollaredSource (S : Finset ℕ) (b : ℕ → ℝ) (t : ℝ) :
    paperFT (fun x => (criticalCollaredSource S b x : ℂ)) t =
      ∫ v in Ioi (1 : ℝ), factorialPhaseCombination S (fun n => (b n : ℂ)) v *
        criticalCollarMellinKernel t v := by
  set B := factorialPhaseCombination S (fun n => (b n : ℂ)) with hB
  have h1 : paperFT (fun x => (criticalCollaredSource S b x : ℂ)) t = ∫ y in Iic (0 : ℝ),
      ((Real.smoothTransition (Real.exp (-y) - 1) * Real.exp (y / 2) : ℝ) : ℂ) * B (Real.exp (-y)) *
        Complex.exp (Complex.I * (t : ℂ) * (y : ℂ)) := by
    unfold paperFT
    rw [← integral_indicator measurableSet_Iic]
    congr 1
    funext y
    by_cases hy : y ≤ 0
    · simp only [criticalCollaredSource, criticalFactorialSource,
        indicator_of_mem (show y ∈ Iic 0 from hy)]
      rw [Complex.ofReal_mul, Complex.ofReal_mul, factorialPhaseCombination_ofReal_re]
      push_cast
      ring
    · simp only [criticalCollaredSource, criticalFactorialSource,
        indicator_of_notMem (show y ∉ Iic 0 from hy), mul_zero, Complex.ofReal_zero, zero_mul]
  have h2 : (∫ y in Iic (0 : ℝ),
      ((Real.smoothTransition (Real.exp (-y) - 1) * Real.exp (y / 2) : ℝ) : ℂ) * B (Real.exp (-y)) *
        Complex.exp (Complex.I * (t : ℂ) * (y : ℂ))) =
      ∫ y in Ioi (0 : ℝ), ((Real.smoothTransition (Real.exp y - 1) * Real.exp (-y / 2) : ℝ) : ℂ) *
        B (Real.exp y) * Complex.exp (-(Complex.I * ((t * y : ℝ) : ℂ))) := by
    have h := integral_comp_neg_Iic (0 : ℝ) (fun y : ℝ =>
      ((Real.smoothTransition (Real.exp y - 1) * Real.exp (-y / 2) : ℝ) : ℂ) *
        B (Real.exp y) * Complex.exp (-(Complex.I * ((t * y : ℝ) : ℂ))))
    simp only [neg_zero] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Iic fun y _ => ?_
    rw [show -(-y) / 2 = y / 2 by ring,
      show (-(Complex.I * ((t * -y : ℝ) : ℂ))) = Complex.I * (t : ℂ) * (y : ℂ) by push_cast; ring]
  have h3 := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) (f := Real.exp)
    (f' := Real.exp) measurableSet_Ioi (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt)
    Real.exp_injective.injOn (fun v => B v * criticalCollarMellinKernel t v)
  rw [Real.image_exp_Ioi, Real.exp_zero] at h3
  rw [h1, h2, h3]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [abs_of_pos (Real.exp_pos y), Complex.real_smul]
  unfold criticalCollarMellinKernel criticalCollarAmplitude
  rw [Real.log_exp, ← Real.exp_mul]
  have he : Real.exp y * Real.exp (y * -(3 / 2)) = Real.exp (-y / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← he]
  push_cast
  ring

/-- Low-frequency constant `D_c = 3 (C_a + 1)/π³` of the collared source. -/
def criticalCollarLowFreqConstant : ℝ := 3 * (criticalCollarPhaseConstant + 1) / Real.pi ^ 3

theorem criticalCollarLowFreqConstant_pos : 0 < criticalCollarLowFreqConstant := by
  unfold criticalCollarLowFreqConstant
  have := criticalCollarPhaseConstant_nonneg
  positivity

/-- **Low-frequency Mellin bound of a collared source.** If `|t| ≤ π(n+1)` on the support,
`‖ĝ_c(t)‖ ≤ D_c ∑_n |b_n|/(n+1)`. -/
theorem norm_paperFT_criticalCollaredSource_le (S : Finset ℕ) (b : ℕ → ℝ) {t : ℝ}
    (ht : ∀ n ∈ S, |t| ≤ Real.pi * ((n + 1 : ℕ) : ℝ)) :
    ‖paperFT (fun x => (criticalCollaredSource S b x : ℂ)) t‖ ≤
      criticalCollarLowFreqConstant * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ) := by
  set bc : ℕ → ℂ := fun n => (b n : ℂ) with hbc
  set C := criticalCollarPhaseConstant
  have hC := criticalCollarPhaseConstant_nonneg
  set T := ∑ n ∈ S, ‖bc n‖ / ((n + 1 : ℕ) : ℝ) with hT
  have hTeq : T = ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ) := by
    simp only [hT, hbc, Complex.norm_real, Real.norm_eq_abs]
  rw [← hTeq]
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun n _ => by positivity
  set Cb := 2 * ∑ n ∈ S, ‖bc n‖ with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  set c : ℂ := -((2 / Real.pi ^ 2 : ℝ) : ℂ) with hc
  set F : ℕ → ℝ → ℂ := fun k v => c * (dyadicHarmonicWeight k : ℂ) *
    (factorialHarmonicLayer S bc k v * criticalCollarMellinKernel t v) with hF
  have hreadout : paperFT (fun x => (criticalCollaredSource S b x : ℂ)) t =
      ∫ v in Ioi (1 : ℝ), ∑' k, F k v := by
    rw [paperFT_criticalCollaredSource]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    rw [factorialPhaseCombination_eq_tsum, ← hc]
    simp only [hF]
    rw [show (c * ∑' k, (dyadicHarmonicWeight k : ℂ) * factorialHarmonicLayer S bc k v) *
        criticalCollarMellinKernel t v
        = (∑' k, (dyadicHarmonicWeight k : ℂ) * factorialHarmonicLayer S bc k v) *
          (c * criticalCollarMellinKernel t v) by ring, ← tsum_mul_right]
    refine tsum_congr fun k => ?_
    ring
  have hFk (k : ℕ) : IntegrableOn (F k) (Ioi 1) ∧ ‖∫ v in Ioi (1 : ℝ), F k v‖ ≤
      2 * C / Real.pi ^ 3 * (1 / (k : ℝ) ^ 3) * T := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hF, dyadicHarmonicWeight_zero]
    obtain ⟨hi, hb⟩ := norm_integral_factorialHarmonicLayer_criticalCollarMellinKernel_le S bc hk ht
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    refine ⟨hi.const_mul _, ?_⟩
    simp only [hF]
    rw [integral_const_mul, norm_mul, norm_mul, hc, norm_neg, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]
    have hw := abs_dyadicHarmonicWeight_le k
    have hsum : (∑ n ∈ S, ‖bc n‖ * (C / (Real.pi * k * ((n + 1 : ℕ) : ℝ)))) = C / (Real.pi * k) * T := by
      rw [hT, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      field_simp
    rw [hsum] at hb
    calc 2 / Real.pi ^ 2 * |dyadicHarmonicWeight k| *
          ‖∫ v in Ioi (1 : ℝ), factorialHarmonicLayer S bc k v * criticalCollarMellinKernel t v‖ ≤
          2 / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2) * (C / (Real.pi * k) * T) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hw (by positivity)) hb (norm_nonneg _)
            (by positivity)
      _ = 2 * C / Real.pi ^ 3 * (1 / (k : ℝ) ^ 3) * T := by
          field_simp
  have hmeas (k : ℕ) := (hFk k).1
  have hw32 : IntegrableOn (fun v : ℝ => v ^ (-3 / 2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hnormint (k : ℕ) : (∫ v in Ioi (1 : ℝ), ‖F k v‖) ≤
      2 / Real.pi ^ 2 * |dyadicHarmonicWeight k| * Cb * 2 := by
    calc (∫ v in Ioi (1 : ℝ), ‖F k v‖) ≤
          ∫ v in Ioi (1 : ℝ), 2 / Real.pi ^ 2 * |dyadicHarmonicWeight k| * Cb * v ^ (-3 / 2 : ℝ) := by
          refine setIntegral_mono_on (hmeas k).norm (hw32.const_mul _)
            measurableSet_Ioi fun v hv => ?_
          have hv0 : 0 < v := lt_trans one_pos hv
          simp only [hF]
          rw [norm_mul, norm_mul, norm_mul, hc, norm_neg, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]
          have h1 := norm_factorialHarmonicLayer_le S bc k v
          have h2 := norm_criticalCollarMellinKernel_le (t := t) hv0
          calc 2 / Real.pi ^ 2 * |dyadicHarmonicWeight k| *
                (‖factorialHarmonicLayer S bc k v‖ * ‖criticalCollarMellinKernel t v‖) ≤
                2 / Real.pi ^ 2 * |dyadicHarmonicWeight k| * (Cb * v ^ (-3 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) hCb0) (by positivity)
            _ = _ := by ring
      _ = 2 / Real.pi ^ 2 * |dyadicHarmonicWeight k| * Cb * 2 := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
          norm_num
  have hsumm : Summable fun k => ∫ v in Ioi (1 : ℝ), ‖F k v‖ :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) hnormint
      ((summable_abs_dyadicHarmonicWeight.mul_left (2 / Real.pi ^ 2)).mul_right Cb |>.mul_right 2)
  rw [hreadout, ← integral_tsum_of_summable_integral_norm hmeas hsumm]
  have hb3 : Summable fun k : ℕ => 2 * C / Real.pi ^ 3 * (1 / (k : ℝ) ^ 3) * T :=
    ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3)).mul_left _).mul_right _
  have hs := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => (hFk k).2) hb3
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  calc (∑' k, ‖∫ v in Ioi (1 : ℝ), F k v‖) ≤ ∑' k : ℕ, 2 * C / Real.pi ^ 3 * (1 / (k : ℝ) ^ 3) * T :=
        hs.tsum_le_tsum (fun k => (hFk k).2) hb3
    _ = 2 * C / Real.pi ^ 3 * (∑' k : ℕ, 1 / (k : ℝ) ^ 3) * T := by
        rw [tsum_mul_right, tsum_mul_left]
    _ ≤ 2 * C / Real.pi ^ 3 * (3 / 2) * T := by
        gcongr
        exact tsum_one_div_nat_cube_le_three_halves
    _ ≤ criticalCollarLowFreqConstant * T := by
        unfold criticalCollarLowFreqConstant
        have : 2 * C / Real.pi ^ 3 * (3 / 2) ≤ 3 * (C + 1) / Real.pi ^ 3 := by
          rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
          linarith
        exact mul_le_mul_of_nonneg_right this hT0

/-- **Collared low-frequency exclusion.** For a family on `n + 1 ≥ M ≥ 2` and `|t| ≤ πM`,
`‖ĝ_c(t)‖² ≤ (2 D_c²/M) ∑ b_n²`. -/
theorem norm_sq_paperFT_criticalCollaredSource_le (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ}
    (hM : 2 ≤ M) (hS : ∀ n ∈ S, M ≤ n + 1) {t : ℝ} (ht : |t| ≤ Real.pi * M) :
    ‖paperFT (fun x => (criticalCollaredSource S b x : ℂ)) t‖ ^ 2 ≤
      2 * criticalCollarLowFreqConstant ^ 2 / M * ∑ n ∈ S, b n ^ 2 := by
  have ht' : ∀ n ∈ S, |t| ≤ Real.pi * ((n + 1 : ℕ) : ℝ) := fun n hn => ht.trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hS n hn) Real.pi_pos.le)
  have h1 := norm_paperFT_criticalCollaredSource_le S b ht'
  set D := criticalCollarLowFreqConstant
  have hD := criticalCollarLowFreqConstant_pos
  set T := ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun n _ => by positivity
  have hcs : T ^ 2 ≤ (∑ n ∈ S, b n ^ 2) * ∑ n ∈ S, (1 / ((n + 1 : ℕ) : ℝ)) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun n => |b n|) (fun n => 1 / ((n + 1 : ℕ) : ℝ))
    simpa only [hT, mul_one_div, sq_abs] using h
  have hinv : (∑ n ∈ S, (1 / ((n + 1 : ℕ) : ℝ)) ^ 2) ≤ 2 / (M : ℝ) := by
    have h := sum_low_freq_sq_le_two_mul_sq_div (S.map ⟨fun n => n + 1, add_left_injective 1⟩) hM
      (by simpa using hS) 1
    simpa [Finset.sum_map] using h
  have hE : 0 ≤ ∑ n ∈ S, b n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ‖paperFT (fun x => (criticalCollaredSource S b x : ℂ)) t‖ ^ 2 ≤ (D * T) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = D ^ 2 * T ^ 2 := by ring
    _ ≤ D ^ 2 * ((∑ n ∈ S, b n ^ 2) * (2 / (M : ℝ))) := by
        gcongr
        exact hcs.trans (mul_le_mul_of_nonneg_left hinv hE)
    _ = 2 * D ^ 2 / M * ∑ n ∈ S, b n ^ 2 := by ring

/-! ### Mass floor and logarithmic coercivity of the collared source -/

/-- A collared critical source is admissible. -/
theorem admissibleSource_criticalCollaredSource (S : Finset ℕ) (b : ℕ → ℝ) :
    AdmissibleSource (criticalCollaredSource S b) := by
  obtain ⟨h1, h2⟩ := integrable_criticalFactorialSource S b
  have hm : AEStronglyMeasurable (fun x => (criticalCollaredSource S b x : ℂ)) volume :=
    (Complex.measurable_ofReal.comp ((by fun_prop : Continuous fun x : ℝ =>
      Real.smoothTransition (Real.exp (-x) - 1)).measurable.mul
        (measurable_criticalFactorialSource S b))).aestronglyMeasurable
  have hle : ∀ᵐ x ∂volume, ‖(criticalCollaredSource S b x : ℂ)‖ ≤
      ‖(criticalFactorialSource S b x : ℂ)‖ := Eventually.of_forall fun x => by
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      criticalCollaredSource, abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.smoothTransition.le_one _)
  exact ⟨h1.norm.mono' hm (by simpa using hle), h2.of_le hm hle⟩

/-- Mass constant `A_c = L/(16π⁴(2 + L)²)` of the collared source. -/
def criticalCollarMassLower : ℝ :=
  factorialWindowLength / (16 * Real.pi ^ 4) / (2 + factorialWindowLength) ^ 2

theorem criticalCollarMassLower_pos : 0 < criticalCollarMassLower := by
  unfold criticalCollarMassLower
  have := factorialWindowLength_pos
  positivity

/-- **Collared energy in the dilation variable.**
`∫ g_c² = ∫_{v>1} σ(v - 1)² ‖B_b(v)‖² / v² dv`. -/
theorem integral_criticalCollaredSource_sq_eq (S : Finset ℕ) (b : ℕ → ℝ) :
    ∫ y, criticalCollaredSource S b y ^ 2 = ∫ v in Ioi 1, Real.smoothTransition (v - 1) ^ 2 *
      ‖factorialPhaseCombination S (fun n => (b n : ℂ)) v‖ ^ 2 / v ^ 2 := by
  set B := factorialPhaseCombination S (fun n => (b n : ℂ))
  set H : ℝ → ℝ := fun v => Real.smoothTransition (v - 1) ^ 2 * ‖B v‖ ^ 2
  have hBre (v : ℝ) : ‖B v‖ = |(B v).re| := by
    have h : ((B v).re : ℂ) = B v := factorialPhaseCombination_ofReal_re S b v
    rw [← h, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  have hpt : ∀ y, criticalCollaredSource S b y ^ 2 =
      (Iic (0 : ℝ)).indicator (fun y => Real.exp y * H (Real.exp (-y))) y := by
    intro y
    by_cases hy : y ≤ 0
    · rw [indicator_of_mem (show y ∈ Iic 0 from hy)]
      simp only [criticalCollaredSource, criticalFactorialSource,
        indicator_of_mem (show y ∈ Iic 0 from hy), H, hBre, sq_abs]
      have : Real.exp (y / 2) ^ 2 = Real.exp y := by rw [← Real.exp_nat_mul]; ring_nf
      rw [mul_pow, mul_pow, this]
      ring
    · rw [indicator_of_notMem (show y ∉ Iic 0 from hy)]
      simp [criticalCollaredSource, criticalFactorialSource,
        indicator_of_notMem (show y ∉ Iic 0 from hy)]
  rw [funext hpt, integral_indicator measurableSet_Iic, integral_Iic_zero_exp_mul_comp_exp_neg H]

/-- **Collared mass floor.** `∫ g_c² ≥ A_c ∑ b_n²`: the window `[2, 2 + L]` lies beyond the
collar and carries the Riesz floor of the phases. -/
theorem integral_criticalCollaredSource_sq_ge (S : Finset ℕ) (b : ℕ → ℝ) :
    criticalCollarMassLower * ∑ n ∈ S, b n ^ 2 ≤ ∫ y, criticalCollaredSource S b y ^ 2 := by
  set B := factorialPhaseCombination S (fun n => (b n : ℂ))
  set L := factorialWindowLength
  have hL := factorialWindowLength_pos
  set H : ℝ → ℝ := fun v => Real.smoothTransition (v - 1) ^ 2 * ‖B v‖ ^ 2
  have hcB : Continuous fun v => ‖B v‖ ^ 2 :=
    ((continuous_factorialPhaseCombination S _).norm).pow 2
  have hBb (v : ℝ) : ‖B v‖ ^ 2 ≤ (2 * ∑ n ∈ S, |b n|) ^ 2 := by
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    nlinarith [abs_factorialPhaseProfile_le (n + 1) v, abs_nonneg (b n)]
  have hHint : IntegrableOn (fun v => H v / v ^ 2) (Ioi 1) := by
    have hw : IntegrableOn (fun v : ℝ => (2 * ∑ n ∈ S, |b n|) ^ 2 * v ^ (-2 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul _
    refine hw.mono' (((by fun_prop : Continuous fun v => Real.smoothTransition (v - 1) ^ 2).mul
      hcB).aestronglyMeasurable.div₀ (measurable_id.pow_const 2).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := lt_trans one_pos hv
    have hσ : Real.smoothTransition (v - 1) ^ 2 ≤ 1 :=
      pow_le_one₀ (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg hv0.le,
      Real.rpow_two, ← div_eq_mul_inv]
    gcongr
    calc H v ≤ 1 * (2 * ∑ n ∈ S, |b n|) ^ 2 := by
          simp only [H]; exact mul_le_mul hσ (hBb v) (by positivity) zero_le_one
      _ = _ := one_mul _
  have hfloor : L / (16 * Real.pi ^ 4) * ∑ n ∈ S, b n ^ 2 ≤ ∫ v in Ioc 2 (2 + L), ‖B v‖ ^ 2 := by
    have h := factorialPhaseCombination_window_lower S (fun n => (b n : ℂ)) 2
    rw [intervalIntegral.integral_of_le (by linarith)] at h
    simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using h
  have hwin : (∫ v in Ioc 2 (2 + L), ‖B v‖ ^ 2) / (2 + L) ^ 2 ≤ ∫ v in Ioc 2 (2 + L), H v / v ^ 2 := by
    rw [← integral_div]
    refine setIntegral_mono_on (hcB.integrableOn_Icc.mono_set Ioc_subset_Icc_self |>.div_const _)
      (hHint.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi one_le_two)))
      measurableSet_Ioc fun v hv => ?_
    have hv2 : 2 < v := hv.1
    have hσ : Real.smoothTransition (v - 1) = 1 := Real.smoothTransition.one_of_one_le (by linarith)
    simp only [H, hσ, one_pow, one_mul]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (pow_le_pow_left₀ (by linarith) hv.2 2)
  have hsub : (∫ v in Ioc 2 (2 + L), H v / v ^ 2) ≤ ∫ v in Ioi 1, H v / v ^ 2 :=
    setIntegral_mono_set hHint (Eventually.of_forall fun v => by simp only [H]; positivity)
      (Eventually.of_forall (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi one_le_two)))
  rw [integral_criticalCollaredSource_sq_eq]
  unfold criticalCollarMassLower
  calc L / (16 * Real.pi ^ 4) / (2 + L) ^ 2 * ∑ n ∈ S, b n ^ 2 =
        (L / (16 * Real.pi ^ 4) * ∑ n ∈ S, b n ^ 2) / (2 + L) ^ 2 := by ring
    _ ≤ (∫ v in Ioc 2 (2 + L), ‖B v‖ ^ 2) / (2 + L) ^ 2 := by gcongr
    _ ≤ _ := hwin.trans hsub

/-- Slope `e^{-1/2} A_c/2` of the collared logarithmic law. -/
def criticalCollarArchLogSlope : ℝ := Real.exp (-(1 / 2 : ℝ)) * (criticalCollarMassLower / 2)

/-- Offset `3 + log(1/η(A_c, D_c))` of the collared logarithmic law. -/
def criticalCollarArchLogOffset : ℝ :=
  3 + Real.log (1 / lowFreqRelativeCutoff criticalCollarMassLower criticalCollarLowFreqConstant)

theorem criticalCollarArchLogSlope_pos : 0 < criticalCollarArchLogSlope := by
  unfold criticalCollarArchLogSlope
  have := criticalCollarMassLower_pos
  positivity

/-- **Collared archimedean log-coercivity.** For every finite family on scales
`n + 1 ≥ M ≥ 2` and every real coefficient vector,
`Lévy(g_c) ≥ s_c (log M - c_c) ∑ b_n²`. -/
theorem ofReal_le_criticalCollaredLevyEnergy (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ} (hM : 2 ≤ M)
    (hS : ∀ n ∈ S, M ≤ n + 1) :
    ENNReal.ofReal (criticalCollarArchLogSlope * (Real.log M - criticalCollarArchLogOffset) *
      ∑ n ∈ S, b n ^ 2) ≤ sourceLevyEnergy (criticalCollaredSource S b) := by
  have h := ofReal_le_sourceLevyEnergy (admissibleSource_criticalCollaredSource S b)
    criticalCollarMassLower_pos criticalCollarLowFreqConstant_pos
    (Finset.sum_nonneg fun n _ => sq_nonneg (b n)) hM (integral_criticalCollaredSource_sq_ge S b)
    (fun t ht => norm_sq_paperFT_criticalCollaredSource_le S b hM hS ht)
  unfold criticalCollarArchLogSlope criticalCollarArchLogOffset
  exact h

/-! ### The collared Lévy–prime form on dyadic blocks -/

/-- **Collared Lévy–prime coercivity.** On every dyadic block `M ≤ n + 1 ≤ 2M` (`M ≥ 2`),
`Lévy(g_c) - 2 P_c(g_c) ≥ (s_c (log M - c_c) - 2 C_c) ∑ b_n²`, uniformly in the number and
positions of the scales: the archimedean gain grows like `log M` on `ℓ²`, the prime channel
stays `ℓ²`-bounded. -/
theorem criticalCollaredLevyPrime_ge (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ} (hM : 2 ≤ M)
    (hS : DyadicScaleBlock S M) :
    (((criticalCollarArchLogSlope * (Real.log M - criticalCollarArchLogOffset) -
        2 * criticalCollaredPrimeConstant) * ∑ n ∈ S, b n ^ 2 : ℝ) : EReal) ≤
      (sourceLevyEnergy (criticalCollaredSource S b) : EReal) -
        ((2 * criticalCollaredPrimeEnergy S b : ℝ) : EReal) := by
  set E := ∑ n ∈ S, b n ^ 2
  set X := criticalCollarArchLogSlope * (Real.log M - criticalCollarArchLogOffset) * E
  have hlev : (X : EReal) ≤ (sourceLevyEnergy (criticalCollaredSource S b) : EReal) := by
    have h1 := ofReal_le_criticalCollaredLevyEnergy S b hM fun n hn => (hS n hn).1
    have h2 := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1
    rw [EReal.coe_ennreal_ofReal] at h2
    exact le_trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)) h2
  have hP := abs_criticalCollaredPrimeEnergy_le (by omega) hS b
  have hP' : 2 * criticalCollaredPrimeEnergy S b ≤ 2 * criticalCollaredPrimeConstant * E := by
    have := (abs_le.mp hP).2
    linarith
  rw [show (criticalCollarArchLogSlope * (Real.log M - criticalCollarArchLogOffset) -
      2 * criticalCollaredPrimeConstant) * E = X - 2 * criticalCollaredPrimeConstant * E by ring,
    EReal.coe_sub]
  exact EReal.sub_le_sub hlev (EReal.coe_le_coe_iff.mpr hP')

/-- **Positive definiteness on high dyadic blocks.** If `s_c (log M - c_c) > 2 C_c`, then every
nonzero real family on a dyadic block `[M, 2M]` has strictly positive collared Lévy–prime
energy, with no restriction on the number of atoms. -/
theorem criticalCollaredLevyPrime_pos (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ} (hM : 2 ≤ M)
    (hS : DyadicScaleBlock S M)
    (hlog : 2 * criticalCollaredPrimeConstant <
      criticalCollarArchLogSlope * (Real.log M - criticalCollarArchLogOffset))
    (hb : ∃ n ∈ S, b n ≠ 0) :
    0 < (sourceLevyEnergy (criticalCollaredSource S b) : EReal) -
        ((2 * criticalCollaredPrimeEnergy S b : ℝ) : EReal) := by
  obtain ⟨j, hj, hbj⟩ := hb
  have hE : 0 < ∑ n ∈ S, b n ^ 2 :=
    lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg (b i)) hj)
  refine lt_of_lt_of_le (EReal.coe_pos.mpr (mul_pos (by linarith) hE))
    (criticalCollaredLevyPrime_ge S b hM hS)

end GaloisForLFunctions.ArithmeticPositivityTheory
