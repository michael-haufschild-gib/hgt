import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilConstrainedKernelForm

/-!
# The constrained restricted Weil form as a Fourier multiplier

The kernel form `A(S) g(0) + ∫_0^S K₊(h)(g(0) − g(h)) dh + prime block` of
`SuzukiWeilConstrainedKernelForm` is transported to the frequency side.  With mathlib's
normalisation `𝓕 u (ξ) = ∫ u(x) e^{-2πixξ} dx` and `F(ξ) = ‖𝓕 u (ξ)‖²`:

* `g(h) = ∫ F(ξ) cos(2π ξ h) dξ` (Fourier inversion of the Schwartz autocorrelation, whose
  transform is `F` by the corpus's `fourier_autocorrelationSchwartz`);
* `∫_0^S K₊(h)(g(0) − g(h)) dh = ∫ F(ξ) Λ_S(2πξ) dξ`, `Λ_S(η) = ∫_0^S K₊(h)(1 − cos hη) dh`
  (Tonelli, with the majorant `K₊(h) h² · 2π² ξ² F(ξ)`);
* on the polar-constrained subspace the whole form is
  `∫ F(ξ) m_S(2πξ) dξ`, `m_S(η) = A(S) + Λ_S(η) − 2 Σ_{2 ≤ n ≤ e^S} Λ(n) n^{-1/2} cos(η log n)`.

`m_S` is exactly the multiplier certified band by band in the P2 computations.
-/

open MeasureTheory Set FourierTransform SchwartzMap

namespace RHTower

open GaloisForLFunctions.RHTower GaloisForLFunctions.HTGeometry

/-- The Schwartz autocorrelation at lag `h` is the Fourier integral of the spectral density. -/
theorem autocorrelationSchwartz_eq_integral_fourier (u : 𝓢(ℝ, ℂ)) (h : ℝ) :
    autocorrelationSchwartz u h =
      ∫ ξ : ℝ, ((‖𝓕 (⇑u) ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * (Real.fourierChar (ξ * h) : ℂ) := by
  have h3 : Integrable (𝓕 ⇑(autocorrelationSchwartz u)) := by
    have h1 := (fourier (autocorrelationSchwartz u)).integrable (μ := volume)
    rwa [fourier_coe] at h1
  have hinv := (autocorrelationSchwartz u).continuous.fourierInv_fourier_eq
    (autocorrelationSchwartz u).integrable h3
  have hh := congrFun hinv h
  rw [← hh, Real.fourierInv_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  have hf : 𝓕 ⇑(autocorrelationSchwartz u) ξ = 𝓕 (⇑u) ξ * (starRingEnd ℂ) (𝓕 (⇑u) ξ) := by
    rw [← fourier_coe, fourier_autocorrelationSchwartz, fourier_coe]
  have hin : inner ℝ ξ h = ξ * h := by simp [mul_comm]
  simp only [hf, Circle.smul_def, smul_eq_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq, hin]
  ring

/-- The spectral density `‖𝓕 u‖²` is the modulus of the transform of the autocorrelation. -/
theorem norm_fourier_autocorrelationSchwartz (u : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    ‖𝓕 ⇑(autocorrelationSchwartz u) ξ‖ = ‖𝓕 (⇑u) ξ‖ ^ (2 : ℕ) := by
  have hf : 𝓕 ⇑(autocorrelationSchwartz u) ξ = 𝓕 (⇑u) ξ * (starRingEnd ℂ) (𝓕 (⇑u) ξ) := by
    rw [← fourier_coe, fourier_autocorrelationSchwartz, fourier_coe]
  rw [hf, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

theorem integrable_spectralDensity (u : 𝓢(ℝ, ℂ)) :
    Integrable (fun ξ : ℝ => ‖𝓕 (⇑u) ξ‖ ^ (2 : ℕ)) := by
  have h3 : Integrable (𝓕 ⇑(autocorrelationSchwartz u)) := by
    have h1 := (fourier (autocorrelationSchwartz u)).integrable (μ := volume)
    rwa [fourier_coe] at h1
  refine h3.norm.congr (Filter.Eventually.of_forall fun ξ => ?_)
  exact norm_fourier_autocorrelationSchwartz u ξ

theorem integrable_sq_mul_spectralDensity (u : 𝓢(ℝ, ℂ)) :
    Integrable (fun ξ : ℝ => ξ ^ (2 : ℕ) * ‖𝓕 (⇑u) ξ‖ ^ (2 : ℕ)) := by
  have h1 := (fourier (autocorrelationSchwartz u)).integrable_pow_mul (μ := volume) 2
  refine h1.congr (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [fourier_coe, Real.norm_eq_abs, sq_abs]
  rw [norm_fourier_autocorrelationSchwartz]

theorem continuous_spectralDensity (u : 𝓢(ℝ, ℂ)) :
    Continuous fun ξ : ℝ => ‖𝓕 (⇑u) ξ‖ ^ (2 : ℕ) := by
  have : Continuous (𝓕 (⇑u)) := by
    rw [← fourier_coe]; exact (fourier u).continuous
  exact this.norm.pow 2

/-- Real form: `g(h) = ∫ ‖𝓕 u‖² cos(2π ξ h) dξ`. -/
theorem autocorrelationSchwartz_re_eq_integral_cos (u : 𝓢(ℝ, ℂ)) (h : ℝ) :
    (autocorrelationSchwartz u h).re =
      ∫ ξ : ℝ, ‖𝓕 (⇑u) ξ‖ ^ (2 : ℕ) * Real.cos (2 * Real.pi * (ξ * h)) := by
  rw [autocorrelationSchwartz_eq_integral_fourier]
  have hint : Integrable (fun ξ : ℝ =>
      ((‖𝓕 (⇑u) ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * (Real.fourierChar (ξ * h) : ℂ)) := by
    refine ((integrable_spectralDensity u).norm).mono' ?_ ?_
    · refine (Complex.continuous_ofReal.comp (continuous_spectralDensity u)).aestronglyMeasurable.mul ?_
      exact (continuous_subtype_val.comp (Real.continuous_fourierChar.comp
        (continuous_id.mul continuous_const))).aestronglyMeasurable
    · filter_upwards with ξ
      rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real]
  change RCLike.re (∫ ξ : ℝ, ((‖𝓕 (⇑u) ξ‖ ^ (2 : ℕ) : ℝ) : ℂ) * (Real.fourierChar (ξ * h) : ℂ)) = _
  rw [← integral_re hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [Real.fourierChar_apply, RCLike.re_to_complex, Complex.re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re]

/-- Suzuki's autocorrelation as a Fourier integral of the spectral density of the test. -/
theorem suzukiCoreAutocorrelation_eq_integral_fourier_cos {a : ℝ} (u : SuzukiRestrictedWeilCore a)
    (h : ℝ) :
    suzukiCoreAutocorrelation u h =
      ∫ ξ : ℝ, ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
        Real.cos (2 * Real.pi * (ξ * h)) := by
  have h1 : (suzukiCoreAutocorrelation u h : ℂ) =
      autocorrelationSchwartz (suzukiRestrictedWeilCoreSchwartz u) h := by
    rw [← suzukiRestrictedWeilCoreAutocorrelationTest_apply_eq_ofReal]
    rfl
  have h2 := congrArg Complex.re h1
  rw [Complex.ofReal_re] at h2
  rw [h2, autocorrelationSchwartz_re_eq_integral_cos]

/-- The archimedean energy multiplier `Λ_S(η) = ∫_0^S K₊(h)(1 − cos hη) dh`. -/
noncomputable def weilConstrainedMultiplierEnergy (S η : ℝ) : ℝ :=
  ∫ h in Ioc (0 : ℝ) S, weilPositiveKernel h * (1 - Real.cos (h * η))

/-- `K₊(h) h² ≤ e^{S/2} S` on `(0, S]`. -/
theorem weilPositiveKernel_mul_sq_le {h S : ℝ} (hh : 0 < h) (hS : h ≤ S) :
    weilPositiveKernel h * h ^ (2 : ℕ) ≤ Real.exp (S / 2) * S := by
  unfold weilPositiveKernel
  have hsinh : h ≤ Real.sinh h := (Real.self_le_sinh_iff).2 hh.le
  have hsp : 0 < Real.sinh h := Real.sinh_pos_iff.2 hh
  have he : Real.exp (h / 2) ≤ Real.exp (S / 2) := Real.exp_le_exp.2 (by linarith)
  rw [div_mul_eq_mul_div, div_le_iff₀ hsp]
  calc Real.exp (h / 2) * h ^ (2 : ℕ) = Real.exp (h / 2) * h * h := by ring
    _ ≤ Real.exp (S / 2) * S * Real.sinh h := by
        gcongr
        exact mul_nonneg (Real.exp_pos _).le (by linarith)

/-- Integrability of the Tonelli integrand `K₊(h) F(ξ) (1 − cos 2πξh)` on `(0, S] × ℝ`. -/
theorem integrable_tonelli_integrand (A : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) :
    Integrable (fun z : ℝ × ℝ => weilPositiveKernel z.1 *
      (‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) z.2‖ ^ (2 : ℕ) *
        (1 - Real.cos (2 * Real.pi * (z.2 * z.1)))))
      ((volume.restrict (Ioc (0 : ℝ) (2 * A.1))).prod volume) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (2 * A.1))) :=
    isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  have hG := integrable_sq_mul_spectralDensity (suzukiRestrictedWeilCoreSchwartz u)
  have hC : Integrable (fun _ : ℝ => Real.exp (2 * A.1 / 2) * (2 * A.1) * (2 * Real.pi ^ (2 : ℕ)))
      (volume.restrict (Ioc (0 : ℝ) (2 * A.1))) := integrable_const _
  have hmaj := hC.mul_prod hG
  refine hmaj.mono' ?_ ?_
  · have hK : Measurable weilPositiveKernel := by
      unfold weilPositiveKernel
      exact (Real.measurable_exp.comp (measurable_id.div_const 2)).div
        Real.continuous_sinh.measurable
    have hFm : Measurable fun ξ : ℝ => ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) :=
      (continuous_spectralDensity _).measurable
    refine Measurable.aestronglyMeasurable ?_
    refine (hK.comp measurable_fst).mul ((hFm.comp measurable_snd).mul ?_)
    exact measurable_const.sub (Real.continuous_cos.measurable.comp
      (measurable_const.mul (measurable_snd.mul measurable_fst)))
  · have hprod : (volume.restrict (Ioc (0 : ℝ) (2 * A.1))).prod (volume : Measure ℝ) =
        ((volume : Measure ℝ).prod volume).restrict (Ioc (0 : ℝ) (2 * A.1) ×ˢ univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [hprod, ae_restrict_iff' (measurableSet_Ioc.prod MeasurableSet.univ)]
    filter_upwards with z hz
    have hz1 : 0 < z.1 := hz.1.1
    have hz2 : z.1 ≤ 2 * A.1 := hz.1.2
    have hKpos : 0 < weilPositiveKernel z.1 := weilPositiveKernel_pos hz1
    have hF0 : 0 ≤ ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) z.2‖ ^ (2 : ℕ) := by positivity
    have hcos : 0 ≤ 1 - Real.cos (2 * Real.pi * (z.2 * z.1)) := by
      linarith [Real.cos_le_one (2 * Real.pi * (z.2 * z.1))]
    have hcos2 : 1 - Real.cos (2 * Real.pi * (z.2 * z.1)) ≤
        2 * Real.pi ^ (2 : ℕ) * (z.2 ^ (2 : ℕ) * z.1 ^ (2 : ℕ)) := by
      have := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * (z.2 * z.1))
      nlinarith
    have hKsq := weilPositiveKernel_mul_sq_le hz1 hz2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc weilPositiveKernel z.1 * (‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) z.2‖ ^ (2 : ℕ) *
          (1 - Real.cos (2 * Real.pi * (z.2 * z.1))))
        ≤ weilPositiveKernel z.1 * (‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) z.2‖ ^ (2 : ℕ) *
          (2 * Real.pi ^ (2 : ℕ) * (z.2 ^ (2 : ℕ) * z.1 ^ (2 : ℕ)))) := by gcongr
      _ = (weilPositiveKernel z.1 * z.1 ^ (2 : ℕ)) * (2 * Real.pi ^ (2 : ℕ)) *
          (z.2 ^ (2 : ℕ) * ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) z.2‖ ^ (2 : ℕ)) := by ring
      _ ≤ (Real.exp (2 * A.1 / 2) * (2 * A.1)) * (2 * Real.pi ^ (2 : ℕ)) *
          (z.2 ^ (2 : ℕ) * ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) z.2‖ ^ (2 : ℕ)) := by
          gcongr
      _ = _ := by ring

/-- `F · cos` is integrable for every frequency shift. -/
theorem integrable_spectralDensity_mul_cos (u : 𝓢(ℝ, ℂ)) (c : ℝ) :
    Integrable (fun ξ : ℝ => ‖𝓕 (⇑u) ξ‖ ^ (2 : ℕ) * Real.cos (2 * Real.pi * (ξ * c))) := by
  refine (integrable_spectralDensity u).mono' ?_ ?_
  · exact ((continuous_spectralDensity u).mul (Real.continuous_cos.comp
      (continuous_const.mul (continuous_id.mul continuous_const)))).aestronglyMeasurable
  · filter_upwards with ξ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖𝓕 (⇑u) ξ‖ ^ (2 : ℕ))]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

/-- **Tonelli.**  The kernel energy is the spectral density integrated against `Λ_S(2πξ)`. -/
theorem integral_weilPositiveKernel_mul_defect_eq_fourier (A : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) :
    (∫ h in Ioc (0 : ℝ) (2 * A.1), weilPositiveKernel h *
      (suzukiCoreAutocorrelation u 0 - suzukiCoreAutocorrelation u h)) =
      ∫ ξ : ℝ, ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
        weilConstrainedMultiplierEnergy (2 * A.1) (2 * Real.pi * ξ) := by
  have hdef : ∀ h : ℝ, suzukiCoreAutocorrelation u 0 - suzukiCoreAutocorrelation u h =
      ∫ ξ : ℝ, ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
        (1 - Real.cos (2 * Real.pi * (ξ * h))) := by
    intro h
    rw [suzukiCoreAutocorrelation_eq_integral_fourier_cos u 0,
      suzukiCoreAutocorrelation_eq_integral_fourier_cos u h,
      ← integral_sub (integrable_spectralDensity_mul_cos _ 0) (integrable_spectralDensity_mul_cos _ h)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [mul_zero, Real.cos_zero, mul_one]
    ring
  have hswap := integral_integral_swap (μ := volume.restrict (Ioc (0 : ℝ) (2 * A.1)))
    (ν := volume) (f := fun h ξ => weilPositiveKernel h *
      (‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
        (1 - Real.cos (2 * Real.pi * (ξ * h))))) (integrable_tonelli_integrand A u)
  calc (∫ h in Ioc (0 : ℝ) (2 * A.1), weilPositiveKernel h *
        (suzukiCoreAutocorrelation u 0 - suzukiCoreAutocorrelation u h))
      = ∫ h in Ioc (0 : ℝ) (2 * A.1), ∫ ξ : ℝ, weilPositiveKernel h *
          (‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
            (1 - Real.cos (2 * Real.pi * (ξ * h)))) := by
        refine setIntegral_congr_fun measurableSet_Ioc (fun h _ => ?_)
        rw [hdef h, integral_const_mul]
    _ = ∫ ξ : ℝ, ∫ h in Ioc (0 : ℝ) (2 * A.1), weilPositiveKernel h *
          (‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
            (1 - Real.cos (2 * Real.pi * (ξ * h)))) := hswap
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        unfold weilConstrainedMultiplierEnergy
        dsimp only
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioc (fun h _ => ?_)
        ring_nf

/-- The constrained multiplier
`m_S(η) = A(S) + Λ_S(η) − 2 Σ_{2 ≤ n ≤ e^S} Λ(n) n^{-1/2} cos(η log n)`. -/
noncomputable def weilConstrainedMultiplier (S η : ℝ) : ℝ :=
  weilConstrainedConstant S + weilConstrainedMultiplierEnergy S η -
    2 * ∑ n ∈ Finset.Icc 2 ⌊Real.exp S⌋₊, criticalMellinAtomWeight n * Real.cos (η * Real.log n)

theorem integrable_spectralDensity_mul_multiplierEnergy (A : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1) :
    Integrable (fun ξ : ℝ => ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
      weilConstrainedMultiplierEnergy (2 * A.1) (2 * Real.pi * ξ)) := by
  have := (integrable_tonelli_integrand A u).integral_prod_right
  refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
  unfold weilConstrainedMultiplierEnergy
  dsimp only
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc (fun h _ => ?_)
  ring_nf

/-- **The constrained restricted Weil form is a Fourier multiplier.**  On the polar-constrained
subspace, `Q(u) = ∫ ‖𝓕 u(ξ)‖² m_S(2πξ) dξ`. -/
theorem suzukiRestrictedWeilForm_eq_integral_multiplier_of_moment_eq_zero
    (A : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore A.1)
    (hmom : (∫ x : ℝ, Real.exp (x / 2) * u x) = 0 ∨ (∫ x : ℝ, Real.exp (-(x / 2)) * u x) = 0) :
    suzukiRestrictedWeilForm A.1 u u =
      ∫ ξ : ℝ, ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
        weilConstrainedMultiplier (2 * A.1) (2 * Real.pi * ξ) := by
  rw [suzukiRestrictedWeilForm_eq_constrainedKernelForm_of_moment_eq_zero A u hmom,
    weilPrimeBlock_suzukiRestrictedWeilIndices_eq_autocorrelation,
    integral_weilPositiveKernel_mul_defect_eq_fourier]
  have hF := integrable_spectralDensity (suzukiRestrictedWeilCoreSchwartz u)
  have hΛ := integrable_spectralDensity_mul_multiplierEnergy A u
  have hcos := integrable_spectralDensity_mul_cos (suzukiRestrictedWeilCoreSchwartz u)
  have hg0 : suzukiCoreAutocorrelation u 0 =
      ∫ ξ : ℝ, ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) := by
    rw [suzukiCoreAutocorrelation_eq_integral_fourier_cos u 0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [mul_zero, Real.cos_zero, mul_one]
  have hsum : ∀ n : ℕ, suzukiCoreAutocorrelation u (Real.log n) =
      ∫ ξ : ℝ, ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
        Real.cos (2 * Real.pi * ξ * Real.log n) := by
    intro n
    rw [suzukiCoreAutocorrelation_eq_integral_fourier_cos u (Real.log n)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    ring_nf
  have hcos' : ∀ n : ℕ, Integrable (fun ξ : ℝ =>
      ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) * Real.cos (2 * Real.pi * ξ * Real.log n)) := by
    intro n
    refine (hcos (Real.log n)).congr (Filter.Eventually.of_forall fun ξ => ?_)
    ring_nf
  have hsumint : Integrable (fun ξ : ℝ => ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
      (2 * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A.1)⌋₊, criticalMellinAtomWeight n *
        Real.cos (2 * Real.pi * ξ * Real.log n))) := by
    have : (fun ξ : ℝ => ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
        (2 * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A.1)⌋₊, criticalMellinAtomWeight n *
          Real.cos (2 * Real.pi * ξ * Real.log n))) =
        fun ξ : ℝ => ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A.1)⌋₊, (2 * criticalMellinAtomWeight n) *
          (‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
            Real.cos (2 * Real.pi * ξ * Real.log n)) := by
      funext ξ
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      ring
    rw [this]
    exact integrable_finsetSum _ (fun n _ => (hcos' n).const_mul _)
  rw [hg0]
  simp_rw [hsum]
  -- expand the right-hand side
  have hexp : (fun ξ : ℝ => ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
      weilConstrainedMultiplier (2 * A.1) (2 * Real.pi * ξ)) =
      fun ξ : ℝ => (weilConstrainedConstant (2 * A.1) *
        ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) +
        ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
          weilConstrainedMultiplierEnergy (2 * A.1) (2 * Real.pi * ξ)) -
        ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
          (2 * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A.1)⌋₊, criticalMellinAtomWeight n *
            Real.cos (2 * Real.pi * ξ * Real.log n)) := by
    funext ξ
    unfold weilConstrainedMultiplier
    ring
  have h12 : Integrable (fun ξ : ℝ => weilConstrainedConstant (2 * A.1) *
      ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) +
      ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
        weilConstrainedMultiplierEnergy (2 * A.1) (2 * Real.pi * ξ)) := (hF.const_mul _).add hΛ
  have hsplit : (∫ ξ : ℝ, ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
      (2 * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A.1)⌋₊, criticalMellinAtomWeight n *
        Real.cos (2 * Real.pi * ξ * Real.log n))) =
      2 * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A.1)⌋₊, criticalMellinAtomWeight n *
        ∫ ξ : ℝ, ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
          Real.cos (2 * Real.pi * ξ * Real.log n) := by
    have hfun : (fun ξ : ℝ => ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
        (2 * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A.1)⌋₊, criticalMellinAtomWeight n *
          Real.cos (2 * Real.pi * ξ * Real.log n))) =
        fun ξ : ℝ => ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A.1)⌋₊, (2 * criticalMellinAtomWeight n) *
          (‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
            Real.cos (2 * Real.pi * ξ * Real.log n)) := by
      funext ξ
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      ring
    rw [hfun, integral_finsetSum _ (fun n _ => (hcos' n).const_mul _), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [integral_const_mul]
    ring
  rw [hexp, integral_sub h12 hsumint, integral_add (hF.const_mul _) hΛ, integral_const_mul, hsplit]
  ring

/-- A uniform lower bound of the multiplier is a lower bound of the constrained form
(`g(0) = ‖u‖²` is the total spectral mass). -/
theorem suzukiRestrictedWeilForm_ge_of_multiplier_ge (A : SuzukiPositiveAperture)
    (u : SuzukiRestrictedWeilCore A.1)
    (hmom : (∫ x : ℝ, Real.exp (x / 2) * u x) = 0 ∨ (∫ x : ℝ, Real.exp (-(x / 2)) * u x) = 0)
    {κ : ℝ} (hκ : ∀ η : ℝ, κ ≤ weilConstrainedMultiplier (2 * A.1) η) :
    κ * suzukiCoreAutocorrelation u 0 ≤ suzukiRestrictedWeilForm A.1 u u := by
  rw [suzukiRestrictedWeilForm_eq_integral_multiplier_of_moment_eq_zero A u hmom,
    suzukiCoreAutocorrelation_eq_integral_fourier_cos u 0]
  have hF := integrable_spectralDensity (suzukiRestrictedWeilCoreSchwartz u)
  have hg0 : (∫ ξ : ℝ, ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
      Real.cos (2 * Real.pi * (ξ * 0))) = ∫ ξ : ℝ, ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [mul_zero, Real.cos_zero, mul_one]
  rw [hg0, ← integral_const_mul]
  have hΛ : Integrable (fun ξ : ℝ => ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
      weilConstrainedMultiplier (2 * A.1) (2 * Real.pi * ξ)) := by
    have h1 := integrable_spectralDensity_mul_multiplierEnergy A u
    have h2 := integrable_spectralDensity_mul_cos (suzukiRestrictedWeilCoreSchwartz u)
    have h3 : Integrable (fun ξ : ℝ => ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A.1)⌋₊,
        (2 * criticalMellinAtomWeight n) * (‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
          Real.cos (2 * Real.pi * (ξ * Real.log n)))) :=
      integrable_finsetSum _ (fun n _ => (h2 (Real.log n)).const_mul _)
    refine (((hF.const_mul (weilConstrainedConstant (2 * A.1))).add h1).sub h3).congr
      (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    unfold weilConstrainedMultiplier
    have hc : ∀ n : ℕ, Real.cos (2 * Real.pi * ξ * Real.log n) =
        Real.cos (2 * Real.pi * (ξ * Real.log n)) := fun n => by ring_nf
    simp only [hc]
    have hs : (∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A.1)⌋₊, (2 * criticalMellinAtomWeight n) *
        (‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
          Real.cos (2 * Real.pi * (ξ * Real.log n)))) =
        ‖𝓕 (⇑(suzukiRestrictedWeilCoreSchwartz u)) ξ‖ ^ (2 : ℕ) *
          (2 * ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A.1)⌋₊, criticalMellinAtomWeight n *
            Real.cos (2 * Real.pi * (ξ * Real.log n))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun n _ => by ring)
    rw [hs]
    ring
  refine integral_mono (hF.const_mul κ) hΛ (fun ξ => ?_)
  simp only
  exact mul_le_mul_of_nonneg_right (hκ _) (by positivity) |>.trans_eq (mul_comm _ _)

end RHTower
