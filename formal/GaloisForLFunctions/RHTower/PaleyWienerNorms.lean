import GaloisForLFunctions.RHTower.BandTransformEnergy
import GaloisForLFunctions.RHTower.BandLeakageEnvelope

/-!
# Plancherel, Nikolskii and Bernstein for a compactly supported spectrum

A function built from a compactly supported spectrum,

```text
Psi(x) = ∫_(-k)^k H(v) e^(2 pi i v x) dv,
```

is the Fourier integral of the spectrum extended by zero, so Plancherel computes its energy exactly:
`∫_ℝ |Psi|² = ∫_(-k)^k |H|²`.  Two inequalities follow from that identity and cost nothing more:

* **Nikolskii**: Cauchy–Schwarz on the defining integral bounds the pointwise size by the energy,
  `|Psi(x)|² <= 2k ∫ |H|² = 2k ∫_ℝ |Psi|²`;
* **Bernstein**: the derivative has spectrum `2 pi v H(v)`, and `|2 pi v| <= 2 pi k` on the window, so
  `∫_ℝ |Psi'|² <= (2 pi k)² ∫_ℝ |Psi|²`.

Applied to the band transform — whose spectrum is the windowed spectrum of the test function, supported
in `|v| <= c/(2 pi)` — these are the sup-norm and derivative bounds of the prolate theory: every
eigenfunction of the band operator obeys `psi(x)² <= (c/pi) ‖psi‖²/nu` and its derivative has energy at
most `c²` times its own.  Mathlib has neither inequality.
-/

noncomputable section

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral FourierTransform

open _root_.RHTower

/-! ## The spectrum extended by zero -/

theorem integrable_indicator_of_continuous {H : ℝ → ℂ} (hH : Continuous H) (k : ℝ) :
    Integrable (Set.indicator (Icc (-k) k) H) (volume : Measure ℝ) := by
  rw [integrable_indicator_iff measurableSet_Icc]
  exact hH.continuousOn.integrableOn_compact isCompact_Icc

theorem memLp_indicator_of_continuous {H : ℝ → ℂ} (hH : Continuous H) (k : ℝ) :
    MemLp (Set.indicator (Icc (-k) k) H) 2 (volume : Measure ℝ) := by
  rw [memLp_indicator_iff_restrict measurableSet_Icc]
  haveI hfin : IsFiniteMeasure ((volume : Measure ℝ).restrict (Icc (-k) k)) := by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -k) (b := k)).exists_bound_of_continuousOn
    hH.continuousOn
  refine MemLp.of_bound hH.aestronglyMeasurable.restrict C ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact hC x hx

/-- **A compactly supported spectrum synthesises the Fourier integral of its zero extension.** -/
theorem compactFourier_eq_fourier_indicator (H : ℝ → ℂ) {k : ℝ} (hk : 0 ≤ k) (x : ℝ) :
    HTGeometry.compactFourier H (-k) k ((2 * Real.pi * x : ℝ) : ℂ)
      = 𝓕 (Set.indicator (Icc (-k) k) H) (-x) := by
  rw [Real.fourier_eq', HTGeometry.compactFourier]
  have hind : (∫ v : ℝ, Complex.exp ((↑(-2 * Real.pi * (inner ℝ v (-x))) : ℂ) * Complex.I)
        • Set.indicator (Icc (-k) k) H v)
      = ∫ v in Icc (-k) k, H v * Complex.exp (Complex.I * (((2 * Real.pi * x : ℝ) : ℂ) * (v : ℂ))) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [Set.indicator_apply]
    split_ifs with hv
    · have hinner : (inner ℝ v (-x) : ℝ) = -(v * x) := by
        simp
        ring
      rw [hinner, smul_eq_mul]
      have hexp : Complex.exp ((↑(-2 * Real.pi * -(v * x)) : ℂ) * Complex.I)
          = Complex.exp (Complex.I * (((2 * Real.pi * x : ℝ) : ℂ) * (v : ℂ))) := by
        congr 1
        push_cast
        ring
      rw [hexp]
      ring
    · rw [smul_zero]
  rw [hind, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -k ≤ k)]

/-- **Plancherel for a compactly supported spectrum.** -/
theorem integral_norm_sq_compactFourier {H : ℝ → ℂ} (hH : Continuous H) {k : ℝ} (hk : 0 ≤ k) :
    (∫ x : ℝ, ‖HTGeometry.compactFourier H (-k) k ((2 * Real.pi * x : ℝ) : ℂ)‖ ^ 2)
      = ∫ v in Icc (-k) k, ‖H v‖ ^ 2 := by
  have hstep1 : (∫ x : ℝ, ‖HTGeometry.compactFourier H (-k) k ((2 * Real.pi * x : ℝ) : ℂ)‖ ^ 2)
      = ∫ x : ℝ, ‖𝓕 (Set.indicator (Icc (-k) k) H) (-x)‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖HTGeometry.compactFourier H (-k) k ((2 * Real.pi * x : ℝ) : ℂ)‖ ^ 2
        = ‖𝓕 (Set.indicator (Icc (-k) k) H) (-x)‖ ^ 2
    rw [compactFourier_eq_fourier_indicator H hk x]
  have hstep2 : (∫ x : ℝ, ‖𝓕 (Set.indicator (Icc (-k) k) H) (-x)‖ ^ 2)
      = ∫ x : ℝ, ‖𝓕 (Set.indicator (Icc (-k) k) H) x‖ ^ 2 :=
    integral_neg_eq_self (fun x : ℝ => ‖𝓕 (Set.indicator (Icc (-k) k) H) x‖ ^ 2) volume
  have hstep3 : (∫ x : ℝ, ‖𝓕 (Set.indicator (Icc (-k) k) H) x‖ ^ 2)
      = ∫ v : ℝ, ‖Set.indicator (Icc (-k) k) H v‖ ^ 2 :=
    integral_norm_sq_fourier_eq (integrable_indicator_of_continuous hH k)
      (memLp_indicator_of_continuous hH k)
  have hstep4 : (∫ v : ℝ, ‖Set.indicator (Icc (-k) k) H v‖ ^ 2)
      = ∫ v in Icc (-k) k, ‖H v‖ ^ 2 := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [Set.indicator_apply]
    split_ifs with hv
    · rfl
    · simp
  rw [hstep1, hstep2, hstep3, hstep4]

/-! ## Nikolskii -/

/-- **Nikolskii's inequality for a compactly supported spectrum.**  Cauchy–Schwarz on the synthesis
integral: the pointwise size is bounded by the window length times the spectral energy. -/
theorem norm_sq_compactFourier_le {H : ℝ → ℂ} (hH : Continuous H) {k : ℝ} (hk : 0 ≤ k) (x : ℝ) :
    ‖HTGeometry.compactFourier H (-k) k ((2 * Real.pi * x : ℝ) : ℂ)‖ ^ 2
      ≤ 2 * k * ∫ v in Icc (-k) k, ‖H v‖ ^ 2 := by
  have hle : -k ≤ k := by linarith
  set f : ℝ → ℂ := fun v => H v * Complex.exp (Complex.I * (((2 * Real.pi * x : ℝ) : ℂ) * (v : ℂ)))
    with hf
  have hnormf : ∀ v : ℝ, ‖f v‖ = ‖H v‖ := by
    intro v
    rw [hf]
    have hphase : ‖Complex.exp (Complex.I * (((2 * Real.pi * x : ℝ) : ℂ) * (v : ℂ)))‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : (Complex.I * (((2 * Real.pi * x : ℝ) : ℂ) * (v : ℂ))).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre, Real.exp_zero]
    rw [norm_mul, hphase, mul_one]
  have hcontf : Continuous f := by
    rw [hf]
    fun_prop
  -- the modulus of the integral is at most the integral of the modulus
  have h1 : ‖∫ v in (-k)..k, f v‖ ≤ ∫ v in (-k)..k, ‖H v‖ := by
    have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := f) hle
    refine h.trans ?_
    refine le_of_eq ?_
    refine intervalIntegral.integral_congr fun v _ => ?_
    exact hnormf v
  -- and the squared mean is at most the mean square
  have h2 : (∫ v in (-k)..k, ‖H v‖) ^ 2 ≤ (k - -k) * ∫ v in (-k)..k, ‖H v‖ ^ 2 := by
    rcases eq_or_lt_of_le hle with heq | hlt
    · have hk0 : k = 0 := by linarith
      simp [hk0]
    · exact sq_intervalIntegral_le hlt (hH.norm)
  have h3 : ‖∫ v in (-k)..k, f v‖ ^ 2 ≤ (∫ v in (-k)..k, ‖H v‖) ^ 2 := by
    have hnn : (0 : ℝ) ≤ ∫ v in (-k)..k, ‖H v‖ :=
      intervalIntegral.integral_nonneg hle fun v _ => norm_nonneg _
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hwindow : (∫ v in (-k)..k, ‖H v‖ ^ 2) = ∫ v in Icc (-k) k, ‖H v‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hlen : k - -k = 2 * k := by ring
  rw [HTGeometry.compactFourier]
  calc ‖∫ v in (-k)..k, f v‖ ^ 2 ≤ (∫ v in (-k)..k, ‖H v‖) ^ 2 := h3
    _ ≤ (k - -k) * ∫ v in (-k)..k, ‖H v‖ ^ 2 := h2
    _ = 2 * k * ∫ v in Icc (-k) k, ‖H v‖ ^ 2 := by rw [hlen, hwindow]

/-! ## Bernstein -/

/-- **The derivative of a synthesis is the synthesis of the multiplied spectrum.** -/
theorem hasDerivAt_compactFourier_real {H : ℝ → ℂ} (hH : Continuous H) (k x : ℝ) :
    HasDerivAt (fun y : ℝ => HTGeometry.compactFourier H (-k) k ((2 * Real.pi * y : ℝ) : ℂ))
      (HTGeometry.compactFourier (fun v => 2 * (Real.pi : ℂ) * Complex.I * (v : ℂ) * H v) (-k) k
        ((2 * Real.pi * x : ℝ) : ℂ)) x := by
  have hcast : ((2 * Real.pi * x : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * ((x : ℝ) : ℂ) := by
    push_cast
    ring
  have hF := HTGeometry.hasDerivAt_compactFourier hH (-k) k ((2 * Real.pi * x : ℝ) : ℂ)
  have hE : HasDerivAt (fun z : ℂ => 2 * (Real.pi : ℂ) * z) (2 * (Real.pi : ℂ))
      ((x : ℝ) : ℂ) := by
    simpa using (hasDerivAt_id ((x : ℝ) : ℂ)).const_mul (2 * (Real.pi : ℂ))
  have hFat : HasDerivAt (HTGeometry.compactFourier H (-k) k)
      (∫ v in (-k)..k, H v * (Complex.I * (v : ℂ))
        * Complex.exp (Complex.I * (((2 * Real.pi * x : ℝ) : ℂ) * (v : ℂ))))
      (2 * (Real.pi : ℂ) * ((x : ℝ) : ℂ)) := by
    rw [← hcast]
    exact hF
  have hcomp := (hFat.comp ((x : ℝ) : ℂ) hE).comp_ofReal
  refine hcomp.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · -- the derivative is the synthesis of the multiplied spectrum
    rw [HTGeometry.compactFourier, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun v _ => ?_
    ring
  · filter_upwards with y
    have hcasty : ((2 * Real.pi * y : ℝ) : ℂ) = 2 * (Real.pi : ℂ) * ((y : ℝ) : ℂ) := by
      push_cast
      ring
    simp only [Function.comp_apply]
    rw [hcasty]

/-- **Bernstein's inequality for a compactly supported spectrum.**  Multiplying the spectrum by the
frequency multiplies the energy by at most `(2 pi k)²` — the derivative of a band-limited function has
energy at most the squared bandwidth times its own. -/
theorem integral_norm_sq_deriv_compactFourier_le {H : ℝ → ℂ} (hH : Continuous H) {k : ℝ}
    (hk : 0 ≤ k) :
    (∫ x : ℝ, ‖HTGeometry.compactFourier
        (fun v => 2 * (Real.pi : ℂ) * Complex.I * (v : ℂ) * H v) (-k) k
          ((2 * Real.pi * x : ℝ) : ℂ)‖ ^ 2)
      ≤ (2 * Real.pi * k) ^ 2
          * ∫ x : ℝ, ‖HTGeometry.compactFourier H (-k) k ((2 * Real.pi * x : ℝ) : ℂ)‖ ^ 2 := by
  have hle : -k ≤ k := by linarith
  have hmul : Continuous fun v : ℝ => 2 * (Real.pi : ℂ) * Complex.I * (v : ℂ) * H v := by
    fun_prop
  rw [integral_norm_sq_compactFourier hmul hk, integral_norm_sq_compactFourier hH hk]
  -- compare the two spectral energies pointwise on the window
  have hint1 : IntegrableOn (fun v : ℝ =>
      ‖2 * (Real.pi : ℂ) * Complex.I * (v : ℂ) * H v‖ ^ 2) (Icc (-k) k) volume :=
    ((hmul.norm.pow 2).continuousOn).integrableOn_compact isCompact_Icc
  have hint2 : IntegrableOn (fun v : ℝ => (2 * Real.pi * k) ^ 2 * ‖H v‖ ^ 2)
      (Icc (-k) k) volume :=
    (((hH.norm.pow 2).const_mul _).continuousOn).integrableOn_compact isCompact_Icc
  have hpt : ∀ v ∈ Icc (-k) k,
      ‖2 * (Real.pi : ℂ) * Complex.I * (v : ℂ) * H v‖ ^ 2
        ≤ (2 * Real.pi * k) ^ 2 * ‖H v‖ ^ 2 := by
    intro v hv
    have hnorm : ‖2 * (Real.pi : ℂ) * Complex.I * (v : ℂ) * H v‖
        = 2 * Real.pi * |v| * ‖H v‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, norm_mul]
      have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
      have hpi : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      rw [h2, hpi]
    have hvk : |v| ≤ k := abs_le.mpr ⟨hv.1, hv.2⟩
    have hnn : (0 : ℝ) ≤ ‖H v‖ := norm_nonneg _
    have habs : (0 : ℝ) ≤ |v| := abs_nonneg v
    rw [hnorm, mul_pow]
    have hle2 : (2 * Real.pi * |v|) ^ 2 ≤ (2 * Real.pi * k) ^ 2 := by
      have hnn2 : (0 : ℝ) ≤ 2 * Real.pi * |v| := by positivity
      have hmono : 2 * Real.pi * |v| ≤ 2 * Real.pi * k := by
        have : (0 : ℝ) ≤ 2 * Real.pi := by positivity
        exact mul_le_mul_of_nonneg_left hvk this
      exact pow_le_pow_left₀ hnn2 hmono 2
    have hsq : (0 : ℝ) ≤ ‖H v‖ ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right hle2 hsq
  have hcompare := MeasureTheory.setIntegral_mono_on hint1 hint2 measurableSet_Icc hpt
  refine hcompare.trans ?_
  rw [← MeasureTheory.integral_const_mul]
/-! ## The band transform -/

/-- The band transform synthesises its windowed spectrum. -/
theorem bandTransform_eq_compactFourier {c : ℝ} (hc : 0 < c) {Φ : ℝ → ℝ} (hΦ : Continuous Φ)
    (x : ℝ) :
    ((bandTransform c Φ x : ℝ) : ℂ)
      = HTGeometry.compactFourier (𝓕 (bandTrunc Φ)) (-(c / (2 * Real.pi))) (c / (2 * Real.pi))
          ((2 * Real.pi * x : ℝ) : ℂ) := by
  have hkpos : 0 < c / (2 * Real.pi) := by positivity
  rw [bandTransform_eq_fourier_windowSpectrum hc hΦ x, windowSpectrum,
    compactFourier_eq_fourier_indicator (𝓕 (bandTrunc Φ)) hkpos.le x]

/-- **Nikolskii for the band transform.**  Its pointwise square is at most `c/pi` times its energy. -/
theorem sq_bandTransform_le {c : ℝ} (hc : 0 < c) {Φ : ℝ → ℝ} (hΦ : Continuous Φ) (x : ℝ) :
    (bandTransform c Φ x) ^ 2 ≤ (c / Real.pi) * ∫ y : ℝ, (bandTransform c Φ y) ^ 2 := by
  have hkpos : 0 < c / (2 * Real.pi) := by positivity
  have hG := continuous_fourier_bandTrunc hΦ
  -- the pointwise bound in terms of the spectral energy
  have h1 : (bandTransform c Φ x) ^ 2
      ≤ 2 * (c / (2 * Real.pi)) * ∫ v in Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)),
          ‖𝓕 (bandTrunc Φ) v‖ ^ 2 := by
    have hcast : (bandTransform c Φ x) ^ 2
        = ‖HTGeometry.compactFourier (𝓕 (bandTrunc Φ)) (-(c / (2 * Real.pi)))
            (c / (2 * Real.pi)) ((2 * Real.pi * x : ℝ) : ℂ)‖ ^ 2 := by
      rw [← bandTransform_eq_compactFourier hc hΦ x, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hcast]
    exact norm_sq_compactFourier_le hG hkpos.le x
  -- the spectral energy is the energy of the transform
  have h2 : (∫ v in Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)), ‖𝓕 (bandTrunc Φ) v‖ ^ 2)
      = ∫ y : ℝ, (bandTransform c Φ y) ^ 2 := by
    have hplan := integral_norm_sq_compactFourier hG hkpos.le
    rw [← hplan]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show ‖HTGeometry.compactFourier (𝓕 (bandTrunc Φ)) (-(c / (2 * Real.pi)))
        (c / (2 * Real.pi)) ((2 * Real.pi * y : ℝ) : ℂ)‖ ^ 2 = (bandTransform c Φ y) ^ 2
    rw [← bandTransform_eq_compactFourier hc hΦ y, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [h2] at h1
  have hval : 2 * (c / (2 * Real.pi)) = c / Real.pi := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [hval] at h1
  exact h1

/-- The energy of the band transform is the energy of the synthesis of its windowed spectrum. -/
theorem integral_sq_bandTransform_eq_synthesis {c : ℝ} (hc : 0 < c) {Φ : ℝ → ℝ}
    (hΦ : Continuous Φ) :
    (∫ x : ℝ, ‖HTGeometry.compactFourier (𝓕 (bandTrunc Φ)) (-(c / (2 * Real.pi)))
        (c / (2 * Real.pi)) ((2 * Real.pi * x : ℝ) : ℂ)‖ ^ 2)
      = ∫ x : ℝ, (bandTransform c Φ x) ^ 2 := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ‖HTGeometry.compactFourier (𝓕 (bandTrunc Φ)) (-(c / (2 * Real.pi)))
      (c / (2 * Real.pi)) ((2 * Real.pi * y : ℝ) : ℂ)‖ ^ 2 = (bandTransform c Φ y) ^ 2
  rw [← bandTransform_eq_compactFourier hc hΦ y, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Bernstein's inequality for the band transform.**  The synthesis of the frequency-multiplied
spectrum — that is, the derivative of the band transform — has energy at most `c²` times its own. -/
theorem integral_sq_bandTransform_bernstein {c : ℝ} (hc : 0 < c) {Φ : ℝ → ℝ} (hΦ : Continuous Φ) :
    (∫ x : ℝ, ‖HTGeometry.compactFourier
        (fun v => 2 * (Real.pi : ℂ) * Complex.I * (v : ℂ) * 𝓕 (bandTrunc Φ) v)
          (-(c / (2 * Real.pi))) (c / (2 * Real.pi)) ((2 * Real.pi * x : ℝ) : ℂ)‖ ^ 2)
      ≤ c ^ 2 * ∫ x : ℝ, (bandTransform c Φ x) ^ 2 := by
  have hkpos : 0 < c / (2 * Real.pi) := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hband := integral_norm_sq_deriv_compactFourier_le (continuous_fourier_bandTrunc hΦ)
    hkpos.le
  rw [integral_sq_bandTransform_eq_synthesis hc hΦ] at hband
  have hval : (2 * Real.pi * (c / (2 * Real.pi))) ^ 2 = c ^ 2 := by
    have hne : 2 * Real.pi ≠ 0 := by positivity
    field_simp
  rw [hval] at hband
  exact hband

/-- **The sup bound for the prolate eigenfunctions.**  Every eigenfunction of the band operator obeys
`psi(x)² <= (c/pi) ‖psi‖²/nu` at every real point. -/
theorem sq_eigenExtension_le {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {ψ : RealIntervalL2 (-1 : ℝ) 1} (heig : bandOperatorL2 c ψ = ν • ψ) (x : ℝ) :
    (eigenExtension c ν ψ x) ^ 2 ≤ (c / Real.pi) * (‖ψ‖ ^ 2 / ν) := by
  have hΦ : Continuous (eigenExtension c ν ψ) := continuous_eigenExtension c ν ψ
  have hbt : ∀ y, bandTransform c (eigenExtension c ν ψ) y = ν * eigenExtension c ν ψ y :=
    bandTransform_eigenExtension (ne_of_gt hν) heig
  have hmain := sq_bandTransform_le hc hΦ x
  rw [hbt x] at hmain
  -- the energy of the band transform is `nu²` times the energy of the eigenfunction
  have henergy : (∫ y : ℝ, (bandTransform c (eigenExtension c ν ψ) y) ^ 2)
      = ν ^ 2 * (‖ψ‖ ^ 2 / ν) := by
    have h1 : (∫ y : ℝ, (bandTransform c (eigenExtension c ν ψ) y) ^ 2)
        = ν ^ 2 * ∫ y : ℝ, (eigenExtension c ν ψ y) ^ 2 := by
      rw [← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show (bandTransform c (eigenExtension c ν ψ) y) ^ 2
          = ν ^ 2 * (eigenExtension c ν ψ y) ^ 2
      rw [hbt y]
      ring
    rw [h1, integral_sq_eigenExtension hc (ne_of_gt hν) heig]
  rw [henergy] at hmain
  -- divide by `nu²`
  have hνne : (ν : ℝ) ≠ 0 := ne_of_gt hν
  have hνsq : (0 : ℝ) < ν ^ 2 := by positivity
  have hstep : ν ^ 2 * (eigenExtension c ν ψ x) ^ 2
      ≤ ν ^ 2 * ((c / Real.pi) * (‖ψ‖ ^ 2 / ν)) := by
    have hrw : (c / Real.pi) * (ν ^ 2 * (‖ψ‖ ^ 2 / ν))
        = ν ^ 2 * ((c / Real.pi) * (‖ψ‖ ^ 2 / ν)) := by ring
    calc ν ^ 2 * (eigenExtension c ν ψ x) ^ 2
        = (ν * eigenExtension c ν ψ x) ^ 2 := by ring
      _ ≤ (c / Real.pi) * (ν ^ 2 * (‖ψ‖ ^ 2 / ν)) := hmain
      _ = ν ^ 2 * ((c / Real.pi) * (‖ψ‖ ^ 2 / ν)) := hrw
  exact le_of_mul_le_mul_left hstep hνsq

end GaloisForLFunctions.RHTower

end
