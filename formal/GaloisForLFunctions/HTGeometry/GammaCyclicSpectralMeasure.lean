import GaloisForLFunctions.HTGeometry.CoshFourierInversion

/-!
# The Gamma cyclic spectral measure

Fourier inversion turns the closed nonnegative transform of `φ(t) = (cosh t)^(-1/2)` into a
probability density

```text
ρ(x) = 2^(-1/2) |Γ(1/4 + iπx)|² / √π ≥ 0,     ∫_ℝ ρ = 1,
```

whose characteristic function is `φ`:

```text
∫_ℝ e^(2πi h x) ρ(x) dx = (cosh h)^(-1/2) .
```

Subtracting the values at `h-k` and `h+k` gives the spectral form of the odd Gamma kernel,

```text
φ(h-k) - φ(h+k) = 2 ∫_ℝ sin(2π h x) sin(2π k x) ρ(x) dx ,
```

which is positive semidefinite in the odd sector.
-/

open MeasureTheory FourierTransform FourierTransformInv

namespace HTGeometry

noncomputable section

/-! ### The density -/

/-- The archimedean spectral density `ρ(x) = 2^(-1/2) |Γ(1/4 + iπx)|²/√π`. -/
def gammaCyclicDensity (x : ℝ) : ℝ :=
  (2 : ℝ) ^ ((1 / 2 : ℝ) - 1) *
    Complex.normSq (Complex.Gamma
      ((((1 / 2 : ℝ) : ℂ) + ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) / 2)) /
    Real.Gamma (1 / 2)

/-- The Fourier transform of the covariance is the density. -/
theorem fourier_coshHalf_apply (x : ℝ) :
    𝓕 coshHalf x = ((gammaCyclicDensity x : ℝ) : ℂ) := by
  rw [Real.fourier_eq]
  have hcongr : ∀ v : ℝ, (𝐞 (-(inner ℝ v x)) • coshHalf v)
      = (((Real.cosh v) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) *
        Complex.exp (-(((2 * Real.pi * x : ℝ) : ℂ) * (v : ℂ)) * Complex.I) := by
    intro v
    have hexp : ((2 * Real.pi * (-(v * x)) : ℝ) : ℂ) * Complex.I
        = -(((2 * Real.pi * x : ℝ) : ℂ) * (v : ℂ)) * Complex.I := by
      push_cast
      ring
    rw [Real.inner_apply, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, hexp, coshHalf,
      mul_comm]
  simp_rw [hcongr]
  rw [integral_cosh_rpow_neg_mul_exp_eq_ofReal (by norm_num) (2 * Real.pi * x)]
  rfl

theorem gammaCyclicDensity_nonneg (x : ℝ) : 0 ≤ gammaCyclicDensity x :=
  integral_cosh_rpow_neg_mul_exp_nonneg (by norm_num) (2 * Real.pi * x)

theorem integrable_gammaCyclicDensity : Integrable gammaCyclicDensity := by
  have h := integrable_fourier_coshHalf.re
  refine h.congr ?_
  filter_upwards with x
  rw [fourier_coshHalf_apply]
  simp

theorem continuous_coshHalfReal : Continuous fun t : ℝ => Real.cosh t ^ (-(1 / 2) : ℝ) :=
  Real.continuous_cosh.rpow_const fun x => Or.inl (Real.cosh_pos x).ne'

/-! ### The characteristic function -/

/-- **Fourier inversion in density form.**  `∫ e^(2πihx) ρ(x) dx = (cosh h)^(-1/2)`. -/
theorem integral_exp_mul_gammaCyclicDensity (h : ℝ) :
    (∫ x : ℝ, Complex.exp (((2 * Real.pi * (x * h) : ℝ) : ℂ) * Complex.I) *
        ((gammaCyclicDensity x : ℝ) : ℂ))
      = ((Real.cosh h ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
  have hinv := congrFun fourierInv_fourier_coshHalf h
  rw [Real.fourierInv_eq] at hinv
  have hcongr : ∀ x : ℝ, (𝐞 (inner ℝ x h) • 𝓕 coshHalf x)
      = Complex.exp (((2 * Real.pi * (x * h) : ℝ) : ℂ) * Complex.I) *
        ((gammaCyclicDensity x : ℝ) : ℂ) := by
    intro x
    rw [Real.inner_apply, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul,
      fourier_coshHalf_apply]
  simp_rw [hcongr] at hinv
  rw [hinv, coshHalf]

/-! ### The odd kernel is spectral -/

theorem integrable_cos_mul_gammaCyclicDensity (a : ℝ) :
    Integrable fun x : ℝ => Real.cos (2 * Real.pi * (x * a)) * gammaCyclicDensity x := by
  refine Integrable.mono' (g := fun x => |gammaCyclicDensity x|)
    integrable_gammaCyclicDensity.abs ?_ ?_
  · exact ((Real.continuous_cos.comp (by fun_prop)).aestronglyMeasurable).mul
      integrable_gammaCyclicDensity.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |Real.cos (2 * Real.pi * (x * a))| ≤ 1 := Real.abs_cos_le_one _
    nlinarith [abs_nonneg (gammaCyclicDensity x)]

theorem integral_cos_mul_gammaCyclicDensity (a : ℝ) :
    (∫ x : ℝ, Real.cos (2 * Real.pi * (x * a)) * gammaCyclicDensity x)
      = Real.cosh a ^ (-(1 / 2) : ℝ) := by
  have hint : Integrable fun x : ℝ =>
      Complex.exp (((2 * Real.pi * (x * a) : ℝ) : ℂ) * Complex.I) *
        ((gammaCyclicDensity x : ℝ) : ℂ) := by
    refine Integrable.mono' (g := fun x => |gammaCyclicDensity x|)
      integrable_gammaCyclicDensity.abs ?_ ?_
    · refine (Continuous.aestronglyMeasurable ?_).mul
        (Complex.continuous_ofReal.comp_aestronglyMeasurable
          integrable_gammaCyclicDensity.aestronglyMeasurable)
      exact Complex.continuous_exp.comp (by fun_prop)
    · filter_upwards with x
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
  have hre := Complex.reCLM.integral_comp_comm hint
  rw [integral_exp_mul_gammaCyclicDensity a] at hre
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at hre
  rw [← hre]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.exp_ofReal_mul_I_re]

/-- **The odd Gamma kernel is spectral.**
`φ(h-k) - φ(h+k) = 2 ∫ sin(2πhx) sin(2πkx) ρ(x) dx`. -/
theorem gammaCyclicOddKernel_eq (h k : ℝ) :
    Real.cosh (h - k) ^ (-(1 / 2) : ℝ) - Real.cosh (h + k) ^ (-(1 / 2) : ℝ)
      = 2 * ∫ x : ℝ, Real.sin (2 * Real.pi * (x * h)) * Real.sin (2 * Real.pi * (x * k)) *
          gammaCyclicDensity x := by
  have h1 := integral_cos_mul_gammaCyclicDensity (h - k)
  have h2 := integral_cos_mul_gammaCyclicDensity (h + k)
  rw [← h1, ← h2, ← integral_sub (integrable_cos_mul_gammaCyclicDensity _)
    (integrable_cos_mul_gammaCyclicDensity _), ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards with x
  have hcos : Real.cos (2 * Real.pi * (x * (h - k))) - Real.cos (2 * Real.pi * (x * (h + k)))
      = 2 * (Real.sin (2 * Real.pi * (x * h)) * Real.sin (2 * Real.pi * (x * k))) := by
    rw [Real.cos_sub_cos]
    have e1 : (2 * Real.pi * (x * (h - k)) + 2 * Real.pi * (x * (h + k))) / 2
        = 2 * Real.pi * (x * h) := by ring
    have e2 : (2 * Real.pi * (x * (h - k)) - 2 * Real.pi * (x * (h + k))) / 2
        = -(2 * Real.pi * (x * k)) := by ring
    rw [e1, e2, Real.sin_neg]
    ring
  calc Real.cos (2 * Real.pi * (x * (h - k))) * gammaCyclicDensity x -
        Real.cos (2 * Real.pi * (x * (h + k))) * gammaCyclicDensity x
      = (Real.cos (2 * Real.pi * (x * (h - k))) -
          Real.cos (2 * Real.pi * (x * (h + k)))) * gammaCyclicDensity x := by ring
    _ = 2 * (Real.sin (2 * Real.pi * (x * h)) * Real.sin (2 * Real.pi * (x * k)) *
          gammaCyclicDensity x) := by rw [hcos]; ring

/-! ### Total mass -/

theorem integral_gammaCyclicDensity : (∫ x : ℝ, gammaCyclicDensity x) = 1 := by
  have h := integral_cos_mul_gammaCyclicDensity 0
  simp only [mul_zero, Real.cos_zero, one_mul] at h
  rw [h, Real.cosh_zero, Real.one_rpow]

/-! ### The spectral measure -/

theorem continuous_gammaCyclicDensity : Continuous gammaCyclicDensity := by
  have hc : Continuous (𝓕 coshHalf) := by
    refine VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar ?_
      integrable_coshHalf
    fun_prop
  have heq : gammaCyclicDensity = fun x => (𝓕 coshHalf x).re := by
    funext x
    rw [fourier_coshHalf_apply, Complex.ofReal_re]
  rw [heq]
  exact Complex.continuous_re.comp hc

theorem lintegral_gammaCyclicDensity :
    (∫⁻ x : ℝ, ENNReal.ofReal (gammaCyclicDensity x)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_gammaCyclicDensity
    (Filter.Eventually.of_forall gammaCyclicDensity_nonneg), integral_gammaCyclicDensity]
  simp

/-- The Gamma cyclic spectral measure `ν_Γ`, normalised so that its characteristic function is
`φ(h) = (cosh h)^(-1/2)`. -/
def gammaCyclicMeasure : Measure ℝ :=
  Measure.map (fun x : ℝ => 2 * Real.pi * x)
    (volume.withDensity fun x => ENNReal.ofReal (gammaCyclicDensity x))

instance isProbabilityMeasure_gammaCyclicMeasure :
    IsProbabilityMeasure gammaCyclicMeasure := by
  constructor
  rw [gammaCyclicMeasure, Measure.map_apply (by fun_prop) MeasurableSet.univ,
    Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_gammaCyclicDensity]

/-- **The Gamma cyclic measure has characteristic function `φ`.** -/
theorem integral_exp_gammaCyclicMeasure (h : ℝ) :
    (∫ y : ℝ, Complex.exp (((h * y : ℝ) : ℂ) * Complex.I) ∂gammaCyclicMeasure)
      = ((Real.cosh h ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
  have hmeas : Measurable fun x : ℝ => (2 : ℝ) * Real.pi * x := by fun_prop
  have hstrong : AEStronglyMeasurable (fun y : ℝ => Complex.exp (((h * y : ℝ) : ℂ) * Complex.I))
      (Measure.map (fun x : ℝ => 2 * Real.pi * x)
        (volume.withDensity fun x => ENNReal.ofReal (gammaCyclicDensity x))) := by
    refine Continuous.aestronglyMeasurable ?_
    exact Complex.continuous_exp.comp (by fun_prop)
  have hdmeas : Measurable fun x : ℝ => ENNReal.ofReal (gammaCyclicDensity x) :=
    ENNReal.measurable_ofReal.comp continuous_gammaCyclicDensity.measurable
  rw [gammaCyclicMeasure, integral_map hmeas.aemeasurable hstrong,
    integral_withDensity_eq_integral_toReal_smul hdmeas
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  rw [← integral_exp_mul_gammaCyclicDensity h]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (gammaCyclicDensity_nonneg x), Complex.real_smul, mul_comm]
  congr 2
  push_cast
  ring

/-- **The odd Gamma kernel is spectral, measure form.**
`φ(h-k) - φ(h+k) = 2 ∫ sin(h y) sin(k y) dν_Γ(y)`. -/
theorem gammaCyclicOddKernel_measure_eq (h k : ℝ) :
    Real.cosh (h - k) ^ (-(1 / 2) : ℝ) - Real.cosh (h + k) ^ (-(1 / 2) : ℝ)
      = 2 * ∫ y : ℝ, Real.sin (h * y) * Real.sin (k * y) ∂gammaCyclicMeasure := by
  have hmeas : Measurable fun x : ℝ => (2 : ℝ) * Real.pi * x := by fun_prop
  have hstrong : AEStronglyMeasurable (fun y : ℝ => Real.sin (h * y) * Real.sin (k * y))
      (Measure.map (fun x : ℝ => 2 * Real.pi * x)
        (volume.withDensity fun x => ENNReal.ofReal (gammaCyclicDensity x))) :=
    Continuous.aestronglyMeasurable (by fun_prop)
  have hdmeas : Measurable fun x : ℝ => ENNReal.ofReal (gammaCyclicDensity x) :=
    ENNReal.measurable_ofReal.comp continuous_gammaCyclicDensity.measurable
  rw [gammaCyclicMeasure, integral_map hmeas.aemeasurable hstrong,
    integral_withDensity_eq_integral_toReal_smul hdmeas
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  rw [gammaCyclicOddKernel_eq h k]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (gammaCyclicDensity_nonneg x), smul_eq_mul]
  have e1 : h * (2 * Real.pi * x) = 2 * Real.pi * (x * h) := by ring
  have e2 : k * (2 * Real.pi * x) = 2 * Real.pi * (x * k) := by ring
  rw [e1, e2]
  ring

/-! ### Tail bounds for the density -/

theorem gammaCyclicDensity_le_bound (x : ℝ) :
    gammaCyclicDensity x ≤ ∫ t : ℝ, ‖coshHalf t‖ := by
  have h := norm_fourier_coshHalf_le_const x
  rw [fourier_coshHalf_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gammaCyclicDensity_nonneg x)] at h
  exact h

theorem gammaCyclicDensity_mul_sq_le (x : ℝ) :
    gammaCyclicDensity x * (4 * Real.pi ^ 2 * x ^ 2) ≤ ∫ t : ℝ, ‖coshHalfDeriv2 t‖ := by
  have h := norm_sq_mul_fourier_coshHalf_le x
  rw [fourier_coshHalf_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (gammaCyclicDensity_nonneg x)] at h
  exact h

/-- The density is even. -/
theorem gammaCyclicDensity_neg (x : ℝ) : gammaCyclicDensity (-x) = gammaCyclicDensity x := by
  have hconj : (((1 / 2 : ℝ) : ℂ) + ((2 * Real.pi * (-x) : ℝ) : ℂ) * Complex.I) / 2
      = (starRingEnd ℂ) ((((1 / 2 : ℝ) : ℂ) + ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) / 2) := by
    simp [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq_apply]
    constructor <;> ring
  rw [gammaCyclicDensity, gammaCyclicDensity, hconj, Complex.Gamma_conj, Complex.normSq_conj]

/-- **The measure-to-density bridge.**  Integrals against `ν_Γ` are density integrals in the
`2π`-rescaled variable. -/
theorem integral_gammaCyclicMeasure_eq_density {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ y : ℝ, f y ∂gammaCyclicMeasure)
      = ∫ x : ℝ, f (2 * Real.pi * x) * gammaCyclicDensity x := by
  have hmeas : Measurable fun x : ℝ => (2 : ℝ) * Real.pi * x := by fun_prop
  have hdmeas : Measurable fun x : ℝ => ENNReal.ofReal (gammaCyclicDensity x) :=
    ENNReal.measurable_ofReal.comp continuous_gammaCyclicDensity.measurable
  rw [gammaCyclicMeasure, integral_map hmeas.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hdmeas
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (gammaCyclicDensity_nonneg x), smul_eq_mul, mul_comm]

end

end HTGeometry
