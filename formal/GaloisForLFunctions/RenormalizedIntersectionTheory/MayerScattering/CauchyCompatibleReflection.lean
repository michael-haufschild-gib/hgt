import GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering.CauchyReflectionOrder
import GaloisForLFunctions.HTGeometry.L2ConvolutionFourierMultiplier

/-!
# Reflection compatible with actual Cauchy averaging

Compatibility with the normalized Cauchy convolution forces its arithmetic reflection correction.
The construction retains the literal convolution and its action on actual resonant core fields.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter MeasureTheory Topology
open scoped ComplexConjugate FourierTransform ENNReal
open GaloisForLFunctions RenormalizedIntersectionTheory
open MayerScatteringCore MayerCauchyMellinSymbol

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering

/-- Local interval tests recover the pointwise cost of a bounded factorization. -/
private theorem relative_multiplier_norm_bound
    {a b : ℝ → ℂ}
    {A B T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)}
    (ha : Continuous a) (hb : Continuous b)
    (hA : ∀ f, (A f : ℝ → ℂ) =ᵐ[volume] fun x => a x * f x)
    (hB : ∀ f, (B f : ℝ → ℂ) =ᵐ[volume] fun x => b x * f x)
    (hT : ∀ f, T (A f) = B f) (x₀ : ℝ) :
    ‖b x₀‖ ≤ ‖T‖ * ‖a x₀‖ := by
  by_contra hbad
  have hgap : 0 < ‖b x₀‖ - ‖T‖ * ‖a x₀‖ := sub_pos.mpr (lt_of_not_ge hbad)
  let ε : ℝ := (‖b x₀‖ - ‖T‖ * ‖a x₀‖) / (2 * (‖T‖ + 1))
  have hden : 0 < 2 * (‖T‖ + 1) := by positivity
  have hε : 0 < ε := div_pos hgap hden
  have he : ε * (2 * (‖T‖ + 1)) = ‖b x₀‖ - ‖T‖ * ‖a x₀‖ :=
    div_mul_cancel₀ _ hden.ne'
  let U : ℝ := ‖a x₀‖ + ε
  let L : ℝ := ‖b x₀‖ - ε
  have hU : 0 ≤ U := add_nonneg (norm_nonneg _) hε.le
  have hstrict : ‖T‖ * U < L := by
    dsimp only [U, L]
    nlinarith only [he, hgap]
  have hL : 0 < L := lt_of_le_of_lt (mul_nonneg (norm_nonneg T) hU) hstrict
  have hnA : ∀ᶠ x in 𝓝 x₀, ‖a x‖ < U :=
    (ha.norm.tendsto x₀).eventually (eventually_lt_nhds (by dsimp [U]; linarith only [hε]))
  have hnB : ∀ᶠ x in 𝓝 x₀, L < ‖b x‖ :=
    (hb.norm.tendsto x₀).eventually (eventually_gt_nhds (by dsimp [L]; linarith only [hε]))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hnA.and hnB)
  have hfin : volume (Metric.ball x₀ r) ≠ ∞ := by
    rw [Real.volume_ball]
    exact ENNReal.ofReal_ne_top
  let f : Lp ℂ 2 (volume : Measure ℝ) := indicatorConstLp 2 measurableSet_ball hfin (1 : ℂ)
  have hfpos : 0 < ‖f‖ := by
    dsimp only [f]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul,
      measureReal_def, Real.volume_ball, ENNReal.toReal_ofReal (by positivity)]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hAf : ‖A f‖ ≤ U * ‖f‖ := by
    have hh : ‖A f‖ ≤ ‖(U : ℂ) • f‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hA f, Lp.coeFn_smul (U : ℂ) f,
        (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_ball) (hμs := hfin)
          (c := (1 : ℂ)))] with x hAx hsmul hfx
      rw [hAx, hsmul, Pi.smul_apply, norm_mul, norm_smul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hU]
      by_cases hx : x ∈ Metric.ball x₀ r
      · exact mul_le_mul_of_nonneg_right (hball hx).1.le (norm_nonneg _)
      · change f x = _ at hfx
        rw [hfx, indicator_of_notMem hx]
        simp
    simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hU] using hh
  have hBf : L * ‖f‖ ≤ ‖B f‖ := by
    have hh : ‖(L : ℂ) • f‖ ≤ ‖B f‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hB f, Lp.coeFn_smul (L : ℂ) f,
        (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_ball) (hμs := hfin)
          (c := (1 : ℂ)))] with x hBx hsmul hfx
      rw [hBx, hsmul, Pi.smul_apply, norm_mul, norm_smul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
      by_cases hx : x ∈ Metric.ball x₀ r
      · exact mul_le_mul_of_nonneg_right (hball hx).2.le (norm_nonneg _)
      · change f x = _ at hfx
        rw [hfx, indicator_of_notMem hx]
        simp
    simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL] using hh
  have hnorm : L * ‖f‖ ≤ (‖T‖ * U) * ‖f‖ := by
    calc
      _ ≤ ‖B f‖ := hBf
      _ = ‖T (A f)‖ := congrArg norm (hT f).symm
      _ ≤ ‖T‖ * ‖A f‖ := T.le_opNorm _
      _ ≤ ‖T‖ * (U * ‖f‖) := mul_le_mul_of_nonneg_left hAf (norm_nonneg T)
      _ = _ := by ring
  exact (not_le_of_gt (mul_lt_mul_of_pos_right hstrict hfpos)) hnorm

/-- The actual Cauchy averaging kernel on unweighted logarithmic Haar coordinates,
normalized to take the Gamma-normalized theta field to the PM core. -/
def mayerCauchyHaarKernel (s : ℂ) (x : ℝ) : ℂ :=
  (Gammaℝ (2 * s))⁻¹ * MayerQuadraticCone.cauchyKernel (2 * s) (Real.exp (-x))

/-- The logarithmic kernel is measurable at every parameter. -/
theorem measurable_mayerCauchyHaarKernel (s : ℂ) : Measurable (mayerCauchyHaarKernel s) := by
  unfold mayerCauchyHaarKernel MayerQuadraticCone.cauchyKernel MayerQuadraticCone.cauchyWeight
  fun_prop

/-- The zeroth absolute Mellin moment admits the actual kernel on the whole source half-plane. -/
theorem integrable_mayerCauchyHaarKernel (s : ℂ) (hs : 0 < s.re) :
    Integrable (mayerCauchyHaarKernel s) := by
  have hm := (MayerCauchyMellinSymbol.cauchyKernel_mellin_zero
    (show 0 < (2 * s).re by simp; linarith only [hs])).1
  have hi := _root_.RHTower.integrable_logMellinPullback_of_mellinConvergent
    (MayerQuadraticCone.cauchyKernel (2 * s)) 0 hm
  simp only [neg_zero, zero_mul, Real.exp_zero, one_smul] at hi
  exact hi.const_mul _

/-- The actual unweighted Cauchy kernel has exactly the core Mellin multiplier. -/
theorem fourier_mayerCauchyHaarKernel (s : ℂ) (hs : 0 < s.re) (ξ : ℝ) :
    𝓕 (mayerCauchyHaarKernel s) ξ = mayerCoreMellinFactor s (2 * Real.pi * ξ) := by
  have hm := MayerCauchyMellinSymbol.cauchyKernel_hasMellin
    (show 0 < (2 * s).re by simp; linarith only [hs])
    (show -1 < ((((2 * Real.pi * ξ : ℝ) : ℂ) * I).re) by simp)
    (show ((((2 * Real.pi * ξ : ℝ) : ℂ) * I).re) < (2 * s).re + 1 by
      simp; linarith only [hs])
  have he : 𝓕 (fun x : ℝ => MayerQuadraticCone.cauchyKernel (2 * s) (Real.exp (-x))) ξ =
      MayerCauchyMellinSymbol.symbol (2 * s) (((2 * Real.pi * ξ : ℝ) : ℂ) * I) := by
    rw [← hm.2, mellin_eq_fourier]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, mul_zero, zero_mul, sub_self, neg_zero, Real.exp_zero, one_smul,
      Complex.mul_im, mul_one, add_zero]
    rw [show 2 * Real.pi * ξ / (2 * Real.pi) = ξ by field_simp]
  change 𝓕 (fun x : ℝ => (Gammaℝ (2 * s))⁻¹ *
    MayerQuadraticCone.cauchyKernel (2 * s) (Real.exp (-x))) ξ = _
  rw [HTGeometry.fourier_const_mul_apply, he, mayerCoreMellinFactor]
  ring

/-- Actual normalized Cauchy averaging, as a bounded operator on unweighted logarithmic `L²`. -/
def mayerCauchyHaarOperator (s : ℂ) (hs : 0 < s.re) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (HTGeometry.convolutionKernel (mayerCauchyHaarKernel s)
    (measurable_mayerCauchyHaarKernel s) (integrable_mayerCauchyHaarKernel s hs)).op

/-- The bounded operator retains the literal normalized Cauchy convolution. -/
theorem mayerCauchyHaarOperator_coeFn (s : ℂ) (hs : 0 < s.re)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (mayerCauchyHaarOperator s hs f : ℝ → ℂ) =ᵐ[volume]
      fun y => ∫ z : ℝ, mayerCauchyHaarKernel s (y - z) * f z := by
  have h := (HTGeometry.convolutionKernel (mayerCauchyHaarKernel s)
    (measurable_mayerCauchyHaarKernel s) (integrable_mayerCauchyHaarKernel s hs)).op_coeFn f
  filter_upwards [h] with y hy
  exact hy

/-- Plancherel identifies the source integral operator with its literal Fourier multiplier. -/
theorem mayerCauchyHaarOperator_eq_fourierMultiplier (s : ℂ) (hs : 0 < s.re) :
    mayerCauchyHaarOperator s hs =
      HTGeometry.fourierMulCLM
        (HTGeometry.continuous_fourier_of_integrable' (integrable_mayerCauchyHaarKernel s hs)).measurable
        (integral_nonneg fun x => norm_nonneg (mayerCauchyHaarKernel s x))
        (HTGeometry.norm_fourier_apply_le_integral_norm (mayerCauchyHaarKernel s)) :=
  HTGeometry.convolutionKernel_op_eq_fourierMulCLM _ _ _


private theorem cauchy_symbol_bound (s : ℂ) (hs : 0 < s.re) (ξ : ℝ) :
    ‖mayerCoreMellinFactor s (2 * Real.pi * ξ)‖ ≤ ∫ x, ‖mayerCauchyHaarKernel s x‖ := by
  rw [← fourier_mayerCauchyHaarKernel s hs ξ]
  exact HTGeometry.norm_fourier_apply_le_integral_norm _ _

private theorem cauchy_operator_fourier (s : ℂ) (hs : 0 < s.re) :
    mayerCauchyHaarOperator s hs = HTGeometry.fourierMulCLM
      ((continuous_mayerCoreMellinFactor s hs).comp
        (show Continuous (fun ξ : ℝ => 2 * Real.pi * ξ) by fun_prop)).measurable
      (integral_nonneg fun x => norm_nonneg (mayerCauchyHaarKernel s x))
      (cauchy_symbol_bound s hs) := by
  rw [mayerCauchyHaarOperator_eq_fourierMultiplier]
  apply HTGeometry.fourierMulCLM_congr_ae
  exact Filter.Eventually.of_forall (fourier_mayerCauchyHaarKernel s hs)

private theorem cauchy_adjoint_fourier (s : ℂ) (hs : 0 < s.re) :
    ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs) = HTGeometry.fourierMulCLM
      (Complex.continuous_conj.comp ((continuous_mayerCoreMellinFactor s hs).comp
        (show Continuous (fun ξ : ℝ => 2 * Real.pi * ξ) by fun_prop))).measurable
      (integral_nonneg fun x => norm_nonneg (mayerCauchyHaarKernel s x))
      (fun ξ => (Complex.norm_conj _).trans_le (cauchy_symbol_bound s hs ξ)) := by
  rw [cauchy_operator_fourier]
  exact HTGeometry.adjoint_fourierMulCLM _ _ _ _ _ _ (fun _ => rfl)

/-- The Fourier transform of actual Cauchy averaging is its source Mellin symbol. -/
theorem fourier_mayerCauchyHaarOperator_coeFn (s : ℂ) (hs : 0 < s.re)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (HTGeometry.fourierL2 ℝ (mayerCauchyHaarOperator s hs f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => mayerCoreMellinFactor s (2 * Real.pi * ξ) * HTGeometry.fourierL2 ℝ f ξ := by
  rw [cauchy_operator_fourier, HTGeometry.fourierMulCLM_apply,
    HTGeometry.fourierL2_fourierL2inv]
  exact lpBoundedMulCLM_coeFn _ _ _ _

/-- The adjoint averaging operator has the conjugate source symbol. -/
theorem fourier_adjoint_mayerCauchyHaarOperator_coeFn (s : ℂ) (hs : 0 < s.re)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (HTGeometry.fourierL2 ℝ (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs) f)
      : ℝ → ℂ) =ᵐ[volume]
      fun ξ => conj (mayerCoreMellinFactor s (2 * Real.pi * ξ)) * HTGeometry.fourierL2 ℝ f ξ := by
  rw [cauchy_adjoint_fourier, HTGeometry.fourierMulCLM_apply,
    HTGeometry.fourierL2_fourierL2inv]
  exact lpBoundedMulCLM_coeFn _ _ _ _

/-- Cauchy averaging discards no logarithmic `L²` field. -/
theorem injective_mayerCauchyHaarOperator (s : ℂ) (hs : 0 < s.re) :
    Function.Injective (mayerCauchyHaarOperator s hs) := by
  intro f g h
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  apply Lp.ext
  have he := congrArg (HTGeometry.fourierL2 ℝ) h
  filter_upwards [fourier_mayerCauchyHaarOperator_coeFn s hs f,
    fourier_mayerCauchyHaarOperator_coeFn s hs g] with ξ hf hg
  rw [he, hg] at hf
  exact (mul_left_cancel₀ (mayerCoreMellinFactor_ne_zero_of_re_pos s hs _) hf).symm

private theorem injective_adjoint_cauchy (s : ℂ) (hs : 0 < s.re) :
    Function.Injective (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs)) := by
  intro f g h
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  apply Lp.ext
  have he := congrArg (HTGeometry.fourierL2 ℝ) h
  filter_upwards [fourier_adjoint_mayerCauchyHaarOperator_coeFn s hs f,
    fourier_adjoint_mayerCauchyHaarOperator_coeFn s hs g] with ξ hf hg
  rw [he, hg] at hf
  exact (mul_left_cancel₀ ((map_ne_zero (starRingEnd ℂ)).mpr
    (mayerCoreMellinFactor_ne_zero_of_re_pos s hs _)) hf).symm

private theorem fourier_field_reflection_ae (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (HTGeometry.fourierL2 ℝ (mayerFieldReflection f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => mayerArithmeticMellinPhase (2 * Real.pi * ξ) *
        conj (HTGeometry.fourierL2 ℝ f ξ) := by
  change ((Lp.fourierTransformₗᵢ ℝ ℂ) ((Lp.fourierTransformₗᵢ ℝ ℂ).symm
    (HTGeometry.unimodularMulUnitary
      (continuous_mayerArithmeticMellinPhase.comp
        (show Continuous (fun ξ : ℝ => 2 * Real.pi * ξ) by fun_prop)).measurable
      (fun ξ => norm_mayerArithmeticMellinPhase (2 * Real.pi * ξ))
      (star (HTGeometry.fourierL2 ℝ f)))) : ℝ → ℂ) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  filter_upwards [HTGeometry.unimodularMulUnitary_coeFn
    (continuous_mayerArithmeticMellinPhase.comp
      (show Continuous (fun ξ : ℝ => 2 * Real.pi * ξ) by fun_prop)).measurable
    (fun ξ => norm_mayerArithmeticMellinPhase (2 * Real.pi * ξ))
    (star (HTGeometry.fourierL2 ℝ f)), Lp.coeFn_star (HTGeometry.fourierL2 ℝ f)] with ξ h hstar
  rw [h, hstar]
  rfl

/-- Arithmetic field reflection conjugates actual Cauchy averaging to its Hilbert adjoint. -/
theorem mayerFieldReflection_cauchy_adjoint (s : ℂ) (hs : 0 < s.re)
    (f : Lp ℂ 2 (volume : Measure ℝ)) :
    mayerFieldReflection (mayerCauchyHaarOperator s hs (mayerFieldReflection f)) =
      ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs) f := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change HTGeometry.fourierL2 ℝ
    (mayerFieldReflection (mayerCauchyHaarOperator s hs (mayerFieldReflection f))) =
    HTGeometry.fourierL2 ℝ (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs) f)
  apply Lp.ext
  filter_upwards [fourier_field_reflection_ae
      (mayerCauchyHaarOperator s hs (mayerFieldReflection f)),
    fourier_mayerCauchyHaarOperator_coeFn s hs (mayerFieldReflection f),
    fourier_field_reflection_ae f, fourier_adjoint_mayerCauchyHaarOperator_coeFn s hs f]
      with ξ h1 h2 h3 h4
  rw [h1, h2, h3, h4, map_mul, map_mul, starRingEnd_self_apply]
  calc
    _ = (mayerArithmeticMellinPhase (2 * Real.pi * ξ) *
      conj (mayerArithmeticMellinPhase (2 * Real.pi * ξ))) *
        (conj (mayerCoreMellinFactor s (2 * Real.pi * ξ)) * HTGeometry.fourierL2 ℝ f ξ) := by ring
    _ = _ := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mayerArithmeticMellinPhase]
      simp


/-- Actual averaging has dense range, since its adjoint loses no frequency. -/
theorem denseRange_mayerCauchyHaarOperator (s : ℂ) (hs : 0 < s.re) :
    DenseRange (mayerCauchyHaarOperator s hs) := by
  refine HTGeometry.denseRange_of_orthogonal_trivial fun g hg => ?_
  have he := hg (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs) g)
  rw [← ContinuousLinearMap.adjoint_inner_right] at he
  have hz := inner_self_eq_zero.mp he
  apply injective_adjoint_cauchy s hs
  simpa only [map_zero] using hz

/-- The adjoint averaging range is also dense. -/
theorem denseRange_adjoint_mayerCauchyHaarOperator (s : ℂ) (hs : 0 < s.re) :
    DenseRange (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs)) := by
  refine HTGeometry.denseRange_of_orthogonal_trivial fun g hg => ?_
  have he := hg (mayerCauchyHaarOperator s hs g)
  rw [← ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_adjoint] at he
  have hz := inner_self_eq_zero.mp he
  apply injective_mayerCauchyHaarOperator s hs
  simpa only [map_zero] using hz

private def frequencyOperator
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) :=
  (HTGeometry.fourierL2 ℝ).comp (T.comp (HTGeometry.fourierL2inv ℝ))

private theorem norm_frequencyOperator_le
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ)) :
    ‖frequencyOperator T‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun f => ?_
  change ‖HTGeometry.fourierL2 ℝ (T (HTGeometry.fourierL2inv ℝ f))‖ ≤ ‖T‖ * ‖f‖
  rw [HTGeometry.norm_fourierL2_apply]
  simpa only [HTGeometry.norm_fourierL2inv_apply] using T.le_opNorm (HTGeometry.fourierL2inv ℝ f)

/-- Compatibility with actual averaging forces the pointwise reflection cost.
The candidate bounded operator need not be a Fourier multiplier. -/
theorem mayerCauchy_factorization_norm_bound (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hT : ∀ f, T (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs0) f) =
      mayerCauchyHaarOperator (riemannMayerReflect s)
        (by simp [riemannMayerReflect]; linarith only [hs1]) f) (t : ℝ) :
    ‖mayerCoreReflectionFactor s t‖ ≤ ‖T‖ := by
  have hr : 0 < (riemannMayerReflect s).re := by
    simp [riemannMayerReflect]; linarith only [hs1]
  have ha : Continuous (fun ξ : ℝ => conj (mayerCoreMellinFactor s (2 * Real.pi * ξ))) :=
    Complex.continuous_conj.comp ((continuous_mayerCoreMellinFactor s hs0).comp (by fun_prop))
  have hb : Continuous (fun ξ : ℝ => mayerCoreMellinFactor (riemannMayerReflect s) (2 * Real.pi * ξ)) :=
    (continuous_mayerCoreMellinFactor (riemannMayerReflect s) hr).comp (by fun_prop)
  have hA (f : Lp ℂ 2 (volume : Measure ℝ)) :
      (frequencyOperator (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs0)) f
        : ℝ → ℂ) =ᵐ[volume]
        fun ξ => conj (mayerCoreMellinFactor s (2 * Real.pi * ξ)) * f ξ := by
    simpa only [frequencyOperator, ContinuousLinearMap.comp_apply,
      HTGeometry.fourierL2_fourierL2inv] using
      fourier_adjoint_mayerCauchyHaarOperator_coeFn s hs0 (HTGeometry.fourierL2inv ℝ f)
  have hB (f : Lp ℂ 2 (volume : Measure ℝ)) :
      (frequencyOperator (mayerCauchyHaarOperator (riemannMayerReflect s) hr) f
        : ℝ → ℂ) =ᵐ[volume]
        fun ξ => mayerCoreMellinFactor (riemannMayerReflect s) (2 * Real.pi * ξ) * f ξ := by
    simpa only [frequencyOperator, ContinuousLinearMap.comp_apply,
      HTGeometry.fourierL2_fourierL2inv] using
      fourier_mayerCauchyHaarOperator_coeFn (riemannMayerReflect s) hr (HTGeometry.fourierL2inv ℝ f)
  have hcomp (f : Lp ℂ 2 (volume : Measure ℝ)) :
      frequencyOperator T
        (frequencyOperator (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs0)) f) =
      frequencyOperator (mayerCauchyHaarOperator (riemannMayerReflect s) hr) f := by
    simp only [frequencyOperator, ContinuousLinearMap.comp_apply,
      HTGeometry.fourierL2inv_fourierL2, hT]
  have h := relative_multiplier_norm_bound ha hb hA hB hcomp (t / (2 * Real.pi))
  have hscale : 2 * Real.pi * (t / (2 * Real.pi)) = t := by field_simp
  simp only [hscale, Complex.norm_conj] at h
  rw [mayerCoreReflectionFactor, norm_div, Complex.norm_conj]
  apply (div_le_iff₀ (norm_pos_iff.mpr (mayerCoreMellinFactor_ne_zero_of_re_pos s hs0 t))).mpr
  exact h.trans (mul_le_mul_of_nonneg_right (norm_frequencyOperator_le T) (norm_nonneg _))

/-- The bounded correction in physical coordinates, constructed from the source symbol. -/
def mayerCauchyReflectionCorrection (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    (hs : 1 / 4 ≤ s.re) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  HTGeometry.fourierMulCLM
    ((continuous_mayerCoreReflectionFactor s hs0 hs1).comp
      (show Continuous (fun ξ : ℝ => 2 * Real.pi * ξ) by fun_prop)).measurable
    (norm_nonneg _) (fun ξ => mayerCoreReflectionFactor_sharp_bound s hs0 hs1 hs (2 * Real.pi * ξ))

private theorem fourier_correction_ae (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    (hs : 1 / 4 ≤ s.re) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (HTGeometry.fourierL2 ℝ (mayerCauchyReflectionCorrection s hs0 hs1 hs f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => mayerCoreReflectionFactor s (2 * Real.pi * ξ) * HTGeometry.fourierL2 ℝ f ξ := by
  rw [mayerCauchyReflectionCorrection, HTGeometry.fourierMulCLM_apply,
    HTGeometry.fourierL2_fourierL2inv]
  exact lpBoundedMulCLM_coeFn _ _ _ _

/-- The source-defined correction factors reflected averaging through the actual adjoint. -/
theorem mayerCauchyReflectionCorrection_factorization (s : ℂ) (hs0 : 0 < s.re)
    (hs1 : s.re < 1 / 2) (hs : 1 / 4 ≤ s.re) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    mayerCauchyReflectionCorrection s hs0 hs1 hs
      (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs0) f) =
      mayerCauchyHaarOperator (riemannMayerReflect s)
        (by simp [riemannMayerReflect]; linarith only [hs1]) f := by
  have hr : 0 < (riemannMayerReflect s).re := by
    simp [riemannMayerReflect]; linarith only [hs1]
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change HTGeometry.fourierL2 ℝ (mayerCauchyReflectionCorrection s hs0 hs1 hs
    (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs0) f)) =
    HTGeometry.fourierL2 ℝ (mayerCauchyHaarOperator (riemannMayerReflect s) hr f)
  apply Lp.ext
  filter_upwards [fourier_correction_ae s hs0 hs1 hs
      (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs0) f),
    fourier_adjoint_mayerCauchyHaarOperator_coeFn s hs0 f,
    fourier_mayerCauchyHaarOperator_coeFn (riemannMayerReflect s) hr f] with ξ h1 h2 h3
  rw [h1, h2, h3, mayerCoreReflectionFactor, ← mul_assoc,
    div_mul_cancel₀ _ ((map_ne_zero (starRingEnd ℂ)).mpr
      (mayerCoreMellinFactor_ne_zero_of_re_pos s hs0 _))]

/-- Arbitrary bounded factorizations exist exactly on the sharp half-strip.
This statement imposes no multiplier form on the candidate operator. -/
theorem mayerCauchy_bounded_factorization_iff (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    (∃ T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      ∀ f, T (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs0) f) =
        mayerCauchyHaarOperator (riemannMayerReflect s)
          (by simp [riemannMayerReflect]; linarith only [hs1]) f) ↔ 1 / 4 ≤ s.re := by
  constructor
  · rintro ⟨T, hT⟩
    exact (mayerCoreReflectionFactor_bounded_iff s hs0 hs1).mp
      ⟨‖T‖, mayerCauchy_factorization_norm_bound s hs0 hs1 T hT⟩
  · intro hs
    exact ⟨mayerCauchyReflectionCorrection s hs0 hs1 hs,
      mayerCauchyReflectionCorrection_factorization s hs0 hs1 hs⟩

/-- Compatibility determines the correction uniquely on the entire physical space. -/
theorem mayerCauchy_factorization_unique (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    (hs : 1 / 4 ≤ s.re)
    (T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
    (hT : ∀ f, T (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs0) f) =
      mayerCauchyHaarOperator (riemannMayerReflect s)
        (by simp [riemannMayerReflect]; linarith only [hs1]) f) :
    T = mayerCauchyReflectionCorrection s hs0 hs1 hs := by
  have h := (denseRange_adjoint_mayerCauchyHaarOperator s hs0).equalizer
    T.continuous (mayerCauchyReflectionCorrection s hs0 hs1 hs).continuous
    (funext fun f => (hT f).trans (mayerCauchyReflectionCorrection_factorization s hs0 hs1 hs f).symm)
  exact ContinuousLinearMap.ext fun f => congrFun h f

/-- The forced correction has the exact attained norm of the arithmetic Gamma quotient. -/
theorem norm_mayerCauchyReflectionCorrection (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    (hs : 1 / 4 ≤ s.re) :
    ‖mayerCauchyReflectionCorrection s hs0 hs1 hs‖ = ‖mayerCoreReflectionFactor s (2 * s.im)‖ := by
  apply le_antisymm
  · exact HTGeometry.norm_fourierMulCLM_le _ _ _
  · exact mayerCauchy_factorization_norm_bound s hs0 hs1 _
      (mayerCauchyReflectionCorrection_factorization s hs0 hs1 hs) (2 * s.im)


/-- The actual averaged core in unweighted logarithmic Haar coordinates. -/
def mayerPeriodCoreLog (s : upperMayerResonances) (x : ℝ) : ℂ :=
  mayerPeriodCore s.1 (Real.exp (-x))

private theorem periodCoreLog_integrable (s : upperMayerResonances) :
    Integrable (mayerPeriodCoreLog s) := by
  have hm := (mayerPeriodCore_hasMellin_imaginary s 0).1
  simp only [Complex.ofReal_zero, zero_mul] at hm
  have hi := _root_.RHTower.integrable_logMellinPullback_of_mellinConvergent
    (mayerPeriodCore s.1) 0 hm
  change Integrable (fun x : ℝ => mayerPeriodCore s.1 (Real.exp (-x)))
  simpa only [neg_zero, zero_mul, Real.exp_zero, one_smul] using hi

private theorem periodCoreLog_bound (s : upperMayerResonances) :
    ∃ C : ℝ, ∀ x, ‖mayerPeriodCoreLog s x‖ ≤ C := by
  obtain ⟨C, N, hC, hb⟩ := upperMayerCore_two_endpoint_growth_bound
  let K := C * (1 + s.1.im) ^ N * Real.exp (Real.pi * s.1.im / 2)
  have hy := s.2.1
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, fun x => ?_⟩
  have h := hb s (Real.exp (-x)) (Real.exp_pos _)
  change ‖mayerPeriodCoreLog s x‖ ≤ K * min _ _ at h
  refine h.trans (le_trans (mul_le_mul_of_nonneg_left ?_ hK) (le_of_eq (mul_one K)))
  by_cases hx : 1 ≤ Real.exp (-x)
  · exact (min_le_left _ _).trans (inv_le_one_of_one_le₀ hx)
  · exact (min_le_right _ _).trans (Real.rpow_le_one (Real.exp_pos _).le (le_of_not_ge hx)
      (by linarith only [s.2.2.2.1]))

/-- Every actual upper-resonant PM core is unconditionally admitted on the whole Haar line. -/
theorem mayerPeriodCoreLog_memLp (s : upperMayerResonances) : MemLp (mayerPeriodCoreLog s) 2 := by
  obtain ⟨C, hC⟩ := periodCoreLog_bound s
  exact _root_.RHTower.memLp_two_of_integrable_of_norm_le (periodCoreLog_integrable s) hC

/-- The actual PM core as an element of logarithmic Haar `L²`. -/
def mayerPeriodCoreLogColumn (s : upperMayerResonances) : Lp ℂ 2 (volume : Measure ℝ) :=
  (mayerPeriodCoreLog_memLp s).toLp (mayerPeriodCoreLog s)

private theorem fourier_periodCoreLog (s : upperMayerResonances) (ξ : ℝ) :
    𝓕 (mayerPeriodCoreLog s) ξ =
      mayerCoreMellinFactor s (2 * Real.pi * ξ) * mayerFieldMellin s (2 * Real.pi * ξ) := by
  have hm := mayerPeriodCore_hasMellin_imaginary s (2 * Real.pi * ξ)
  rw [← hm.2, mellin_eq_fourier]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, mul_zero, zero_mul, sub_self, neg_zero, Real.exp_zero, one_smul,
    Complex.mul_im, mul_one, add_zero]
  rw [show 2 * Real.pi * ξ / (2 * Real.pi) = ξ by field_simp]
  rfl

private theorem fourier_field_column_ae (s : upperMayerResonances) :
    (HTGeometry.fourierL2 ℝ (mayerFieldLogColumn s) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => mayerFieldMellin s (2 * Real.pi * ξ) := by
  have hcoe : (mayerFieldLogColumn s : ℝ → ℂ) =ᵐ[volume] mayerFieldLog s :=
    (mayerFieldLog_memLp s).coeFn_toLp
  have hint : Integrable (mayerFieldLogColumn s : ℝ → ℂ) :=
    (mayerFieldLog_integrable s).congr hcoe.symm
  refine (HTGeometry.fourierL2_coeFn_ae_eq_fourier (mayerFieldLogColumn s) hint).trans ?_
  filter_upwards with ξ
  exact (Real.fourier_congr_ae hcoe ξ).trans (fourier_mayerFieldLog s ξ)

private theorem fourier_periodCore_column_ae (s : upperMayerResonances) :
    (HTGeometry.fourierL2 ℝ (mayerPeriodCoreLogColumn s) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => mayerCoreMellinFactor s (2 * Real.pi * ξ) * mayerFieldMellin s (2 * Real.pi * ξ) := by
  have hcoe : (mayerPeriodCoreLogColumn s : ℝ → ℂ) =ᵐ[volume] mayerPeriodCoreLog s :=
    (mayerPeriodCoreLog_memLp s).coeFn_toLp
  have hint : Integrable (mayerPeriodCoreLogColumn s : ℝ → ℂ) :=
    (periodCoreLog_integrable s).congr hcoe.symm
  refine (HTGeometry.fourierL2_coeFn_ae_eq_fourier (mayerPeriodCoreLogColumn s) hint).trans ?_
  filter_upwards with ξ
  exact (Real.fourier_congr_ae hcoe ξ).trans (fourier_periodCoreLog s ξ)

/-- Literal Cauchy averaging takes the actual Gamma-normalized theta field to its PM core. -/
theorem mayerCauchyHaarOperator_column (s : upperMayerResonances) :
    mayerCauchyHaarOperator s.1 s.2.2.1 (mayerFieldLogColumn s) = mayerPeriodCoreLogColumn s := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change HTGeometry.fourierL2 ℝ (mayerCauchyHaarOperator s.1 s.2.2.1 (mayerFieldLogColumn s)) =
    HTGeometry.fourierL2 ℝ (mayerPeriodCoreLogColumn s)
  apply Lp.ext
  filter_upwards [fourier_mayerCauchyHaarOperator_coeFn s.1 s.2.2.1 (mayerFieldLogColumn s),
    fourier_field_column_ae s, fourier_periodCore_column_ae s] with ξ h1 h2 h3
  rw [h1, h2, h3]

/-- The compatible physical reflection: the forced Cauchy correction after field reflection. -/
def mayerCauchyReflection (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    (hs : 1 / 4 ≤ s.re) (f : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  mayerCauchyReflectionCorrection s hs0 hs1 hs (mayerFieldReflection f)

/-- The corrected reflection is additive. -/
theorem mayerCauchyReflection_add (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    (hs : 1 / 4 ≤ s.re) (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    mayerCauchyReflection s hs0 hs1 hs (f + g) =
      mayerCauchyReflection s hs0 hs1 hs f + mayerCauchyReflection s hs0 hs1 hs g := by
  simp only [mayerCauchyReflection, mayerFieldReflection_add, map_add]

/-- The corrected reflection is conjugate-linear. -/
theorem mayerCauchyReflection_smul (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    (hs : 1 / 4 ≤ s.re) (c : ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    mayerCauchyReflection s hs0 hs1 hs (c • f) =
      conj c • mayerCauchyReflection s hs0 hs1 hs f := by
  simp only [mayerCauchyReflection, mayerFieldReflection_smul, map_smul]

/-- Its physical operator bound is the attained Gamma-quotient maximum. -/
theorem mayerCauchyReflection_norm_le (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    (hs : 1 / 4 ≤ s.re) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖mayerCauchyReflection s hs0 hs1 hs f‖ ≤ ‖mayerCoreReflectionFactor s (2 * s.im)‖ * ‖f‖ := by
  have h := (mayerCauchyReflectionCorrection s hs0 hs1 hs).le_opNorm (mayerFieldReflection f)
  simpa only [mayerCauchyReflection, norm_mayerCauchyReflectionCorrection, norm_mayerFieldReflection] using h

/-- Reflection commutes with actual averaging after reflecting its spectral parameter. -/
theorem mayerCauchyReflection_compatible (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    (hs : 1 / 4 ≤ s.re) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    mayerCauchyReflection s hs0 hs1 hs (mayerCauchyHaarOperator s hs0 f) =
      mayerCauchyHaarOperator (riemannMayerReflect s)
        (by simp [riemannMayerReflect]; linarith only [hs1]) (mayerFieldReflection f) := by
  have h := mayerFieldReflection_cauchy_adjoint s hs0 (mayerFieldReflection f)
  rw [mayerFieldReflection_involutive] at h
  rw [mayerCauchyReflection, h, mayerCauchyReflectionCorrection_factorization]

/-- The compatible bounded reflection exchanges actual PM core columns. -/
theorem mayerCauchyReflection_column (s : upperMayerResonances) (hs : 1 / 4 ≤ s.1.re) :
    mayerCauchyReflection s.1 s.2.2.1 s.2.2.2.1 hs (mayerPeriodCoreLogColumn s) =
      mayerPeriodCoreLogColumn (reflectUpperResonance s) := by
  rw [← mayerCauchyHaarOperator_column s, mayerCauchyReflection_compatible,
    mayerFieldReflection_column]
  exact mayerCauchyHaarOperator_column (reflectUpperResonance s)


private def linearizedReflection
    (R : Lp ℂ 2 (volume : Measure ℝ) → Lp ℂ 2 (volume : Measure ℝ))
    (hadd : ∀ f g, R (f + g) = R f + R g)
    (hsmul : ∀ (c : ℂ) f, R (c • f) = conj c • R f)
    (C : ℝ) (hbound : ∀ f, ‖R f‖ ≤ C * ‖f‖) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  ({ toFun := fun f => R (mayerFieldReflection f)
     map_add' := fun f g => by rw [mayerFieldReflection_add, hadd]
     map_smul' := fun c f => by
       simp only [mayerFieldReflection_smul, hsmul, starRingEnd_self_apply, RingHom.id_apply] }
    : Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ)).mkContinuous C
    (fun f => by
      change ‖R (mayerFieldReflection f)‖ ≤ C * ‖f‖
      simpa only [norm_mayerFieldReflection] using hbound (mayerFieldReflection f))

/-- An arbitrary bounded conjugate-linear reflection compatible with actual averaging exists
exactly on the sharp half-strip. No prescribed Fourier formula is imposed on the candidate. -/
theorem mayerCauchy_bounded_compatible_reflection_iff
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    (∃ R : Lp ℂ 2 (volume : Measure ℝ) → Lp ℂ 2 (volume : Measure ℝ),
      (∀ f g, R (f + g) = R f + R g) ∧
      (∀ (c : ℂ) f, R (c • f) = conj c • R f) ∧
      (∃ C : ℝ, ∀ f, ‖R f‖ ≤ C * ‖f‖) ∧
      (∀ f, R (mayerCauchyHaarOperator s hs0 f) =
        mayerCauchyHaarOperator (riemannMayerReflect s)
          (by simp [riemannMayerReflect]; linarith only [hs1]) (mayerFieldReflection f))) ↔
      1 / 4 ≤ s.re := by
  constructor
  · rintro ⟨R, hadd, hsmul, ⟨C, hbound⟩, hcompat⟩
    apply (mayerCauchy_bounded_factorization_iff s hs0 hs1).mp
    refine ⟨linearizedReflection R hadd hsmul C hbound, fun f => ?_⟩
    change R (mayerFieldReflection
      (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs0) f)) = _
    rw [← mayerFieldReflection_cauchy_adjoint s hs0 f, mayerFieldReflection_involutive,
      hcompat, mayerFieldReflection_involutive]
  · intro hs
    exact ⟨mayerCauchyReflection s hs0 hs1 hs, mayerCauchyReflection_add s hs0 hs1 hs,
      mayerCauchyReflection_smul s hs0 hs1 hs,
      ⟨‖mayerCoreReflectionFactor s (2 * s.im)‖, mayerCauchyReflection_norm_le s hs0 hs1 hs⟩,
      mayerCauchyReflection_compatible s hs0 hs1 hs⟩

/-- There is no bounded compatible reflection throughout the full source strip. -/
theorem mayerCauchy_no_full_strip_compatible_reflection :
    ¬ (∀ s : ℂ, ∀ hs0 : 0 < s.re, ∀ hs1 : s.re < 1 / 2,
      ∃ R : Lp ℂ 2 (volume : Measure ℝ) → Lp ℂ 2 (volume : Measure ℝ),
        (∀ f g, R (f + g) = R f + R g) ∧
        (∀ (c : ℂ) f, R (c • f) = conj c • R f) ∧
        (∃ C : ℝ, ∀ f, ‖R f‖ ≤ C * ‖f‖) ∧
        (∀ f, R (mayerCauchyHaarOperator s hs0 f) =
          mayerCauchyHaarOperator (riemannMayerReflect s)
            (by simp [riemannMayerReflect]; linarith only [hs1]) (mayerFieldReflection f))) := by
  intro h
  have hs0 : 0 < (((1 / 8 : ℂ) + I).re) := by norm_num
  have hs1 : (((1 / 8 : ℂ) + I).re) < 1 / 2 := by norm_num
  have hp := (mayerCauchy_bounded_compatible_reflection_iff _ hs0 hs1).mp (h _ hs0 hs1)
  norm_num at hp


/-- Source compatibility determines every bounded conjugate-linear candidate uniquely. -/
theorem mayerCauchy_compatible_reflection_unique
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) (hs : 1 / 4 ≤ s.re)
    (R : Lp ℂ 2 (volume : Measure ℝ) → Lp ℂ 2 (volume : Measure ℝ))
    (hadd : ∀ f g, R (f + g) = R f + R g)
    (hsmul : ∀ (c : ℂ) f, R (c • f) = conj c • R f)
    (C : ℝ) (hbound : ∀ f, ‖R f‖ ≤ C * ‖f‖)
    (hcompat : ∀ f, R (mayerCauchyHaarOperator s hs0 f) =
      mayerCauchyHaarOperator (riemannMayerReflect s)
        (by simp [riemannMayerReflect]; linarith only [hs1]) (mayerFieldReflection f)) :
    R = mayerCauchyReflection s hs0 hs1 hs := by
  have hT := mayerCauchy_factorization_unique s hs0 hs1 hs
    (linearizedReflection R hadd hsmul C hbound) (fun f => by
      change R (mayerFieldReflection
        (ContinuousLinearMap.adjoint (mayerCauchyHaarOperator s hs0) f)) = _
      rw [← mayerFieldReflection_cauchy_adjoint s hs0 f, mayerFieldReflection_involutive,
        hcompat, mayerFieldReflection_involutive])
  funext f
  have h := congrArg (fun T : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) =>
    T (mayerFieldReflection f)) hT
  change R (mayerFieldReflection (mayerFieldReflection f)) = mayerCauchyReflection s hs0 hs1 hs f at h
  simpa only [mayerFieldReflection_involutive] using h

private theorem norm_reflection_factor_critical (s : ℂ) (hs0 : 0 < s.re)
    (hs : s.re = 1 / 4) (t : ℝ) : ‖mayerCoreReflectionFactor s t‖ = 1 := by
  have hr : riemannMayerReflect s = s := by
    apply Complex.ext <;> norm_num [riemannMayerReflect, hs]
  rw [mayerCoreReflectionFactor, hr, norm_div, Complex.norm_conj,
    div_self ((norm_pos_iff.mpr (mayerCoreMellinFactor_ne_zero_of_re_pos s hs0 t)).ne')]

private theorem fourier_cauchy_reflection_ae (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2)
    (hs : 1 / 4 ≤ s.re) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (HTGeometry.fourierL2 ℝ (mayerCauchyReflection s hs0 hs1 hs f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (mayerCoreReflectionFactor s (2 * Real.pi * ξ) *
        mayerArithmeticMellinPhase (2 * Real.pi * ξ)) * conj (HTGeometry.fourierL2 ℝ f ξ) := by
  filter_upwards [fourier_correction_ae s hs0 hs1 hs (mayerFieldReflection f),
    fourier_field_reflection_ae f] with ξ h1 h2
  change HTGeometry.fourierL2 ℝ
    (mayerCauchyReflectionCorrection s hs0 hs1 hs (mayerFieldReflection f)) ξ = _
  rw [h1, h2]
  exact (mul_assoc _ _ _).symm

/-- On the critical line, the compatible physical reflection is an involution on all `L²`. -/
theorem mayerCauchyReflection_involutive_critical (s : ℂ) (hs0 : 0 < s.re)
    (hs1 : s.re < 1 / 2) (hs : s.re = 1 / 4) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    mayerCauchyReflection s hs0 hs1 hs.ge (mayerCauchyReflection s hs0 hs1 hs.ge f) = f := by
  apply (Lp.fourierTransformₗᵢ ℝ ℂ).injective
  change HTGeometry.fourierL2 ℝ
    (mayerCauchyReflection s hs0 hs1 hs.ge (mayerCauchyReflection s hs0 hs1 hs.ge f)) =
    HTGeometry.fourierL2 ℝ f
  apply Lp.ext
  filter_upwards [fourier_cauchy_reflection_ae s hs0 hs1 hs.ge
    (mayerCauchyReflection s hs0 hs1 hs.ge f), fourier_cauchy_reflection_ae s hs0 hs1 hs.ge f]
    with ξ h1 h2
  rw [h1, h2, map_mul, starRingEnd_self_apply, ← mul_assoc, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, norm_mul, norm_reflection_factor_critical s hs0 hs,
    norm_mayerArithmeticMellinPhase]
  simp

/-- On the critical line, actual core reflection preserves the physical Haar norm. -/
theorem norm_mayerCauchyReflection_critical (s : ℂ) (hs0 : 0 < s.re)
    (hs1 : s.re < 1 / 2) (hs : s.re = 1 / 4) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖mayerCauchyReflection s hs0 hs1 hs.ge f‖ = ‖f‖ := by
  have h1 := mayerCauchyReflection_norm_le s hs0 hs1 hs.ge f
  have h2 := mayerCauchyReflection_norm_le s hs0 hs1 hs.ge
    (mayerCauchyReflection s hs0 hs1 hs.ge f)
  rw [norm_reflection_factor_critical s hs0 hs, one_mul] at h1 h2
  rw [mayerCauchyReflection_involutive_critical s hs0 hs1 hs f] at h2
  exact le_antisymm h1 h2

#print axioms integrable_mayerCauchyHaarKernel
#print axioms fourier_mayerCauchyHaarKernel
#print axioms mayerCauchyHaarOperator_coeFn
#print axioms mayerCauchyHaarOperator_eq_fourierMultiplier
#print axioms injective_mayerCauchyHaarOperator
#print axioms mayerFieldReflection_cauchy_adjoint
#print axioms denseRange_mayerCauchyHaarOperator
#print axioms mayerCauchy_bounded_factorization_iff
#print axioms mayerCauchy_factorization_unique
#print axioms norm_mayerCauchyReflectionCorrection
#print axioms mayerPeriodCoreLog_memLp
#print axioms mayerCauchyHaarOperator_column
#print axioms mayerCauchyReflection_compatible
#print axioms mayerCauchyReflection_column
#print axioms mayerCauchy_bounded_compatible_reflection_iff
#print axioms mayerCauchy_no_full_strip_compatible_reflection
#print axioms mayerCauchy_compatible_reflection_unique
#print axioms mayerCauchyReflection_involutive_critical
#print axioms norm_mayerCauchyReflection_critical

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerScattering
