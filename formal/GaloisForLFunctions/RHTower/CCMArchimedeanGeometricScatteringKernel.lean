import GaloisForLFunctions.RHTower.CCMArchimedeanFourierMellinScattering

/-!
# Literal geometric kernel of the CCM archimedean scattering phase

This module proves Connes--Consani's geometric realization of the archimedean scattering
operator.  It first transports the exact Fourier--Mellin scattering identity to
`L²(ℝ₊*, d*λ)`, then identifies its action on a dense normalized even-Schwartz core with
the literal Haar integral kernel

`kᵘ(λ,μ) = 2 λ⁻¹˲ μ¹˲ cos(2π μ/λ)`.

No kernel representation, transform identity, integrability, or density premise occurs in the
endpoint theorem.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace FourierTransform SchwartzMap

noncomputable section

namespace RHTower

abbrev CCMMultiplicativeL2 := Lp ℂ 2 MellinL2.multiplicativeHaar

/-- Multiplicative inversion, transported from reflection in logarithmic coordinates. -/
def ccmMultiplicativeInversion : CCMMultiplicativeL2 →L[ℂ] CCMMultiplicativeL2 :=
  MellinL2.expPullbackUnitary.symm.toLinearIsometry.toContinuousLinearMap ∘L
    l2Reflection ∘L
      MellinL2.expPullbackUnitary.toLinearIsometry.toContinuousLinearMap

theorem expPullbackUnitary_ccmMultiplicativeInversion (f : CCMMultiplicativeL2) :
    MellinL2.expPullbackUnitary (ccmMultiplicativeInversion f) =
      l2Reflection (MellinL2.expPullbackUnitary f) := by
  change MellinL2.expPullbackUnitary
      (MellinL2.expPullbackUnitary.symm
        (l2Reflection (MellinL2.expPullbackUnitary f))) = _
  rw [MellinL2.expPullbackUnitary.apply_symm_apply]

theorem mellinUnitary_ccmMultiplicativeInversion (f : CCMMultiplicativeL2) :
    MellinL2.mellinUnitary (ccmMultiplicativeInversion f) =
      l2Reflection (MellinL2.mellinUnitary f) := by
  change dilationUnitary MellinL2.spectralNormalization
      MellinL2.spectralNormalization_pos
      (fourierUnitary
        (MellinL2.expPullbackUnitary (ccmMultiplicativeInversion f))) = _
  rw [expPullbackUnitary_ccmMultiplicativeInversion,
    fourierUnitary_l2Reflection]
  change dilation MellinL2.spectralNormalization
      MellinL2.spectralNormalization_pos
      (l2Reflection (fourierUnitary (MellinL2.expPullbackUnitary f))) =
    l2Reflection
      (dilation MellinL2.spectralNormalization
        MellinL2.spectralNormalization_pos
        (fourierUnitary (MellinL2.expPullbackUnitary f)))
  rw [l2Reflection_dilation]

/-- Multiplicative-Haar geometric realization of the CCM scattering phase. -/
def ccmArchimedeanGeometricScattering :
    CCMMultiplicativeL2 →L[ℂ] CCMMultiplicativeL2 :=
  MellinL2.mellinUnitary.symm.toLinearIsometry.toContinuousLinearMap ∘L
    ccmArchimedeanScatteringL2Multiplier ∘L
      MellinL2.mellinUnitary.toLinearIsometry.toContinuousLinearMap

theorem ccmArchimedeanGeometricScattering_eq_inversion_fourier
    (f : CCMMultiplicativeL2) :
    ccmArchimedeanGeometricScattering f =
      ccmMultiplicativeInversion
        (evenToMultiplicativeHaarUnitary
          (evenFourierTransform (evenToMultiplicativeHaarUnitary.symm f))) := by
  apply MellinL2.mellinUnitary.injective
  change MellinL2.mellinUnitary
      (MellinL2.mellinUnitary.symm
        (ccmArchimedeanScatteringL2Multiplier (MellinL2.mellinUnitary f))) = _
  rw [MellinL2.mellinUnitary.apply_symm_apply]
  rw [mellinUnitary_ccmMultiplicativeInversion]
  change ccmArchimedeanScatteringL2Multiplier (MellinL2.mellinUnitary f) =
    l2Reflection
      (archimedeanMellinUnitary
        (evenFourierTransform (evenToMultiplicativeHaarUnitary.symm f)))
  rw [archimedeanMellinUnitary_evenFourierTransform,
    l2Reflection_involutive]
  have hm : archimedeanMellinUnitary (evenToMultiplicativeHaarUnitary.symm f) =
      MellinL2.mellinUnitary f := by
    change MellinL2.mellinUnitary
        (evenToMultiplicativeHaarUnitary
          (evenToMultiplicativeHaarUnitary.symm f)) = MellinL2.mellinUnitary f
    rw [evenToMultiplicativeHaarUnitary.apply_symm_apply]
  rw [hm]

/-- Dense multiplicative-Haar source obtained from an even Schwartz function. -/
def ccmMultiplicativeSchwartzSource (g : SchwartzMap ℝ ℂ) : CCMMultiplicativeL2 :=
  evenToMultiplicativeHaarUnitary (ccmEvenSchwartzSource g)

theorem ccmMultiplicativeSchwartzSource_denseRange :
    DenseRange ccmMultiplicativeSchwartzSource :=
  evenToMultiplicativeHaarUnitary.surjective.denseRange.comp
    ccmEvenSchwartzSource_denseRange evenToMultiplicativeHaarUnitary.continuous

/-- Canonical pointwise representative of the normalized `w∞` image of an even Schwartz
function. -/
def ccmMultiplicativeSchwartzDensity (g : SchwartzMap ℝ ℂ)
    (mu : MellinL2.PosReal) : ℂ :=
  (((Real.sqrt 2 * Real.sqrt (mu : ℝ) : ℝ) : ℂ) * schwartzEvenPart g (mu : ℝ))

theorem expPullback_ccmMultiplicativeSchwartzSource (g : SchwartzMap ℝ ℂ) :
    MellinL2.expPullbackUnitary (ccmMultiplicativeSchwartzSource g) =
      logEvenUnitary (ccmEvenSchwartzSource g) := by
  simp [ccmMultiplicativeSchwartzSource, evenToMultiplicativeHaarUnitary]

theorem ccmMultiplicativeSchwartzSource_ae_exp (g : SchwartzMap ℝ ℂ) :
    (((ccmMultiplicativeSchwartzSource g : CCMMultiplicativeL2) :
        MellinL2.PosReal → ℂ) ∘ MellinL2.expMeasurableEquiv) =ᵐ[volume]
      ccmMultiplicativeSchwartzDensity g ∘ MellinL2.expMeasurableEquiv := by
  have hpull := Lp.coeFn_compMeasurePreserving
    (ccmMultiplicativeSchwartzSource g) MellinL2.exp_measurePreserving
  have hlog := logEvenUnitary_ae (ccmEvenSchwartzSource g)
  have hsource := (ccmEvenSchwartzSource_coeFn g).comp_tendsto
    realExp_quasiMeasurePreserving.tendsto_ae
  filter_upwards [hpull, hlog, hsource] with t hpull_t hlog_t hsource_t
  change (ccmMultiplicativeSchwartzSource g : CCMMultiplicativeL2)
      (MellinL2.expMeasurableEquiv t) =
        ccmMultiplicativeSchwartzDensity g (MellinL2.expMeasurableEquiv t)
  calc
    (ccmMultiplicativeSchwartzSource g : CCMMultiplicativeL2)
        (MellinL2.expMeasurableEquiv t) =
        MellinL2.expPullbackUnitary (ccmMultiplicativeSchwartzSource g) t :=
      hpull_t.symm
    _ = logEvenUnitary (ccmEvenSchwartzSource g) t :=
      congrArg (fun q : SoninL2 => q t)
        (expPullback_ccmMultiplicativeSchwartzSource g)
    _ = (((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ) *
        ((ccmEvenSchwartzSource g : evenSubspace) : SoninL2) (Real.exp t)) := hlog_t
    _ = (((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ) *
        schwartzEvenPart g (Real.exp t)) := by
      have hsource_t' :
          ((ccmEvenSchwartzSource g : evenSubspace) : SoninL2) (Real.exp t) =
            schwartzEvenPart g (Real.exp t) := by
        simpa only [Function.comp_apply] using hsource_t
      rw [hsource_t']
    _ = ccmMultiplicativeSchwartzDensity g (MellinL2.expMeasurableEquiv t) := by
      unfold ccmMultiplicativeSchwartzDensity
      change (((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ) * schwartzEvenPart g (Real.exp t)) =
        (((Real.sqrt 2 * Real.sqrt (Real.exp t) : ℝ) : ℂ) *
          schwartzEvenPart g (Real.exp t))
      rw [Real.exp_half]

theorem ccmMultiplicativeSchwartzSource_ae (g : SchwartzMap ℝ ℂ) :
    ((ccmMultiplicativeSchwartzSource g : CCMMultiplicativeL2) :
        MellinL2.PosReal → ℂ) =ᵐ[MellinL2.multiplicativeHaar]
      ccmMultiplicativeSchwartzDensity g := by
  have h := (ccmMultiplicativeSchwartzSource_ae_exp g).comp_tendsto
    MellinL2.exp_measurePreserving.symm.quasiMeasurePreserving.tendsto_ae
  filter_upwards [h] with mu hmu
  simpa only [Function.comp_apply, MellinL2.expMeasurableEquiv.apply_symm_apply] using hmu

/-! ## Cosine form of the even Fourier transform -/

theorem integrable_mul_fourierCos (g : SchwartzMap ℝ ℂ) (w : ℝ) :
    Integrable (fun x : ℝ =>
      g x * ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ)) := by
  apply g.integrable.mul_bdd (c := 1)
  · fun_prop
  · filter_upwards with x
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      (abs_cos_le_one (2 * Real.pi * w * x))

theorem schwartz_integral_mul_cos_eq_fourier_avg
    (g : SchwartzMap ℝ ℂ) (w : ℝ) :
    (∫ x : ℝ, g x * (Real.cos (2 * Real.pi * w * x) : ℂ)) =
      (2 : ℂ)⁻¹ * 𝓕 (g : ℝ → ℂ) w +
        (2 : ℂ)⁻¹ * 𝓕 (g : ℝ → ℂ) (-w) := by
  have hE1 : Integrable (fun x : ℝ =>
      (2 : ℂ)⁻¹ * (Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) * g x)) := by
    refine (g.integrable.bdd_mul (c := 1) ?_ ?_).const_mul _
    · fun_prop
    · filter_upwards with x
      rw [Complex.norm_exp]
      simp
  have hE2 : Integrable (fun x : ℝ =>
      (2 : ℂ)⁻¹ * (Complex.exp (((-2 * Real.pi * x * -w : ℝ) : ℂ) * Complex.I) * g x)) := by
    refine (g.integrable.bdd_mul (c := 1) ?_ ?_).const_mul _
    · fun_prop
    · filter_upwards with x
      rw [Complex.norm_exp]
      simp
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add hE1 hE2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have key : ∀ z : ℂ, (2 : ℂ)⁻¹ * Complex.exp (z * Complex.I) +
      (2 : ℂ)⁻¹ * Complex.exp (-z * Complex.I) = Complex.cos z := by
    intro z
    rw [Complex.cos]
    ring
  have h1 : (((-2 * Real.pi * x * -w : ℝ) : ℂ)) =
      ((2 * Real.pi * w * x : ℝ) : ℂ) := by
    push_cast
    ring
  have h2 : (((-2 * Real.pi * x * w : ℝ) : ℂ)) =
      -((2 * Real.pi * w * x : ℝ) : ℂ) := by
    push_cast
    ring
  have hcos : ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ) =
      (2 : ℂ)⁻¹ * Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) +
        (2 : ℂ)⁻¹ * Complex.exp (((-2 * Real.pi * x * -w : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_cos, h1, h2, add_comm,
      ← key (((2 * Real.pi * w * x : ℝ) : ℂ))]
  change g x * ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ) =
    (2 : ℂ)⁻¹ * (Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) * g x) +
      (2 : ℂ)⁻¹ * (Complex.exp (((-2 * Real.pi * x * -w : ℝ) : ℂ) * Complex.I) * g x)
  rw [hcos]
  ring

theorem evenSchwartz_fourier_eq_two_mul_integral_Ioi_cos
    (g : SchwartzMap ℝ ℂ) (w : ℝ) :
    𝓕 (schwartzEvenPart g : ℝ → ℂ) w =
      2 * ∫ x in Ioi (0 : ℝ),
        schwartzEvenPart g x * (Real.cos (2 * Real.pi * w * x) : ℂ) := by
  let f : SchwartzMap ℝ ℂ := schwartzEvenPart g
  have heven : ∀ x : ℝ, f (-x) = f x := schwartzEvenPart_even g
  have hproductEven : ∀ x : ℝ,
      f (-x) * (Real.cos (2 * Real.pi * w * (-x)) : ℂ) =
        f x * (Real.cos (2 * Real.pi * w * x) : ℂ) := by
    intro x
    rw [heven, show 2 * Real.pi * w * -x = -(2 * Real.pi * w * x) by ring,
      Real.cos_neg]
  have hsplit := integral_eq_two_mul_integral_Ioi_of_even
    (integrable_mul_fourierCos f w) hproductEven
  have havg := schwartz_integral_mul_cos_eq_fourier_avg f w
  have hFeven := fourier_even_of_even heven w
  change (𝓕 (f : ℝ → ℂ)) w = _
  rw [hFeven] at havg
  calc
    (𝓕 (f : ℝ → ℂ)) w =
        (2 : ℂ)⁻¹ * (𝓕 (f : ℝ → ℂ)) w +
          (2 : ℂ)⁻¹ * (𝓕 (f : ℝ → ℂ)) w := by ring
    _ = ∫ x : ℝ, f x * (Real.cos (2 * Real.pi * w * x) : ℂ) := havg.symm
    _ = 2 * ∫ x in Ioi (0 : ℝ),
        f x * (Real.cos (2 * Real.pi * w * x) : ℂ) := hsplit

/-! ## Literal kernel and its convergent action -/

/-- Connes--Consani's literal geometric kernel
`kᵘ(λ,μ)=2λ⁻¹˲μ¹˲ cos(2πμ/λ)`. -/
def ccmArchimedeanGeometricScatteringKernel
    (lam mu : MellinL2.PosReal) : ℂ :=
  (2 : ℂ) * ((Real.sqrt (lam : ℝ))⁻¹ : ℝ) * Real.sqrt (mu : ℝ) *
    Real.cos (2 * Real.pi * ((mu : ℝ) / (lam : ℝ)))

/-- Literal Haar-kernel action on the canonical dense Schwartz source. -/
def ccmArchimedeanGeometricKernelAction
    (g : SchwartzMap ℝ ℂ) (lam : MellinL2.PosReal) : ℂ :=
  ∫ mu : MellinL2.PosReal,
    ccmArchimedeanGeometricScatteringKernel lam mu *
      ccmMultiplicativeSchwartzDensity g mu ∂MellinL2.multiplicativeHaar

theorem continuous_ccmArchimedeanGeometricKernelIntegrand
    (g : SchwartzMap ℝ ℂ) (lam : MellinL2.PosReal) :
    Continuous (fun mu : MellinL2.PosReal =>
      ccmArchimedeanGeometricScatteringKernel lam mu *
        ccmMultiplicativeSchwartzDensity g mu) := by
  unfold ccmArchimedeanGeometricScatteringKernel ccmMultiplicativeSchwartzDensity
  fun_prop

theorem ccmArchimedeanGeometricKernelIntegrand_exp
    (g : SchwartzMap ℝ ℂ) (lam : MellinL2.PosReal) (t : ℝ) :
    ccmArchimedeanGeometricScatteringKernel lam (MellinL2.expMeasurableEquiv t) *
        ccmMultiplicativeSchwartzDensity g (MellinL2.expMeasurableEquiv t) =
      (((2 * Real.sqrt 2 * (Real.sqrt (lam : ℝ))⁻¹ : ℝ) : ℂ) *
        (Real.exp t • (schwartzEvenPart g (Real.exp t) *
          ((Real.cos (2 * Real.pi * (lam : ℝ)⁻¹ * Real.exp t) : ℝ) : ℂ)))) := by
  change
    ((2 : ℂ) * ((Real.sqrt (lam : ℝ))⁻¹ : ℝ) * Real.sqrt (Real.exp t) *
      Real.cos (2 * Real.pi * (Real.exp t / (lam : ℝ))) *
        (((Real.sqrt 2 * Real.sqrt (Real.exp t) : ℝ) : ℂ) *
          schwartzEvenPart g (Real.exp t))) =
    (((2 * Real.sqrt 2 * (Real.sqrt (lam : ℝ))⁻¹ : ℝ) : ℂ) *
      (Real.exp t • (schwartzEvenPart g (Real.exp t) *
        ((Real.cos (2 * Real.pi * (lam : ℝ)⁻¹ * Real.exp t) : ℝ) : ℂ))))
  rw [div_eq_inv_mul]
  simp only [Complex.real_smul]
  have hsqrt : Real.sqrt (Real.exp t) * Real.sqrt (Real.exp t) = Real.exp t := by
    rw [← pow_two, Real.sq_sqrt (Real.exp_pos t).le]
  have hsqrtC :
      (((Real.sqrt (Real.exp t) : ℝ) : ℂ) * ((Real.sqrt (Real.exp t) : ℝ) : ℂ)) =
        ((Real.exp t : ℝ) : ℂ) := by
    exact_mod_cast hsqrt
  calc
    _ = (((2 * Real.sqrt 2 * (Real.sqrt (lam : ℝ))⁻¹ : ℝ) : ℂ) *
        (((Real.sqrt (Real.exp t) : ℝ) : ℂ) * ((Real.sqrt (Real.exp t) : ℝ) : ℂ)) *
          (schwartzEvenPart g (Real.exp t) *
            ((Real.cos (2 * Real.pi * (lam : ℝ)⁻¹ * Real.exp t) : ℝ) : ℂ))) := by
      push_cast
      ring
    _ = _ := by
      rw [hsqrtC]
      ring

theorem integrable_ccmArchimedeanGeometricKernelIntegrand
    (g : SchwartzMap ℝ ℂ) (lam : MellinL2.PosReal) :
    Integrable (fun mu : MellinL2.PosReal =>
      ccmArchimedeanGeometricScatteringKernel lam mu *
        ccmMultiplicativeSchwartzDensity g mu)
      MellinL2.multiplicativeHaar := by
  rw [← MellinL2.exp_measurePreserving.integrable_comp
    (continuous_ccmArchimedeanGeometricKernelIntegrand g lam).aestronglyMeasurable]
  have hhalf : IntegrableOn (fun x : ℝ =>
      schwartzEvenPart g x *
        (Real.cos (2 * Real.pi * ((lam : ℝ))⁻¹ * x) : ℂ)) (Ioi 0) :=
    (integrable_mul_fourierCos (schwartzEvenPart g) ((lam : ℝ))⁻¹).integrableOn
  have hlog := (integrableOn_Ioi_iff_integrable_exp_smul _).mp hhalf
  have hscaled := hlog.const_mul
    (((2 * Real.sqrt 2 * (Real.sqrt (lam : ℝ))⁻¹ : ℝ) : ℂ))
  exact hscaled.congr (Filter.Eventually.of_forall fun t =>
    (ccmArchimedeanGeometricKernelIntegrand_exp g lam t).symm)

theorem ccmArchimedeanGeometricKernelAction_eq_halfline
    (g : SchwartzMap ℝ ℂ) (lam : MellinL2.PosReal) :
    ccmArchimedeanGeometricKernelAction g lam =
      (((2 * Real.sqrt 2 * (Real.sqrt (lam : ℝ))⁻¹ : ℝ) : ℂ) *
        ∫ x in Ioi (0 : ℝ), schwartzEvenPart g x *
          ((Real.cos (2 * Real.pi * (lam : ℝ)⁻¹ * x) : ℝ) : ℂ)) := by
  unfold ccmArchimedeanGeometricKernelAction
  rw [← MellinL2.exp_measurePreserving.integral_comp']
  calc
    (∫ t : ℝ,
        ccmArchimedeanGeometricScatteringKernel lam (MellinL2.expMeasurableEquiv t) *
          ccmMultiplicativeSchwartzDensity g (MellinL2.expMeasurableEquiv t)) =
        ∫ t : ℝ,
          ((2 * Real.sqrt 2 * (Real.sqrt (lam : ℝ))⁻¹ : ℝ) : ℂ) *
            (Real.exp t • (schwartzEvenPart g (Real.exp t) *
              ((Real.cos (2 * Real.pi * (lam : ℝ)⁻¹ * Real.exp t) : ℝ) : ℂ))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (ccmArchimedeanGeometricKernelIntegrand_exp g lam)
    _ = (((2 * Real.sqrt 2 * (Real.sqrt (lam : ℝ))⁻¹ : ℝ) : ℂ) *
        ∫ t : ℝ, Real.exp t • (schwartzEvenPart g (Real.exp t) *
          ((Real.cos (2 * Real.pi * (lam : ℝ)⁻¹ * Real.exp t) : ℝ) : ℂ))) := by
      rw [integral_const_mul]
    _ = _ := by
      rw [integral_Ioi_eq_integral_exp_smul]

theorem ccmArchimedeanGeometricKernelAction_eq_fourier
    (g : SchwartzMap ℝ ℂ) (lam : MellinL2.PosReal) :
    ccmArchimedeanGeometricKernelAction g lam =
      ((Real.sqrt 2 * (Real.sqrt (lam : ℝ))⁻¹ : ℝ) : ℂ) *
        𝓕 (schwartzEvenPart g : ℝ → ℂ) ((lam : ℝ)⁻¹) := by
  rw [ccmArchimedeanGeometricKernelAction_eq_halfline,
    evenSchwartz_fourier_eq_two_mul_integral_Ioi_cos]
  push_cast
  ring

/-! ## Identification with the actual L² scattering operator -/

/-- Point inversion on the multiplicative positive line. -/
def ccmMultiplicativePointInversion (mu : MellinL2.PosReal) : MellinL2.PosReal :=
  MellinL2.expMeasurableEquiv
    (-(MellinL2.expMeasurableEquiv.symm mu))

theorem coe_ccmMultiplicativePointInversion (mu : MellinL2.PosReal) :
    (ccmMultiplicativePointInversion mu : ℝ) = (mu : ℝ)⁻¹ := by
  have hexp : Real.exp (MellinL2.expMeasurableEquiv.symm mu) = (mu : ℝ) := by
    exact congrArg Subtype.val (MellinL2.expMeasurableEquiv.apply_symm_apply mu)
  unfold ccmMultiplicativePointInversion
  change Real.exp (-(MellinL2.expMeasurableEquiv.symm mu)) = (mu : ℝ)⁻¹
  rw [Real.exp_neg, hexp]

theorem ccmMultiplicativePointInversion_exp (t : ℝ) :
    ccmMultiplicativePointInversion (MellinL2.expMeasurableEquiv t) =
      MellinL2.expMeasurableEquiv (-t) := by
  unfold ccmMultiplicativePointInversion
  rw [MellinL2.expMeasurableEquiv.symm_apply_apply]

theorem ccmMultiplicativePointInversion_measurePreserving :
    MeasurePreserving ccmMultiplicativePointInversion
      MellinL2.multiplicativeHaar MellinL2.multiplicativeHaar := by
  have hcomp := MellinL2.exp_measurePreserving.comp
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).comp
      MellinL2.exp_measurePreserving.symm)
  change MeasurePreserving
    (MellinL2.expMeasurableEquiv ∘ Neg.neg ∘ MellinL2.expMeasurableEquiv.symm)
      MellinL2.multiplicativeHaar MellinL2.multiplicativeHaar
  exact hcomp

theorem ccmMultiplicativeInversion_ae_exp (f : CCMMultiplicativeL2) :
    (fun t : ℝ =>
      ccmMultiplicativeInversion f (MellinL2.expMeasurableEquiv t)) =ᵐ[volume]
        fun t : ℝ => f (MellinL2.expMeasurableEquiv (-t)) := by
  have hout := Lp.coeFn_compMeasurePreserving
    (ccmMultiplicativeInversion f) MellinL2.exp_measurePreserving
  have href := l2Reflection_ae (MellinL2.expPullbackUnitary f)
  have hin := (Lp.coeFn_compMeasurePreserving f MellinL2.exp_measurePreserving).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [hout, href, hin] with t hout_t href_t hin_t
  calc
    ccmMultiplicativeInversion f (MellinL2.expMeasurableEquiv t) =
        MellinL2.expPullbackUnitary (ccmMultiplicativeInversion f) t := hout_t.symm
    _ = l2Reflection (MellinL2.expPullbackUnitary f) t :=
      congrArg (fun q : SoninL2 => q t)
        (expPullbackUnitary_ccmMultiplicativeInversion f)
    _ = MellinL2.expPullbackUnitary f (-t) := href_t
    _ = f (MellinL2.expMeasurableEquiv (-t)) := by
      change (Lp.compMeasurePreserving MellinL2.expMeasurableEquiv
        MellinL2.exp_measurePreserving f) (-t) = _
      simpa only [Function.comp_apply] using hin_t

theorem ccmMultiplicativeInversion_ae (f : CCMMultiplicativeL2) :
    ((ccmMultiplicativeInversion f : CCMMultiplicativeL2) :
        MellinL2.PosReal → ℂ) =ᵐ[MellinL2.multiplicativeHaar]
      fun mu => f (ccmMultiplicativePointInversion mu) := by
  have h := (ccmMultiplicativeInversion_ae_exp f).comp_tendsto
    MellinL2.exp_measurePreserving.symm.quasiMeasurePreserving.tendsto_ae
  filter_upwards [h] with mu hmu
  simpa only [Function.comp_apply, MellinL2.expMeasurableEquiv.apply_symm_apply,
    ccmMultiplicativePointInversion] using hmu

theorem ccmMultiplicativeSchwartzDensity_fourier_inversion_eq_kernelAction
    (g : SchwartzMap ℝ ℂ) (lam : MellinL2.PosReal) :
    ccmMultiplicativeSchwartzDensity (𝓕 g)
        (ccmMultiplicativePointInversion lam) =
      ccmArchimedeanGeometricKernelAction g lam := by
  rw [ccmArchimedeanGeometricKernelAction_eq_fourier]
  unfold ccmMultiplicativeSchwartzDensity
  rw [coe_ccmMultiplicativePointInversion, Real.sqrt_inv,
    ← fourier_schwartzEvenPart]
  simp only [SchwartzMap.fourier_coe]

theorem ccmArchimedeanGeometricScattering_schwartzSource_eq_inversion_fourier
    (g : SchwartzMap ℝ ℂ) :
    ccmArchimedeanGeometricScattering (ccmMultiplicativeSchwartzSource g) =
      ccmMultiplicativeInversion (ccmMultiplicativeSchwartzSource (𝓕 g)) := by
  rw [ccmArchimedeanGeometricScattering_eq_inversion_fourier]
  rw [show evenToMultiplicativeHaarUnitary.symm
      (ccmMultiplicativeSchwartzSource g) = ccmEvenSchwartzSource g by
    simp [ccmMultiplicativeSchwartzSource]]
  rw [ccmEvenSchwartzSource_fourier]
  rfl

/-- Exact almost-everywhere kernel representation on the canonical dense core. -/
theorem ccmArchimedeanGeometricScattering_has_literal_kernel
    (g : SchwartzMap ℝ ℂ) :
    ((ccmArchimedeanGeometricScattering (ccmMultiplicativeSchwartzSource g) :
        CCMMultiplicativeL2) : MellinL2.PosReal → ℂ) =ᵐ[MellinL2.multiplicativeHaar]
      ccmArchimedeanGeometricKernelAction g := by
  have hinv := ccmMultiplicativeInversion_ae
    (ccmMultiplicativeSchwartzSource (𝓕 g))
  have hsource := (ccmMultiplicativeSchwartzSource_ae (𝓕 g)).comp_tendsto
    ccmMultiplicativePointInversion_measurePreserving.quasiMeasurePreserving.tendsto_ae
  filter_upwards [hinv, hsource] with lam hinv_lam hsource_lam
  rw [ccmArchimedeanGeometricScattering_schwartzSource_eq_inversion_fourier]
  rw [hinv_lam]
  have hsource_lam' : ccmMultiplicativeSchwartzSource (𝓕 g)
      (ccmMultiplicativePointInversion lam) =
        ccmMultiplicativeSchwartzDensity (𝓕 g)
          (ccmMultiplicativePointInversion lam) := by
    simpa only [Function.comp_apply] using hsource_lam
  rw [hsource_lam',
    ccmMultiplicativeSchwartzDensity_fourier_inversion_eq_kernelAction]

/-- Published kernel formula written directly against the actual `L²` source representative:
the scattering operator is the integral operator with kernel
`2 / sqrt(λ) * sqrt(μ) * cos(2πμ/λ)` on a dense domain. -/
theorem ccmArchimedeanGeometricScattering_literal_kernel_formula
    (g : SchwartzMap ℝ ℂ) :
    ((ccmArchimedeanGeometricScattering (ccmMultiplicativeSchwartzSource g) :
        CCMMultiplicativeL2) : MellinL2.PosReal → ℂ) =ᵐ[MellinL2.multiplicativeHaar]
      fun lam => ∫ mu : MellinL2.PosReal,
        ccmArchimedeanGeometricScatteringKernel lam mu *
          ccmMultiplicativeSchwartzSource g mu
          ∂MellinL2.multiplicativeHaar := by
  filter_upwards [ccmArchimedeanGeometricScattering_has_literal_kernel g] with lam hlam
  rw [hlam]
  unfold ccmArchimedeanGeometricKernelAction
  apply integral_congr_ae
  filter_upwards [ccmMultiplicativeSchwartzSource_ae g] with mu hmu
  rw [hmu]

end RHTower
