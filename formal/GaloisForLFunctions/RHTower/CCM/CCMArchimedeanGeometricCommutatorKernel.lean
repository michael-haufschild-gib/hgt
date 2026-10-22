import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanGeometricScatteringKernel
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanQuantizedCalculus

/-!
# Geometric kernel of the CCM sharp-projection commutator

This module proves Connes--Consani Lemma `sch3(ii)`.  The sharp multiplier
`P(v)=1` for `v≥1` and `P(v)=0` otherwise is constructed on multiplicative-Haar `L²`.
The commutator with the archimedean geometric scattering operator has literal kernel

`(P(λ)-P(μ)) kᵘ(λ,μ)`.

To handle the discontinuous input `Pξ` without assuming a kernel interface, the proof first
extends the geometric kernel theorem from Schwartz functions to the full even `L¹∩L²` core.
The published endpoint is then instantiated on every normalized even-Schwartz source and has no
analytic, kernel, or transform premise.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace FourierTransform SchwartzMap

noncomputable section

namespace RHTower

/-! ## Even L¹∩L² kernel core -/

/-- Pointwise even functions carrying exactly the integrability needed for the literal kernel. -/
structure CCMEvenL1L2Source where
  toFun : ℝ → ℂ
  integrable : Integrable toFun
  memLp_two : MemLp toFun 2 (volume : Measure ℝ)
  even : ∀ x : ℝ, toFun (-x) = toFun x

instance : CoeFun CCMEvenL1L2Source (fun _ => ℝ → ℂ) :=
  ⟨CCMEvenL1L2Source.toFun⟩

def CCMEvenL1L2Source.toEvenSubspace (f : CCMEvenL1L2Source) : evenSubspace :=
  ⟨f.memLp_two.toLp f,
    memLp_toLp_mem_evenSubspace f.memLp_two f.even⟩

def CCMEvenL1L2Source.toMultiplicativeL2
    (f : CCMEvenL1L2Source) : CCMMultiplicativeL2 :=
  evenToMultiplicativeHaarUnitary f.toEvenSubspace

def CCMEvenL1L2Source.multiplicativeDensity
    (f : CCMEvenL1L2Source) (mu : MellinL2.PosReal) : ℂ :=
  (((Real.sqrt 2 * Real.sqrt (mu : ℝ) : ℝ) : ℂ) * f (mu : ℝ))

theorem CCMEvenL1L2Source.coeFn_toEvenSubspace (f : CCMEvenL1L2Source) :
    (((f.toEvenSubspace : evenSubspace) : SoninL2) : ℝ → ℂ) =ᵐ[volume] f :=
  f.memLp_two.coeFn_toLp

theorem CCMEvenL1L2Source.expPullback_toMultiplicativeL2
    (f : CCMEvenL1L2Source) :
    MellinL2.expPullbackUnitary f.toMultiplicativeL2 =
      logEvenUnitary f.toEvenSubspace := by
  simp [CCMEvenL1L2Source.toMultiplicativeL2,
    evenToMultiplicativeHaarUnitary]

theorem CCMEvenL1L2Source.toMultiplicativeL2_ae_exp
    (f : CCMEvenL1L2Source) :
    (((f.toMultiplicativeL2 : CCMMultiplicativeL2) : MellinL2.PosReal → ℂ) ∘
        MellinL2.expMeasurableEquiv) =ᵐ[volume]
      f.multiplicativeDensity ∘ MellinL2.expMeasurableEquiv := by
  have hpull := Lp.coeFn_compMeasurePreserving
    f.toMultiplicativeL2 MellinL2.exp_measurePreserving
  have hlog := logEvenUnitary_ae f.toEvenSubspace
  have hsource := f.coeFn_toEvenSubspace.comp_tendsto
    realExp_quasiMeasurePreserving.tendsto_ae
  filter_upwards [hpull, hlog, hsource] with t hpull_t hlog_t hsource_t
  change f.toMultiplicativeL2 (MellinL2.expMeasurableEquiv t) =
    f.multiplicativeDensity (MellinL2.expMeasurableEquiv t)
  calc
    f.toMultiplicativeL2 (MellinL2.expMeasurableEquiv t) =
        MellinL2.expPullbackUnitary f.toMultiplicativeL2 t := hpull_t.symm
    _ = logEvenUnitary f.toEvenSubspace t :=
      congrArg (fun q : SoninL2 => q t) f.expPullback_toMultiplicativeL2
    _ = (((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ) *
        ((f.toEvenSubspace : evenSubspace) : SoninL2) (Real.exp t)) := hlog_t
    _ = (((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ) * f (Real.exp t)) := by
      have hsource_t' :
          ((f.toEvenSubspace : evenSubspace) : SoninL2) (Real.exp t) =
            f (Real.exp t) := by
        simpa only [Function.comp_apply] using hsource_t
      rw [hsource_t']
    _ = f.multiplicativeDensity (MellinL2.expMeasurableEquiv t) := by
      unfold CCMEvenL1L2Source.multiplicativeDensity
      change (((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ) * f (Real.exp t)) =
        (((Real.sqrt 2 * Real.sqrt (Real.exp t) : ℝ) : ℂ) * f (Real.exp t))
      rw [Real.exp_half]

theorem CCMEvenL1L2Source.toMultiplicativeL2_ae
    (f : CCMEvenL1L2Source) :
    ((f.toMultiplicativeL2 : CCMMultiplicativeL2) : MellinL2.PosReal → ℂ) =ᵐ[
        MellinL2.multiplicativeHaar] f.multiplicativeDensity := by
  have h := f.toMultiplicativeL2_ae_exp.comp_tendsto
    MellinL2.exp_measurePreserving.symm.quasiMeasurePreserving.tendsto_ae
  filter_upwards [h] with mu hmu
  simpa only [Function.comp_apply, MellinL2.expMeasurableEquiv.apply_symm_apply] using hmu

theorem integral_mul_cos_eq_fourier_avg_of_integrable
    (f : ℝ → ℂ) (hf : Integrable f) (w : ℝ) :
    (∫ x : ℝ, f x * ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ)) =
      (2 : ℂ)⁻¹ * 𝓕 f w + (2 : ℂ)⁻¹ * 𝓕 f (-w) := by
  have hE1 : Integrable (fun x : ℝ =>
      (2 : ℂ)⁻¹ * (Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) * f x)) := by
    refine (hf.bdd_mul (c := 1) ?_ ?_).const_mul _
    · fun_prop
    · filter_upwards with x
      rw [Complex.norm_exp]
      simp
  have hE2 : Integrable (fun x : ℝ =>
      (2 : ℂ)⁻¹ * (Complex.exp (((-2 * Real.pi * x * -w : ℝ) : ℂ) * Complex.I) * f x)) := by
    refine (hf.bdd_mul (c := 1) ?_ ?_).const_mul _
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
  change f x * ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ) =
    (2 : ℂ)⁻¹ * (Complex.exp (((-2 * Real.pi * x * w : ℝ) : ℂ) * Complex.I) * f x) +
      (2 : ℂ)⁻¹ * (Complex.exp (((-2 * Real.pi * x * -w : ℝ) : ℂ) * Complex.I) * f x)
  rw [hcos]
  ring

theorem CCMEvenL1L2Source.fourier_eq_two_mul_integral_Ioi_cos
    (f : CCMEvenL1L2Source) (w : ℝ) :
    𝓕 (f : ℝ → ℂ) w =
      2 * ∫ x in Ioi (0 : ℝ),
        f x * ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ) := by
  have hproduct : Integrable (fun x : ℝ =>
      f x * ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ)) := by
    apply f.integrable.mul_bdd (c := 1)
    · fun_prop
    · filter_upwards with x
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (abs_cos_le_one (2 * Real.pi * w * x))
  have hproductEven : ∀ x : ℝ,
      f (-x) * ((Real.cos (2 * Real.pi * w * (-x)) : ℝ) : ℂ) =
        f x * ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ) := by
    intro x
    rw [f.even, show 2 * Real.pi * w * -x = -(2 * Real.pi * w * x) by ring,
      Real.cos_neg]
  have hsplit := integral_eq_two_mul_integral_Ioi_of_even hproduct hproductEven
  have havg := integral_mul_cos_eq_fourier_avg_of_integrable f f.integrable w
  have hFeven := fourier_even_of_even f.even w
  rw [hFeven] at havg
  calc
    𝓕 (f : ℝ → ℂ) w =
        (2 : ℂ)⁻¹ * 𝓕 (f : ℝ → ℂ) w +
          (2 : ℂ)⁻¹ * 𝓕 (f : ℝ → ℂ) w := by ring
    _ = ∫ x : ℝ, f x * ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ) := havg.symm
    _ = 2 * ∫ x in Ioi (0 : ℝ),
        f x * ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ) := hsplit

def CCMEvenL1L2Source.geometricKernelAction
    (f : CCMEvenL1L2Source) (lam : MellinL2.PosReal) : ℂ :=
  ∫ mu : MellinL2.PosReal,
    ccmArchimedeanGeometricScatteringKernel lam mu * f.multiplicativeDensity mu
      ∂MellinL2.multiplicativeHaar

theorem CCMEvenL1L2Source.geometricKernelIntegrand_exp
    (f : CCMEvenL1L2Source) (lam : MellinL2.PosReal) (t : ℝ) :
    ccmArchimedeanGeometricScatteringKernel lam (MellinL2.expMeasurableEquiv t) *
        f.multiplicativeDensity (MellinL2.expMeasurableEquiv t) =
      (((2 * Real.sqrt 2 * (Real.sqrt (lam : ℝ))⁻¹ : ℝ) : ℂ) *
        (Real.exp t • (f (Real.exp t) *
          ((Real.cos (2 * Real.pi * (lam : ℝ)⁻¹ * Real.exp t) : ℝ) : ℂ)))) := by
  change
    ((2 : ℂ) * ((Real.sqrt (lam : ℝ))⁻¹ : ℝ) * Real.sqrt (Real.exp t) *
      Real.cos (2 * Real.pi * (Real.exp t / (lam : ℝ))) *
        (((Real.sqrt 2 * Real.sqrt (Real.exp t) : ℝ) : ℂ) * f (Real.exp t))) =
    (((2 * Real.sqrt 2 * (Real.sqrt (lam : ℝ))⁻¹ : ℝ) : ℂ) *
      (Real.exp t • (f (Real.exp t) *
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
          (f (Real.exp t) *
            ((Real.cos (2 * Real.pi * (lam : ℝ)⁻¹ * Real.exp t) : ℝ) : ℂ))) := by
      push_cast
      ring
    _ = _ := by
      rw [hsqrtC]
      ring

theorem CCMEvenL1L2Source.integrable_geometricKernelIntegrand
    (f : CCMEvenL1L2Source) (lam : MellinL2.PosReal) :
    Integrable (fun mu : MellinL2.PosReal =>
      ccmArchimedeanGeometricScatteringKernel lam mu * f.multiplicativeDensity mu)
      MellinL2.multiplicativeHaar := by
  have hproduct : Integrable (fun x : ℝ =>
      f x * ((Real.cos (2 * Real.pi * (lam : ℝ)⁻¹ * x) : ℝ) : ℂ)) := by
    apply f.integrable.mul_bdd (c := 1)
    · fun_prop
    · filter_upwards with x
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (abs_cos_le_one (2 * Real.pi * (lam : ℝ)⁻¹ * x))
  have hlog := (integrableOn_Ioi_iff_integrable_exp_smul _).mp hproduct.integrableOn
  have hscaled := hlog.const_mul
    (((2 * Real.sqrt 2 * (Real.sqrt (lam : ℝ))⁻¹ : ℝ) : ℂ))
  have hcomp : Integrable (fun t : ℝ =>
      ccmArchimedeanGeometricScatteringKernel lam (MellinL2.expMeasurableEquiv t) *
        f.multiplicativeDensity (MellinL2.expMeasurableEquiv t)) :=
    hscaled.congr (Filter.Eventually.of_forall fun t =>
      (f.geometricKernelIntegrand_exp lam t).symm)
  have hback := MellinL2.exp_measurePreserving.symm.integrable_comp_of_integrable hcomp
  refine hback.congr (Filter.Eventually.of_forall fun mu => ?_)
  simp only [Function.comp_apply, MellinL2.expMeasurableEquiv.apply_symm_apply]

theorem CCMEvenL1L2Source.geometricKernelAction_eq_fourier
    (f : CCMEvenL1L2Source) (lam : MellinL2.PosReal) :
    f.geometricKernelAction lam =
      ((Real.sqrt 2 * (Real.sqrt (lam : ℝ))⁻¹ : ℝ) : ℂ) *
        𝓕 (f : ℝ → ℂ) ((lam : ℝ)⁻¹) := by
  unfold CCMEvenL1L2Source.geometricKernelAction
  rw [← MellinL2.exp_measurePreserving.integral_comp']
  calc
    (∫ t : ℝ,
        ccmArchimedeanGeometricScatteringKernel lam (MellinL2.expMeasurableEquiv t) *
          f.multiplicativeDensity (MellinL2.expMeasurableEquiv t)) =
        ∫ t : ℝ,
          ((2 * Real.sqrt 2 * (Real.sqrt (lam : ℝ))⁻¹ : ℝ) : ℂ) *
            (Real.exp t • (f (Real.exp t) *
              ((Real.cos (2 * Real.pi * (lam : ℝ)⁻¹ * Real.exp t) : ℝ) : ℂ))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (f.geometricKernelIntegrand_exp lam)
    _ = ((2 * Real.sqrt 2 * (Real.sqrt (lam : ℝ))⁻¹ : ℝ) : ℂ) *
        ∫ t : ℝ, Real.exp t • (f (Real.exp t) *
          ((Real.cos (2 * Real.pi * (lam : ℝ)⁻¹ * Real.exp t) : ℝ) : ℂ)) := by
      rw [integral_const_mul]
    _ = ((2 * Real.sqrt 2 * (Real.sqrt (lam : ℝ))⁻¹ : ℝ) : ℂ) *
        ∫ x in Ioi (0 : ℝ), f x *
          ((Real.cos (2 * Real.pi * (lam : ℝ)⁻¹ * x) : ℝ) : ℂ) := by
      rw [integral_Ioi_eq_integral_exp_smul]
    _ = _ := by
      rw [f.fourier_eq_two_mul_integral_Ioi_cos]
      push_cast
      ring

def CCMEvenL1L2Source.fourierMultiplicativeL2
    (f : CCMEvenL1L2Source) : CCMMultiplicativeL2 :=
  evenToMultiplicativeHaarUnitary (evenFourierTransform f.toEvenSubspace)

def CCMEvenL1L2Source.fourierMultiplicativeDensity
    (f : CCMEvenL1L2Source) (mu : MellinL2.PosReal) : ℂ :=
  (((Real.sqrt 2 * Real.sqrt (mu : ℝ) : ℝ) : ℂ) *
    𝓕 (f : ℝ → ℂ) (mu : ℝ))

theorem CCMEvenL1L2Source.expPullback_fourierMultiplicativeL2
    (f : CCMEvenL1L2Source) :
    MellinL2.expPullbackUnitary f.fourierMultiplicativeL2 =
      logEvenUnitary (evenFourierTransform f.toEvenSubspace) := by
  simp [CCMEvenL1L2Source.fourierMultiplicativeL2,
    evenToMultiplicativeHaarUnitary]

theorem CCMEvenL1L2Source.fourierMultiplicativeL2_ae_exp
    (f : CCMEvenL1L2Source) :
    (((f.fourierMultiplicativeL2 : CCMMultiplicativeL2) : MellinL2.PosReal → ℂ) ∘
        MellinL2.expMeasurableEquiv) =ᵐ[volume]
      f.fourierMultiplicativeDensity ∘ MellinL2.expMeasurableEquiv := by
  have hpull := Lp.coeFn_compMeasurePreserving
    f.fourierMultiplicativeL2 MellinL2.exp_measurePreserving
  have hlog := logEvenUnitary_ae (evenFourierTransform f.toEvenSubspace)
  have hfourier :=
    (GaloisForLFunctions.RHTower.coeFn_fourier_toLp f.integrable f.memLp_two).comp_tendsto
      realExp_quasiMeasurePreserving.tendsto_ae
  filter_upwards [hpull, hlog, hfourier] with t hpull_t hlog_t hfourier_t
  change f.fourierMultiplicativeL2 (MellinL2.expMeasurableEquiv t) =
    f.fourierMultiplicativeDensity (MellinL2.expMeasurableEquiv t)
  calc
    f.fourierMultiplicativeL2 (MellinL2.expMeasurableEquiv t) =
        MellinL2.expPullbackUnitary f.fourierMultiplicativeL2 t := hpull_t.symm
    _ = logEvenUnitary (evenFourierTransform f.toEvenSubspace) t :=
      congrArg (fun q : SoninL2 => q t) f.expPullback_fourierMultiplicativeL2
    _ = (((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ) *
        ((evenFourierTransform f.toEvenSubspace : evenSubspace) : SoninL2) (Real.exp t)) := hlog_t
    _ = (((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ) *
        𝓕 (f : ℝ → ℂ) (Real.exp t)) := by
      rw [coe_evenFourierTransform_apply]
      have hfourier_t' :
          ((𝓕 (f.memLp_two.toLp f) : SoninL2) : ℝ → ℂ) (Real.exp t) =
            𝓕 (f : ℝ → ℂ) (Real.exp t) := by
        simpa only [Function.comp_apply] using hfourier_t
      exact congrArg (((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ) * ·) hfourier_t'
    _ = f.fourierMultiplicativeDensity (MellinL2.expMeasurableEquiv t) := by
      unfold CCMEvenL1L2Source.fourierMultiplicativeDensity
      change (((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ) *
          𝓕 (f : ℝ → ℂ) (Real.exp t)) =
        (((Real.sqrt 2 * Real.sqrt (Real.exp t) : ℝ) : ℂ) *
          𝓕 (f : ℝ → ℂ) (Real.exp t))
      rw [Real.exp_half]

theorem CCMEvenL1L2Source.fourierMultiplicativeL2_ae
    (f : CCMEvenL1L2Source) :
    ((f.fourierMultiplicativeL2 : CCMMultiplicativeL2) : MellinL2.PosReal → ℂ) =ᵐ[
        MellinL2.multiplicativeHaar] f.fourierMultiplicativeDensity := by
  have h := f.fourierMultiplicativeL2_ae_exp.comp_tendsto
    MellinL2.exp_measurePreserving.symm.quasiMeasurePreserving.tendsto_ae
  filter_upwards [h] with mu hmu
  simpa only [Function.comp_apply, MellinL2.expMeasurableEquiv.apply_symm_apply] using hmu

theorem CCMEvenL1L2Source.fourierDensity_inversion_eq_kernelAction
    (f : CCMEvenL1L2Source) (lam : MellinL2.PosReal) :
    f.fourierMultiplicativeDensity (ccmMultiplicativePointInversion lam) =
      f.geometricKernelAction lam := by
  rw [f.geometricKernelAction_eq_fourier]
  unfold CCMEvenL1L2Source.fourierMultiplicativeDensity
  rw [coe_ccmMultiplicativePointInversion, Real.sqrt_inv]

theorem CCMEvenL1L2Source.geometricScattering_eq_inversion_fourier
    (f : CCMEvenL1L2Source) :
    ccmArchimedeanGeometricScattering f.toMultiplicativeL2 =
      ccmMultiplicativeInversion f.fourierMultiplicativeL2 := by
  rw [ccmArchimedeanGeometricScattering_eq_inversion_fourier]
  rw [show evenToMultiplicativeHaarUnitary.symm f.toMultiplicativeL2 =
      f.toEvenSubspace by
    simp [CCMEvenL1L2Source.toMultiplicativeL2]]
  rfl

/-- The geometric scattering kernel theorem on the entire even `L¹∩L²` core. -/
theorem CCMEvenL1L2Source.geometricScattering_has_kernel
    (f : CCMEvenL1L2Source) :
    ((ccmArchimedeanGeometricScattering f.toMultiplicativeL2 :
        CCMMultiplicativeL2) : MellinL2.PosReal → ℂ) =ᵐ[MellinL2.multiplicativeHaar]
      f.geometricKernelAction := by
  have hinv := ccmMultiplicativeInversion_ae f.fourierMultiplicativeL2
  have hfourier := f.fourierMultiplicativeL2_ae.comp_tendsto
    ccmMultiplicativePointInversion_measurePreserving.quasiMeasurePreserving.tendsto_ae
  filter_upwards [hinv, hfourier] with lam hinv_lam hfourier_lam
  rw [f.geometricScattering_eq_inversion_fourier]
  rw [hinv_lam]
  have hfourier_lam' : f.fourierMultiplicativeL2
      (ccmMultiplicativePointInversion lam) =
        f.fourierMultiplicativeDensity (ccmMultiplicativePointInversion lam) := by
    simpa only [Function.comp_apply] using hfourier_lam
  rw [hfourier_lam', f.fourierDensity_inversion_eq_kernelAction]

theorem CCMEvenL1L2Source.geometricScattering_literal_kernel_formula
    (f : CCMEvenL1L2Source) :
    ((ccmArchimedeanGeometricScattering f.toMultiplicativeL2 :
        CCMMultiplicativeL2) : MellinL2.PosReal → ℂ) =ᵐ[MellinL2.multiplicativeHaar]
      fun lam => ∫ mu : MellinL2.PosReal,
        ccmArchimedeanGeometricScatteringKernel lam mu * f.toMultiplicativeL2 mu
          ∂MellinL2.multiplicativeHaar := by
  filter_upwards [f.geometricScattering_has_kernel] with lam hlam
  rw [hlam]
  unfold CCMEvenL1L2Source.geometricKernelAction
  apply integral_congr_ae
  filter_upwards [f.toMultiplicativeL2_ae] with mu hmu
  rw [hmu]

/-! ## Sharp multiplicative projection -/

def ccmGeometricUpperHalf : Set MellinL2.PosReal :=
  {mu | (1 : ℝ) ≤ (mu : ℝ)}

theorem measurableSet_ccmGeometricUpperHalf :
    MeasurableSet ccmGeometricUpperHalf := by
  exact measurableSet_Ici.preimage measurable_subtype_coe

/-- Published sharp multiplier `P(v)=1_[1,∞)(v)`. -/
def ccmGeometricSharpValue (mu : MellinL2.PosReal) : ℂ :=
  if (1 : ℝ) ≤ (mu : ℝ) then 1 else 0

def ccmGeometricSharpProjection :
    CCMMultiplicativeL2 →L[ℂ] CCMMultiplicativeL2 :=
  lpSetCutoffCLM (F := ℂ) MellinL2.multiplicativeHaar 2
    ccmGeometricUpperHalf measurableSet_ccmGeometricUpperHalf

theorem ccmGeometricSharpProjection_ae (f : CCMMultiplicativeL2) :
    ((ccmGeometricSharpProjection f : CCMMultiplicativeL2) :
        MellinL2.PosReal → ℂ) =ᵐ[MellinL2.multiplicativeHaar]
      fun mu => ccmGeometricSharpValue mu * f mu := by
  have h : ((ccmGeometricSharpProjection f : CCMMultiplicativeL2) :
      MellinL2.PosReal → ℂ) =ᵐ[MellinL2.multiplicativeHaar]
        ccmGeometricUpperHalf.indicator (fun mu => f mu) := by
    simpa only [ccmGeometricSharpProjection] using
      (lpSetCutoffCLM_coeFn (F := ℂ) (𝕜 := ℂ)
        MellinL2.multiplicativeHaar 2 ccmGeometricUpperHalf
          measurableSet_ccmGeometricUpperHalf f)
  filter_upwards [h] with mu hmu
  rw [hmu]
  by_cases hupper : (1 : ℝ) ≤ (mu : ℝ)
  · simp [ccmGeometricUpperHalf, ccmGeometricSharpValue, hupper]
  · simp [ccmGeometricUpperHalf, ccmGeometricSharpValue, hupper]

def ccmOutsideUnitSet : Set ℝ :=
  {x | (1 : ℝ) ≤ |x|}

theorem measurableSet_ccmOutsideUnitSet : MeasurableSet ccmOutsideUnitSet := by
  exact measurableSet_Ici.preimage measurable_abs

/-- The physical even `L¹∩L²` source obtained by the sharp multiplicative cutoff. -/
def ccmOutsideUnitEvenSchwartzSource
    (g : SchwartzMap ℝ ℂ) : CCMEvenL1L2Source where
  toFun := ccmOutsideUnitSet.indicator (schwartzEvenPart g)
  integrable := (schwartzEvenPart g).integrable.indicator measurableSet_ccmOutsideUnitSet
  memLp_two := (schwartzEvenPart g).memLp 2 volume |>.indicator
    measurableSet_ccmOutsideUnitSet
  even := by
    intro x
    by_cases hx : (1 : ℝ) ≤ |x|
    · simp [ccmOutsideUnitSet, hx, schwartzEvenPart_even]
    · simp [ccmOutsideUnitSet, hx]

theorem ccmOutsideUnitEvenSchwartzSource_apply
    (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    ccmOutsideUnitEvenSchwartzSource g x =
      if (1 : ℝ) ≤ |x| then schwartzEvenPart g x else 0 := by
  by_cases hx : (1 : ℝ) ≤ |x|
  · simp [ccmOutsideUnitEvenSchwartzSource, ccmOutsideUnitSet, hx]
  · simp [ccmOutsideUnitEvenSchwartzSource, ccmOutsideUnitSet, hx]

theorem ccmOutsideUnit_density_eq_sharp_mul
    (g : SchwartzMap ℝ ℂ) (mu : MellinL2.PosReal) :
    (ccmOutsideUnitEvenSchwartzSource g).multiplicativeDensity mu =
      ccmGeometricSharpValue mu * ccmMultiplicativeSchwartzDensity g mu := by
  unfold CCMEvenL1L2Source.multiplicativeDensity
    ccmMultiplicativeSchwartzDensity
  rw [ccmOutsideUnitEvenSchwartzSource_apply]
  have habs : |(mu : ℝ)| = (mu : ℝ) := abs_of_pos mu.property
  rw [habs]
  by_cases hupper : (1 : ℝ) ≤ (mu : ℝ)
  · simp [ccmGeometricSharpValue, hupper]
  · simp [ccmGeometricSharpValue, hupper]

theorem ccmGeometricSharpProjection_schwartzSource
    (g : SchwartzMap ℝ ℂ) :
    ccmGeometricSharpProjection (ccmMultiplicativeSchwartzSource g) =
      (ccmOutsideUnitEvenSchwartzSource g).toMultiplicativeL2 := by
  apply Lp.ext
  filter_upwards [ccmGeometricSharpProjection_ae
      (ccmMultiplicativeSchwartzSource g),
    ccmMultiplicativeSchwartzSource_ae g,
    (ccmOutsideUnitEvenSchwartzSource g).toMultiplicativeL2_ae]
      with mu hproj hsource houtside
  rw [hproj, hsource, houtside, ccmOutsideUnit_density_eq_sharp_mul]

/-! ## Commutator kernel -/

/-- Geometric realization of `[(P),u∞ᵍ]`. -/
def ccmArchimedeanGeometricSharpCommutator :
    CCMMultiplicativeL2 →L[ℂ] CCMMultiplicativeL2 :=
  ccmGeometricSharpProjection * ccmArchimedeanGeometricScattering -
    ccmArchimedeanGeometricScattering * ccmGeometricSharpProjection

/-- Published kernel `(P(λ)-P(μ))kᵘ(λ,μ)`. -/
def ccmArchimedeanGeometricSharpCommutatorKernel
    (lam mu : MellinL2.PosReal) : ℂ :=
  (ccmGeometricSharpValue lam - ccmGeometricSharpValue mu) *
    ccmArchimedeanGeometricScatteringKernel lam mu

def ccmArchimedeanGeometricSharpCommutatorKernelAction
    (g : SchwartzMap ℝ ℂ) (lam : MellinL2.PosReal) : ℂ :=
  ∫ mu : MellinL2.PosReal,
    ccmArchimedeanGeometricSharpCommutatorKernel lam mu *
      ccmMultiplicativeSchwartzDensity g mu
        ∂MellinL2.multiplicativeHaar

theorem integrable_ccmArchimedeanGeometricSharpCommutatorKernelIntegrand
    (g : SchwartzMap ℝ ℂ) (lam : MellinL2.PosReal) :
    Integrable (fun mu : MellinL2.PosReal =>
      ccmArchimedeanGeometricSharpCommutatorKernel lam mu *
        ccmMultiplicativeSchwartzDensity g mu)
      MellinL2.multiplicativeHaar := by
  have hfull := (integrable_ccmArchimedeanGeometricKernelIntegrand g lam).const_mul
    (ccmGeometricSharpValue lam)
  have houtside :=
    (ccmOutsideUnitEvenSchwartzSource g).integrable_geometricKernelIntegrand lam
  have hsub := hfull.sub houtside
  refine hsub.congr (Filter.Eventually.of_forall fun mu => ?_)
  change ccmGeometricSharpValue lam *
        (ccmArchimedeanGeometricScatteringKernel lam mu *
          ccmMultiplicativeSchwartzDensity g mu) -
      ccmArchimedeanGeometricScatteringKernel lam mu *
        (ccmOutsideUnitEvenSchwartzSource g).multiplicativeDensity mu =
    ccmArchimedeanGeometricSharpCommutatorKernel lam mu *
      ccmMultiplicativeSchwartzDensity g mu
  rw [ccmOutsideUnit_density_eq_sharp_mul]
  unfold ccmArchimedeanGeometricSharpCommutatorKernel
  ring

theorem ccmArchimedeanGeometricSharpCommutatorKernelAction_eq_sub
    (g : SchwartzMap ℝ ℂ) (lam : MellinL2.PosReal) :
    ccmArchimedeanGeometricSharpCommutatorKernelAction g lam =
      ccmGeometricSharpValue lam * ccmArchimedeanGeometricKernelAction g lam -
        (ccmOutsideUnitEvenSchwartzSource g).geometricKernelAction lam := by
  unfold ccmArchimedeanGeometricSharpCommutatorKernelAction
    ccmArchimedeanGeometricKernelAction
    CCMEvenL1L2Source.geometricKernelAction
  calc
    (∫ mu : MellinL2.PosReal,
        ccmArchimedeanGeometricSharpCommutatorKernel lam mu *
          ccmMultiplicativeSchwartzDensity g mu
            ∂MellinL2.multiplicativeHaar) =
      ∫ mu : MellinL2.PosReal,
        ccmGeometricSharpValue lam *
            (ccmArchimedeanGeometricScatteringKernel lam mu *
              ccmMultiplicativeSchwartzDensity g mu) -
          ccmArchimedeanGeometricScatteringKernel lam mu *
            (ccmOutsideUnitEvenSchwartzSource g).multiplicativeDensity mu
              ∂MellinL2.multiplicativeHaar := by
        apply integral_congr_ae
        filter_upwards with mu
        rw [ccmOutsideUnit_density_eq_sharp_mul]
        unfold ccmArchimedeanGeometricSharpCommutatorKernel
        ring
    _ = ∫ mu : MellinL2.PosReal,
          ccmGeometricSharpValue lam *
            (ccmArchimedeanGeometricScatteringKernel lam mu *
              ccmMultiplicativeSchwartzDensity g mu)
            ∂MellinL2.multiplicativeHaar -
        ∫ mu : MellinL2.PosReal,
          ccmArchimedeanGeometricScatteringKernel lam mu *
            (ccmOutsideUnitEvenSchwartzSource g).multiplicativeDensity mu
              ∂MellinL2.multiplicativeHaar := by
        rw [integral_sub]
        · exact (integrable_ccmArchimedeanGeometricKernelIntegrand g lam).const_mul _
        · exact (ccmOutsideUnitEvenSchwartzSource g).integrable_geometricKernelIntegrand lam
    _ = _ := by rw [integral_const_mul]

theorem ccmArchimedeanGeometricSharpCommutator_schwartzSource
    (g : SchwartzMap ℝ ℂ) :
    ccmArchimedeanGeometricSharpCommutator (ccmMultiplicativeSchwartzSource g) =
      ccmGeometricSharpProjection
          (ccmArchimedeanGeometricScattering (ccmMultiplicativeSchwartzSource g)) -
        ccmArchimedeanGeometricScattering
          (ccmOutsideUnitEvenSchwartzSource g).toMultiplicativeL2 := by
  unfold ccmArchimedeanGeometricSharpCommutator
  change ccmGeometricSharpProjection
      (ccmArchimedeanGeometricScattering (ccmMultiplicativeSchwartzSource g)) -
    ccmArchimedeanGeometricScattering
      (ccmGeometricSharpProjection (ccmMultiplicativeSchwartzSource g)) = _
  rw [ccmGeometricSharpProjection_schwartzSource]

/-- Exact actual-operator kernel theorem for Connes--Consani Lemma `sch3(ii)`. -/
theorem ccmArchimedeanGeometricSharpCommutator_has_literal_kernel
    (g : SchwartzMap ℝ ℂ) :
    ((ccmArchimedeanGeometricSharpCommutator (ccmMultiplicativeSchwartzSource g) :
        CCMMultiplicativeL2) : MellinL2.PosReal → ℂ) =ᵐ[MellinL2.multiplicativeHaar]
      ccmArchimedeanGeometricSharpCommutatorKernelAction g := by
  have hsub := Lp.coeFn_sub
    (ccmGeometricSharpProjection
      (ccmArchimedeanGeometricScattering (ccmMultiplicativeSchwartzSource g)))
    (ccmArchimedeanGeometricScattering
      (ccmOutsideUnitEvenSchwartzSource g).toMultiplicativeL2)
  have hproj := ccmGeometricSharpProjection_ae
    (ccmArchimedeanGeometricScattering (ccmMultiplicativeSchwartzSource g))
  have hfull := ccmArchimedeanGeometricScattering_has_literal_kernel g
  have houtside := (ccmOutsideUnitEvenSchwartzSource g).geometricScattering_has_kernel
  filter_upwards [hsub, hproj, hfull, houtside]
      with lam hsub_lam hproj_lam hfull_lam houtside_lam
  rw [ccmArchimedeanGeometricSharpCommutator_schwartzSource]
  rw [hsub_lam]
  change ccmGeometricSharpProjection
      (ccmArchimedeanGeometricScattering (ccmMultiplicativeSchwartzSource g)) lam -
    ccmArchimedeanGeometricScattering
      (ccmOutsideUnitEvenSchwartzSource g).toMultiplicativeL2 lam = _
  rw [hproj_lam, hfull_lam, houtside_lam]
  exact (ccmArchimedeanGeometricSharpCommutatorKernelAction_eq_sub g lam).symm

theorem ccmArchimedeanGeometricSharpCommutator_literal_kernel_formula
    (g : SchwartzMap ℝ ℂ) :
    ((ccmArchimedeanGeometricSharpCommutator (ccmMultiplicativeSchwartzSource g) :
        CCMMultiplicativeL2) : MellinL2.PosReal → ℂ) =ᵐ[MellinL2.multiplicativeHaar]
      fun lam => ∫ mu : MellinL2.PosReal,
        (ccmGeometricSharpValue lam - ccmGeometricSharpValue mu) *
          ccmArchimedeanGeometricScatteringKernel lam mu *
            ccmMultiplicativeSchwartzSource g mu
              ∂MellinL2.multiplicativeHaar := by
  filter_upwards [ccmArchimedeanGeometricSharpCommutator_has_literal_kernel g]
      with lam hlam
  rw [hlam]
  unfold ccmArchimedeanGeometricSharpCommutatorKernelAction
    ccmArchimedeanGeometricSharpCommutatorKernel
  apply integral_congr_ae
  filter_upwards [ccmMultiplicativeSchwartzSource_ae g] with mu hmu
  rw [hmu]

end RHTower
