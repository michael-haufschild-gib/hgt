import GaloisForLFunctions.RHTower.ConstrainedProlateOperator
import GaloisForLFunctions.RHTower.L2FourierIntegralBridge
import GaloisForLFunctions.HTGeometry.SymmetricHalfEndpointPeriodization
import GaloisForLFunctions.RHTower.BurnolSoninEvenCosineAperture
import GaloisForLFunctions.RHTower.ConstrainedProlateSignedTrial
import Mathlib.Analysis.Fourier.FourierTransformDeriv

noncomputable section

open MeasureTheory Set FourierTransform Filter Topology
open scoped ENNReal BoundedContinuousFunction FourierTransform Real

namespace RHTower

theorem integrable_id_smul_of_support_Icc
    {a : ℝ} {f : ℝ → ℂ} (hf : Integrable f)
    (hsupp : ∀ x, x ∉ Icc (-a) a → f x = 0) :
    Integrable (fun x : ℝ => x • f x) := by
  refine (hf.norm.const_mul a).mono'
    (continuous_id.aestronglyMeasurable.smul hf.aestronglyMeasurable) ?_
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ Icc (-a) a
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right ((abs_le).2 hx) (norm_nonneg (f x))
    · rw [hsupp x hx]
      simp

theorem integrable_pow_smul_of_support_Icc
    {a : ℝ} {f : ℝ → ℂ} (hf : Integrable f)
    (hsupp : ∀ x, x ∉ Icc (-a) a → f x = 0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n • f x) := by
  refine (hf.norm.const_mul (|a| ^ n)).mono'
    ((continuous_id.pow n).aestronglyMeasurable.smul hf.aestronglyMeasurable) ?_
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ Icc (-a) a
    · rw [norm_smul, Real.norm_eq_abs, abs_pow]
      have ha : 0 ≤ a := (abs_nonneg x).trans ((abs_le).2 hx)
      rw [abs_of_nonneg ha]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg x) ((abs_le).2 hx) n) (norm_nonneg (f x))
    · rw [hsupp x hx]
      simp

theorem integrable_norm_pow_mul_norm_of_support_Icc
    {a : ℝ} {f : ℝ → ℂ} (hf : Integrable f)
    (hsupp : ∀ x, x ∉ Icc (-a) a → f x = 0) (n : ℕ) :
    Integrable (fun x : ℝ => ‖x‖ ^ n * ‖f x‖) := by
  simpa only [norm_smul, norm_pow] using
    (integrable_pow_smul_of_support_Icc hf hsupp n).norm

theorem contDiff_fourier_compactSupport
    {a : ℝ} {f : ℝ → ℂ} (hf : Integrable f)
    (hsupp : ∀ x, x ∉ Icc (-a) a → f x = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (𝓕 f) := by
  exact Real.contDiff_fourier fun n _ =>
    integrable_norm_pow_mul_norm_of_support_Icc hf hsupp n

theorem iteratedDeriv_fourier_compactSupport
    {a : ℝ} {f : ℝ → ℂ} (hf : Integrable f)
    (hsupp : ∀ x, x ∉ Icc (-a) a → f x = 0) (n : ℕ) :
    iteratedDeriv n (𝓕 f) =
      𝓕 (fun x : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ n • f x) := by
  exact Real.iteratedDeriv_fourier
    (N := (⊤ : ℕ∞)) (fun m _ => integrable_pow_smul_of_support_Icc hf hsupp m) le_top

/-- Exact unit-interval rescaling of the Fourier transform of a source supported on `[-a,a]`.
The kernel frequency is `a²`, hence the classical prolate bandwidth is `2πa²`. -/
theorem fourier_compactSupport_unitScale
    {a : ℝ} (ha : 0 < a) {q : ℝ → ℂ}
    (hsupp : ∀ y, y ∉ Icc (-a) a → q y = 0) (x : ℝ) :
    a • ∫ t in Icc (-1 : ℝ) 1,
        𝐞 (-((a * t) * (a * x))) • q (a * t) =
      𝓕 q (a * x) := by
  let g : ℝ → ℂ := fun y => 𝐞 (-(y * (a * x))) • q y
  have hscale := MeasureTheory.Measure.integral_comp_mul_left g a
  have habs : |a⁻¹| = a⁻¹ := abs_of_pos (inv_pos.mpr ha)
  have hmul : a • ∫ t : ℝ, g (a * t) = ∫ y : ℝ, g y := by
    rw [hscale, habs, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  have hsupportScaled : ∀ t, t ∉ Icc (-1 : ℝ) 1 → q (a * t) = 0 := by
    intro t ht
    apply hsupp (a * t)
    intro hat
    apply ht
    constructor <;> nlinarith [hat.1, hat.2]
  have hrestrict : (∫ t : ℝ, g (a * t)) =
      ∫ t in Icc (-1 : ℝ) 1, g (a * t) := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ Icc (-1 : ℝ) 1
    · simp [ht]
    · simp [ht, g, hsupportScaled t ht]
  rw [hrestrict] at hmul
  change a • ∫ t in Icc (-1 : ℝ) 1, g (a * t) = 𝓕 q (a * x)
  rw [hmul, Real.fourier_eq]
  congr 1
  funext y
  simp only [g, RCLike.inner_apply', conj_trivial]

def compactFourierFirstMoment (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  -(2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * f x)

def compactFourierSecondMoment (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  -(2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) * compactFourierFirstMoment f x)

theorem integrable_compactFourierFirstMoment_of_support_Icc
    {a : ℝ} {f : ℝ → ℂ} (hf : Integrable f)
    (hsupp : ∀ x, x ∉ Icc (-a) a → f x = 0) :
    Integrable (compactFourierFirstMoment f) := by
  have h := ((integrable_id_smul_of_support_Icc hf hsupp).const_mul
    (2 * (Real.pi : ℂ) * Complex.I)).neg
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.neg_apply, compactFourierFirstMoment, Complex.real_smul]
  ring

theorem integrable_compactFourierSecondMoment_of_support_Icc
    {a : ℝ} {f : ℝ → ℂ} (hf : Integrable f)
    (hsupp : ∀ x, x ∉ Icc (-a) a → f x = 0) :
    Integrable (compactFourierSecondMoment f) := by
  have hfirst := integrable_compactFourierFirstMoment_of_support_Icc hf hsupp
  have hsupportFirst : ∀ x, x ∉ Icc (-a) a → compactFourierFirstMoment f x = 0 := by
    intro x hx
    simp [compactFourierFirstMoment, hsupp x hx]
  have h := ((integrable_id_smul_of_support_Icc hfirst hsupportFirst).const_mul
    (2 * (Real.pi : ℂ) * Complex.I)).neg
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.neg_apply, compactFourierSecondMoment, Complex.real_smul]
  ring

theorem hasDerivAt_fourier_compactSupport
    {a : ℝ} {f : ℝ → ℂ} (hf : Integrable f)
    (hsupp : ∀ x, x ∉ Icc (-a) a → f x = 0) (w : ℝ) :
    HasDerivAt (𝓕 f) (𝓕 (compactFourierFirstMoment f) w) w := by
  have h := Real.hasDerivAt_fourier hf
    (integrable_id_smul_of_support_Icc hf hsupp) w
  have heq : (fun x : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) • f x) =
      compactFourierFirstMoment f := by
    funext x
    simp only [compactFourierFirstMoment, smul_eq_mul]
    ring
  rw [heq] at h
  exact h

theorem hasDerivAt_fourier_compactFirstMoment
    {a : ℝ} {f : ℝ → ℂ} (hf : Integrable f)
    (hsupp : ∀ x, x ∉ Icc (-a) a → f x = 0) (w : ℝ) :
    HasDerivAt (𝓕 (compactFourierFirstMoment f))
      (𝓕 (compactFourierSecondMoment f) w) w := by
  have hfirst := integrable_compactFourierFirstMoment_of_support_Icc hf hsupp
  have hsupportFirst : ∀ x, x ∉ Icc (-a) a → compactFourierFirstMoment f x = 0 := by
    intro x hx
    simp [compactFourierFirstMoment, hsupp x hx]
  have h := Real.hasDerivAt_fourier hfirst
    (integrable_id_smul_of_support_Icc hfirst hsupportFirst) w
  have heq :
      (fun x : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) •
        compactFourierFirstMoment f x) = compactFourierSecondMoment f := by
    funext x
    simp only [compactFourierSecondMoment, smul_eq_mul]
    ring
  rw [heq] at h
  exact h

theorem integrable_coe_of_mem_evenTimeLimitedSubspace
    (a : ℝ) (f : evenSubspace) (hf : f ∈ evenTimeLimitedSubspace a) :
    Integrable (((f : evenSubspace) : SoninL2) : ℝ → ℂ) := by
  have hfix := (mem_evenTimeLimitedSubspace_iff a f).mp hf
  have hcoe := congrArg (fun g : evenSubspace => (g : SoninL2)) hfix
  have hint := integrable_indicatorCutoff_Icc (-a) a (f : SoninL2)
  change ((evenIndicatorCutoff a f : evenSubspace) : SoninL2) = (f : SoninL2) at hcoe
  rw [coe_evenIndicatorCutoff_apply] at hcoe
  change Integrable
    (((indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
      (f : SoninL2) : SoninL2) : ℝ → ℂ)) at hint
  rw [hcoe] at hint
  exact hint

noncomputable def evenTimeLimitedFourierRepresentative
    (a : ℝ) (f : evenSubspace) (hf : f ∈ evenTimeLimitedSubspace a) : ℝ →ᵇ ℂ :=
  Real.Lp.fourierTransform
    ((memLp_one_iff_integrable.mpr
      (integrable_coe_of_mem_evenTimeLimitedSubspace a f hf)).toLp
      (((f : evenSubspace) : SoninL2) : ℝ → ℂ))

theorem continuous_evenTimeLimitedFourierRepresentative
    (a : ℝ) (f : evenSubspace) (hf : f ∈ evenTimeLimitedSubspace a) :
    Continuous (evenTimeLimitedFourierRepresentative a f hf) :=
  (evenTimeLimitedFourierRepresentative a f hf).continuous

theorem ae_eq_evenTimeLimitedFourierRepresentative
    (a : ℝ) (f : evenSubspace) (hf : f ∈ evenTimeLimitedSubspace a) :
    ((fourierUnitary (f : SoninL2) : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      evenTimeLimitedFourierRepresentative a f hf := by
  simpa [evenTimeLimitedFourierRepresentative] using!
    l2_fourier_coeFn_eq_l1_fourier_of_integrable (f : SoninL2)
      (integrable_coe_of_mem_evenTimeLimitedSubspace a f hf)

theorem mem_evenTimeLimitedSubspace_of_timeBand_eigen
    (a : ℝ) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) :
    f ∈ evenTimeLimitedSubspace a := by
  have hout := evenTimeBandFourier_mem_timeLimited a f
  have hscaled : χ⁻¹ • evenTimeBandFourier a f ∈ evenTimeLimitedSubspace a :=
    (evenTimeLimitedSubspace a).smul_mem χ⁻¹ hout
  rw [heig, inv_smul_smul₀ hχ] at hscaled
  exact hscaled

noncomputable def timeBandEigenFourierRepresentative
    (a : ℝ) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) : ℝ →ᵇ ℂ :=
  evenTimeLimitedFourierRepresentative a f
    (mem_evenTimeLimitedSubspace_of_timeBand_eigen a f χ hχ heig)

noncomputable def timeBandEigenPointwiseSource
    (a : ℝ) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) (x : ℝ) : ℂ :=
  if x ∈ Ioo (-a) a then
    χ⁻¹ * timeBandEigenFourierRepresentative a f χ hχ heig x
  else if x = -a ∨ x = a then
    (χ⁻¹ * timeBandEigenFourierRepresentative a f χ hχ heig x) / 2
  else 0

theorem timeBandEigenPointwiseSource_eq_zero_of_not_mem_Icc
    (a : ℝ) (ha : 0 ≤ a) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) {x : ℝ}
    (hx : x ∉ Icc (-a) a) :
    timeBandEigenPointwiseSource a f χ hχ heig x = 0 := by
  unfold timeBandEigenPointwiseSource
  rw [if_neg]
  · rw [if_neg]
    intro h
    rcases h with rfl | rfl <;> exact hx (by simp [ha])
  · exact fun h => hx (Ioo_subset_Icc_self h)

theorem hasCompactSupport_timeBandEigenPointwiseSource
    (a : ℝ) (ha : 0 ≤ a) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) :
    HasCompactSupport (timeBandEigenPointwiseSource a f χ hχ heig) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro x hx
  exact timeBandEigenPointwiseSource_eq_zero_of_not_mem_Icc a ha f χ hχ heig hx

theorem continuousOn_timeBandEigenPointwiseSource_interior
    {a : ℝ} (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) :
    ContinuousOn (timeBandEigenPointwiseSource a f χ hχ heig) (Ioo (-a) a) := by
  intro x hx
  have hrep : Continuous (timeBandEigenFourierRepresentative a f χ hχ heig) :=
    continuous_evenTimeLimitedFourierRepresentative a f
      (mem_evenTimeLimitedSubspace_of_timeBand_eigen a f χ hχ heig)
  have hcont : Continuous (fun y =>
      χ⁻¹ * timeBandEigenFourierRepresentative a f χ hχ heig y) :=
    continuous_const.mul hrep
  apply ContinuousWithinAt.congr_of_eventuallyEq hcont.continuousAt.continuousWithinAt
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp [timeBandEigenPointwiseSource, hy]
  simp [timeBandEigenPointwiseSource, hx]

@[simp] theorem timeBandEigenPointwiseSource_left_endpoint
    (a : ℝ) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) :
    timeBandEigenPointwiseSource a f χ hχ heig (-a) =
      (χ⁻¹ * timeBandEigenFourierRepresentative a f χ hχ heig (-a)) / 2 := by
  simp [timeBandEigenPointwiseSource]

@[simp] theorem timeBandEigenPointwiseSource_right_endpoint
    (a : ℝ) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) :
    timeBandEigenPointwiseSource a f χ hχ heig a =
      (χ⁻¹ * timeBandEigenFourierRepresentative a f χ hχ heig a) / 2 := by
  simp [timeBandEigenPointwiseSource]

theorem ae_eq_timeBandEigenPointwiseSource
    (a : ℝ) (ha : 0 ≤ a) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) :
    timeBandEigenPointwiseSource a f χ hχ heig =ᵐ[volume]
      (((f : evenSubspace) : SoninL2) : ℝ → ℂ) := by
  have htime := mem_evenTimeLimitedSubspace_of_timeBand_eigen a f χ hχ heig
  have hfix := (mem_evenTimeLimitedSubspace_iff a f).mp htime
  have heig' : evenIndicatorCutoff a (evenFourierTransform f) = χ • f := by
    rw [evenTimeBandFourier_eq_mul] at heig
    simpa only [mul_apply_eq_comp, hfix] using heig
  have heigcoe := congrArg (fun g : evenSubspace => (g : SoninL2)) heig'
  change indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
      (fourierUnitary (f : SoninL2)) = χ • (f : SoninL2) at heigcoe
  have heigfun := congrArg (fun g : SoninL2 => (g : ℝ → ℂ)) heigcoe
  have hfixcoe := congrArg (fun g : evenSubspace => (g : SoninL2)) hfix
  change indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
      (f : SoninL2) = (f : SoninL2) at hfixcoe
  have hfixfun := congrArg (fun g : SoninL2 => (g : ℝ → ℂ)) hfixcoe
  have hbridge := ae_eq_evenTimeLimitedFourierRepresentative a f htime
  have hcutF := indicatorCutoff_ae (centralInterval a)
    (measurableSet_centralInterval a) (fourierUnitary (f : SoninL2))
  have hcutf := indicatorCutoff_ae (centralInterval a)
    (measurableSet_centralInterval a) (f : SoninL2)
  have hsmul := Lp.coeFn_smul χ (f : SoninL2)
  have hend : ∀ᵐ x : ℝ ∂volume, x ≠ -a ∧ x ≠ a := by
    have h₁ : ∀ᵐ x : ℝ ∂volume, x ≠ -a := by simp [ae_iff, measure_singleton]
    have h₂ : ∀ᵐ x : ℝ ∂volume, x ≠ a := by simp [ae_iff, measure_singleton]
    filter_upwards [h₁, h₂] with x hx₁ hx₂
    exact ⟨hx₁, hx₂⟩
  filter_upwards [hbridge, hcutF, hcutf, hsmul, hend] with x hrep hPF hPf hχf hxend
  have heigx := congrFun heigfun x
  have hfixx := congrFun hfixfun x
  have heigx' :
      ((indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
        (fourierUnitary (f : SoninL2)) : SoninL2) : ℝ → ℂ) x =
        χ * (f : SoninL2) x := by
    calc
      _ = ((χ • (f : SoninL2) : SoninL2) : ℝ → ℂ) x := heigx
      _ = χ * (f : SoninL2) x := by
        simpa only [Pi.smul_apply, smul_eq_mul] using hχf
  have hfixx' :
      ((indicatorCutoff (centralInterval a) (measurableSet_centralInterval a)
        (f : SoninL2) : SoninL2) : ℝ → ℂ) x = (f : SoninL2) x := hfixx
  by_cases hx : x ∈ Icc (-a) a
  · have hxoo : x ∈ Ioo (-a) a := by
      exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hxend.1), lt_of_le_of_ne hx.2 hxend.2⟩
    have hrep' : ((fourierUnitary (f : SoninL2) : SoninL2) : ℝ → ℂ) x =
        timeBandEigenFourierRepresentative a f χ hχ heig x := by
      simpa only [timeBandEigenFourierRepresentative] using hrep
    rw [hPF] at heigx'
    simp only [centralInterval, Set.indicator_of_mem hx] at heigx'
    simp only [timeBandEigenPointwiseSource, if_pos hxoo]
    have hscalar : χ⁻¹ * (χ * ((f : SoninL2) x)) = (f : SoninL2) x := by
      field_simp
    rw [← hrep', heigx']
    exact hscalar
  · rw [hPf] at hfixx'
    simp only [centralInterval, Set.indicator_of_notMem hx] at hfixx'
    have hzero : (f : SoninL2) x = 0 := hfixx'.symm
    rw [timeBandEigenPointwiseSource_eq_zero_of_not_mem_Icc a ha f χ hχ heig hx,
      hzero]

theorem integrable_timeBandEigenPointwiseSource
    (a : ℝ) (ha : 0 ≤ a) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) :
    Integrable (timeBandEigenPointwiseSource a f χ hχ heig) := by
  exact (integrable_coe_of_mem_evenTimeLimitedSubspace a f
    (mem_evenTimeLimitedSubspace_of_timeBand_eigen a f χ hχ heig)).congr
      (ae_eq_timeBandEigenPointwiseSource a ha f χ hχ heig).symm

end RHTower

noncomputable section

open MeasureTheory Set FourierTransform Filter Topology
open scoped ENNReal BoundedContinuousFunction FourierTransform Real

namespace RHTower

theorem even_evenTimeLimitedFourierRepresentative
    (a : ℝ) (f : evenSubspace) (hf : f ∈ evenTimeLimitedSubspace a) :
    Function.Even (evenTimeLimitedFourierRepresentative a f hf) := by
  let G : ℝ → ℂ := evenTimeLimitedFourierRepresentative a f hf
  have hbridge := ae_eq_evenTimeLimitedFourierRepresentative a f hf
  have hbridge_neg := hbridge.comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  have hf_even : l2Reflection (f : SoninL2) = (f : SoninL2) :=
    (mem_evenSubspace_iff (f : SoninL2)).mp f.property
  have hF_even : l2Reflection (fourierUnitary (f : SoninL2)) =
      fourierUnitary (f : SoninL2) := by
    rw [← fourierUnitary_l2Reflection, hf_even]
  have hreflect := l2Reflection_ae (fourierUnitary (f : SoninL2))
  rw [hF_even] at hreflect
  have hGae : (fun x : ℝ => G (-x)) =ᵐ[volume] G := by
    filter_upwards [hbridge, hbridge_neg, hreflect] with x hx hxneg href
    dsimp only [Function.comp_apply] at hxneg
    change ((fourierUnitary (f : SoninL2) : SoninL2) : ℝ → ℂ) x =
      ((fourierUnitary (f : SoninL2) : SoninL2) : ℝ → ℂ) (-x) at href
    change evenTimeLimitedFourierRepresentative a f hf (-x) =
      evenTimeLimitedFourierRepresentative a f hf x
    rw [← hxneg, ← href, hx]
  have hright : Continuous G := by
    simpa only [G] using continuous_evenTimeLimitedFourierRepresentative a f hf
  have hleft : Continuous (fun x : ℝ => G (-x)) := hright.comp continuous_neg
  exact congrFun ((hleft.ae_eq_iff_eq volume hright).mp hGae)

theorem evenTimeLimitedFourierRepresentative_exterior_energy
    {a : ℝ} (ha : 0 ≤ a) (f : evenSubspace)
    (hf : f ∈ evenTimeLimitedSubspace a) :
    let q : ℝ → ℂ := evenTimeLimitedFourierRepresentative a f hf
    (∫ y in Iic (-a), ‖q y‖ ^ 2) + ∫ y in Ioi a, ‖q y‖ ^ 2 =
      ‖f‖ ^ 2 - ‖evenTimeBandFourier a f‖ ^ 2 := by
  let q : ℝ → ℂ := evenTimeLimitedFourierRepresentative a f hf
  change (∫ y in Iic (-a), ‖q y‖ ^ 2) + ∫ y in Ioi a, ‖q y‖ ^ 2 =
    ‖f‖ ^ 2 - ‖evenTimeBandFourier a f‖ ^ 2
  have hqae : (((fourierUnitary (f : SoninL2) : SoninL2) : ℝ → ℂ)) =ᵐ[volume] q := by
    simpa only [q] using ae_eq_evenTimeLimitedFourierRepresentative a f hf
  have hqint : Integrable (fun y : ℝ => ‖q y‖ ^ 2) := by
    have hFint : Integrable (fun y : ℝ =>
        ‖((fourierUnitary (f : SoninL2) : SoninL2) y)‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm
        (Lp.aestronglyMeasurable (fourierUnitary (f : SoninL2)))).mp
        (Lp.memLp (fourierUnitary (f : SoninL2)))
    refine hFint.congr ?_
    filter_upwards [hqae] with y hy
    rw [hy]
  have htotal : ∫ y : ℝ, ‖q y‖ ^ 2 = ‖f‖ ^ 2 := by
    calc
      ∫ y : ℝ, ‖q y‖ ^ 2 =
          ∫ y : ℝ, ‖((fourierUnitary (f : SoninL2) : SoninL2) y)‖ ^ 2 := by
            apply integral_congr_ae
            filter_upwards [hqae] with y hy
            rw [hy]
      _ = ‖fourierUnitary (f : SoninL2)‖ ^ 2 :=
        (norm_sq_lp_eq_integral_norm_sq (fourierUnitary (f : SoninL2))).symm
      _ = ‖(f : SoninL2)‖ ^ 2 := by rw [fourierUnitary.norm_map]
      _ = ‖f‖ ^ 2 := rfl
  have hfix : evenIndicatorCutoff a f = f := (mem_evenTimeLimitedSubspace_iff a f).mp hf
  have hT : evenTimeBandFourier a f = evenIndicatorCutoff a (evenFourierTransform f) := by
    rw [evenTimeBandFourier_eq_mul]
    change evenIndicatorCutoff a (evenFourierTransform (evenIndicatorCutoff a f)) = _
    rw [hfix]
  have hTae : ((((evenTimeBandFourier a f : evenSubspace) : SoninL2) : ℝ → ℂ)) =ᵐ[volume]
      (Icc (-a) a).indicator q := by
    have hcut := indicatorCutoff_ae (Icc (-a) a) measurableSet_Icc
      (fourierUnitary (f : SoninL2))
    have hTcoe := congrArg (fun g : evenSubspace => (g : SoninL2)) hT
    change ((evenTimeBandFourier a f : evenSubspace) : SoninL2) =
      indicatorCutoff (Icc (-a) a) measurableSet_Icc
        (fourierUnitary (f : SoninL2)) at hTcoe
    filter_upwards [hcut, hqae] with y hycut hyq
    have hfun := congrArg (fun g : SoninL2 => (g : ℝ → ℂ)) hTcoe
    rw [congrFun hfun y, hycut]
    by_cases hy : y ∈ Icc (-a) a
    · simp [hy, hyq]
    · simp [hy]
  have hinterior : ∫ y in Icc (-a) a, ‖q y‖ ^ 2 = ‖evenTimeBandFourier a f‖ ^ 2 := by
    rw [← integral_indicator measurableSet_Icc]
    calc
      ∫ y : ℝ, (Icc (-a) a).indicator (fun y => ‖q y‖ ^ 2) y =
          ∫ y : ℝ, ‖(((evenTimeBandFourier a f : evenSubspace) : SoninL2) y)‖ ^ 2 := by
            apply integral_congr_ae
            filter_upwards [hTae] with y hy
            rw [hy]
            by_cases hya : y ∈ Icc (-a) a <;> simp [hya]
      _ = ‖((evenTimeBandFourier a f : evenSubspace) : SoninL2)‖ ^ 2 :=
        (norm_sq_lp_eq_integral_norm_sq
          ((evenTimeBandFourier a f : evenSubspace) : SoninL2)).symm
      _ = ‖evenTimeBandFourier a f‖ ^ 2 := rfl
  have hcomp : (Icc (-a) a)ᶜ = Iio (-a) ∪ Ioi a := by
    ext y
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le, mem_union, mem_Iio, mem_Ioi]
  have hdisj : Disjoint (Iio (-a)) (Ioi a) := by
    rw [Set.disjoint_left]
    intro y hy₁ hy₂
    change y < -a at hy₁
    change a < y at hy₂
    linarith [ha]
  have hexterior : ∫ y in (Icc (-a) a)ᶜ, ‖q y‖ ^ 2 =
      (∫ y in Iic (-a), ‖q y‖ ^ 2) + ∫ y in Ioi a, ‖q y‖ ^ 2 := by
    rw [hcomp, setIntegral_union₀ hdisj.aedisjoint measurableSet_Ioi.nullMeasurableSet
      hqint.integrableOn hqint.integrableOn, integral_Iic_eq_integral_Iio]
  rw [← hexterior, setIntegral_compl measurableSet_Icc hqint, htotal, hinterior]

theorem even_timeBandEigenFourierRepresentative
    (a : ℝ) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) :
    Function.Even (timeBandEigenFourierRepresentative a f χ hχ heig) := by
  have htime := mem_evenTimeLimitedSubspace_of_timeBand_eigen a f χ hχ heig
  exact even_evenTimeLimitedFourierRepresentative a f htime

theorem even_timeBandEigenPointwiseSource
    (a : ℝ) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) :
    Function.Even (timeBandEigenPointwiseSource a f χ hχ heig) := by
  intro x
  have hrep := even_timeBandEigenFourierRepresentative a f χ hχ heig x
  have hinterior : -x ∈ Ioo (-a) a ↔ x ∈ Ioo (-a) a := by
    simp only [mem_Ioo]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hendpoint : -x = -a ∨ -x = a ↔ x = -a ∨ x = a := by
    constructor <;> rintro (h | h)
    · right; linarith
    · left; linarith
    · right; linarith
    · left; linarith
  simp only [timeBandEigenPointwiseSource, hinterior, hendpoint, hrep]

theorem timeBandEigenPointwiseSource_eq_inv_mul_representative_interior
    (a : ℝ) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) {x : ℝ}
    (hx : x ∈ Ioo (-a) a) :
    timeBandEigenPointwiseSource a f χ hχ heig x =
      χ⁻¹ * timeBandEigenFourierRepresentative a f χ hχ heig x := by
  simp only [timeBandEigenPointwiseSource, if_pos hx]

theorem fourier_timeBandEigenPointwiseSource_eq_representative
    (a : ℝ) (ha : 0 ≤ a) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) (w : ℝ) :
    𝓕 (timeBandEigenPointwiseSource a f χ hχ heig) w =
      timeBandEigenFourierRepresentative a f χ hχ heig w := by
  have hae := ae_eq_timeBandEigenPointwiseSource a ha f χ hχ heig
  rw [Real.fourier_congr_ae hae w]
  have htime := mem_evenTimeLimitedSubspace_of_timeBand_eigen a f χ hχ heig
  have hcoe := MemLp.coeFn_toLp
    (memLp_one_iff_integrable.mpr
      (integrable_coe_of_mem_evenTimeLimitedSubspace a f htime))
  rw [Real.fourier_congr_ae hcoe.symm w]
  simp only [timeBandEigenFourierRepresentative, evenTimeLimitedFourierRepresentative,
    Real.Lp.fourierTransform_apply]

theorem hasDerivAt_timeBandEigenFourierRepresentative
    (a : ℝ) (ha : 0 ≤ a) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) (w : ℝ) :
    HasDerivAt (timeBandEigenFourierRepresentative a f χ hχ heig)
      (𝓕 (compactFourierFirstMoment
        (timeBandEigenPointwiseSource a f χ hχ heig)) w) w := by
  have hf := integrable_timeBandEigenPointwiseSource a ha f χ hχ heig
  have hsupp : ∀ x, x ∉ Icc (-a) a →
      timeBandEigenPointwiseSource a f χ hχ heig x = 0 := by
    intro x hx
    exact timeBandEigenPointwiseSource_eq_zero_of_not_mem_Icc
      a ha f χ hχ heig hx
  have h := hasDerivAt_fourier_compactSupport hf hsupp w
  have heq : 𝓕 (timeBandEigenPointwiseSource a f χ hχ heig) =
      (timeBandEigenFourierRepresentative a f χ hχ heig : ℝ → ℂ) := by
    funext y
    exact fourier_timeBandEigenPointwiseSource_eq_representative
      a ha f χ hχ heig y
  rw [heq] at h
  exact h

theorem hasDerivAt_timeBandEigenFourierFirstDerivative
    (a : ℝ) (ha : 0 ≤ a) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) (w : ℝ) :
    HasDerivAt
      (deriv (timeBandEigenFourierRepresentative a f χ hχ heig))
      (𝓕 (compactFourierSecondMoment
        (timeBandEigenPointwiseSource a f χ hχ heig)) w) w := by
  let g := timeBandEigenPointwiseSource a f χ hχ heig
  have hf : Integrable g := integrable_timeBandEigenPointwiseSource a ha f χ hχ heig
  have hsupp : ∀ x, x ∉ Icc (-a) a → g x = 0 :=
    fun x hx => timeBandEigenPointwiseSource_eq_zero_of_not_mem_Icc
      a ha f χ hχ heig hx
  have hsecond := hasDerivAt_fourier_compactFirstMoment hf hsupp w
  have hderiv : deriv (timeBandEigenFourierRepresentative a f χ hχ heig) =
      𝓕 (compactFourierFirstMoment g) := by
    funext y
    exact (hasDerivAt_timeBandEigenFourierRepresentative
      a ha f χ hχ heig y).deriv
  rw [hderiv]
  exact hsecond

theorem contDiff_timeBandEigenFourierRepresentative
    (a : ℝ) (ha : 0 ≤ a) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) :
    ContDiff ℝ (⊤ : ℕ∞) (timeBandEigenFourierRepresentative a f χ hχ heig) := by
  have hf := integrable_timeBandEigenPointwiseSource a ha f χ hχ heig
  have hsupp : ∀ x, x ∉ Icc (-a) a →
      timeBandEigenPointwiseSource a f χ hχ heig x = 0 := by
    intro x hx
    exact timeBandEigenPointwiseSource_eq_zero_of_not_mem_Icc
      a ha f χ hχ heig hx
  have h := contDiff_fourier_compactSupport hf hsupp
  have heq : 𝓕 (timeBandEigenPointwiseSource a f χ hχ heig) =
      (timeBandEigenFourierRepresentative a f χ hχ heig : ℝ → ℂ) := by
    funext y
    exact fourier_timeBandEigenPointwiseSource_eq_representative
      a ha f χ hχ heig y
  rw [heq] at h
  exact h

theorem iteratedDeriv_timeBandEigenFourierRepresentative
    (a : ℝ) (ha : 0 ≤ a) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) (n : ℕ) :
    iteratedDeriv n (timeBandEigenFourierRepresentative a f χ hχ heig) =
      𝓕 (fun x : ℝ =>
        (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ n •
          timeBandEigenPointwiseSource a f χ hχ heig x) := by
  have hf := integrable_timeBandEigenPointwiseSource a ha f χ hχ heig
  have hsupp : ∀ x, x ∉ Icc (-a) a →
      timeBandEigenPointwiseSource a f χ hχ heig x = 0 := by
    intro x hx
    exact timeBandEigenPointwiseSource_eq_zero_of_not_mem_Icc
      a ha f χ hχ heig hx
  have h := iteratedDeriv_fourier_compactSupport hf hsupp n
  have heq : 𝓕 (timeBandEigenPointwiseSource a f χ hχ heig) =
      (timeBandEigenFourierRepresentative a f χ hχ heig : ℝ → ℂ) := by
    funext y
    exact fourier_timeBandEigenPointwiseSource_eq_representative
      a ha f χ hχ heig y
  rw [heq] at h
  exact h

theorem contDiffOn_timeBandEigenPointwiseSource_interior
    {a : ℝ} (ha : 0 ≤ a) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) :
    ContDiffOn ℝ (⊤ : ℕ∞) (timeBandEigenPointwiseSource a f χ hχ heig) (Ioo (-a) a) := by
  have hrep : ContDiffOn ℝ (⊤ : ℕ∞)
      (timeBandEigenFourierRepresentative a f χ hχ heig) (Ioo (-a) a) :=
    (contDiff_timeBandEigenFourierRepresentative a ha f χ hχ heig).contDiffOn
  have hmul : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y => χ⁻¹ * timeBandEigenFourierRepresentative a f χ hχ heig y)
      (Ioo (-a) a) := contDiffOn_const.mul hrep
  exact hmul.congr fun x hx =>
    timeBandEigenPointwiseSource_eq_inv_mul_representative_interior
      a f χ hχ heig hx

theorem hasDerivAt_timeBandEigenPointwiseSource_interior
    {a : ℝ} (ha : 0 ≤ a) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) {x : ℝ} (hx : x ∈ Ioo (-a) a) :
    HasDerivAt (timeBandEigenPointwiseSource a f χ hχ heig)
      (χ⁻¹ * 𝓕 (compactFourierFirstMoment
        (timeBandEigenPointwiseSource a f χ hχ heig)) x) x := by
  have h := (hasDerivAt_timeBandEigenFourierRepresentative
    a ha f χ hχ heig x).const_mul χ⁻¹
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact timeBandEigenPointwiseSource_eq_inv_mul_representative_interior
    a f χ hχ heig hy

theorem hasDerivAt_timeBandEigenPointwiseSourceFirstDerivative_interior
    {a : ℝ} (ha : 0 ≤ a) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) {x : ℝ} (hx : x ∈ Ioo (-a) a) :
    HasDerivAt (deriv (timeBandEigenPointwiseSource a f χ hχ heig))
      (χ⁻¹ * 𝓕 (compactFourierSecondMoment
        (timeBandEigenPointwiseSource a f χ hχ heig)) x) x := by
  have h := (hasDerivAt_timeBandEigenFourierFirstDerivative
    a ha f χ hχ heig x).const_mul χ⁻¹
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  rw [(hasDerivAt_timeBandEigenPointwiseSource_interior
    ha f χ hχ heig hy).deriv,
    (hasDerivAt_timeBandEigenFourierRepresentative a ha f χ hχ heig y).deriv]

/-- The canonical compact representative satisfies the prolate Fourier eigen-equation at every
strictly interior point, with no almost-everywhere ambiguity. -/
theorem timeBandEigenPointwiseSource_eq_inv_mul_fourier_interior
    (a : ℝ) (ha : 0 ≤ a) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) {x : ℝ}
    (hx : x ∈ Ioo (-a) a) :
    timeBandEigenPointwiseSource a f χ hχ heig x =
      χ⁻¹ * 𝓕 (timeBandEigenPointwiseSource a f χ hχ heig) x := by
  rw [timeBandEigenPointwiseSource_eq_inv_mul_representative_interior a f χ hχ heig hx,
    fourier_timeBandEigenPointwiseSource_eq_representative a ha f χ hχ heig x]

/-- The physical-aperture eigen-equation rescaled exactly to the classical unit interval.
The Fourier character has frequency `a²`, corresponding to prolate bandwidth `2πa²`. -/
theorem timeBandEigenPointwiseSource_unitScale_eigen
    {a : ℝ} (ha : 0 < a) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    a • ∫ t in Icc (-1 : ℝ) 1,
        𝐞 (-((a * t) * (a * x))) •
          timeBandEigenPointwiseSource a f χ hχ heig (a * t) =
      χ * timeBandEigenPointwiseSource a f χ hχ heig (a * x) := by
  rw [fourier_compactSupport_unitScale ha
    (fun y hy => timeBandEigenPointwiseSource_eq_zero_of_not_mem_Icc
      a ha.le f χ hχ heig hy) x]
  have hax : a * x ∈ Ioo (-a) a := by
    constructor <;> nlinarith [hx.1, hx.2]
  rw [timeBandEigenPointwiseSource_eq_inv_mul_fourier_interior
    a ha.le f χ hχ heig hax]
  field_simp

/-- At the left aperture boundary the compact representative carries exactly half of the
Fourier-eigenfunction boundary value. -/
theorem timeBandEigenPointwiseSource_left_endpoint_eq_half_inv_mul_fourier
    (a : ℝ) (ha : 0 ≤ a) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) :
    timeBandEigenPointwiseSource a f χ hχ heig (-a) =
      (χ⁻¹ * 𝓕 (timeBandEigenPointwiseSource a f χ hχ heig) (-a)) / 2 := by
  rw [timeBandEigenPointwiseSource_left_endpoint,
    fourier_timeBandEigenPointwiseSource_eq_representative a ha f χ hχ heig (-a)]

/-- At the right aperture boundary the compact representative carries exactly half of the
Fourier-eigenfunction boundary value. -/
theorem timeBandEigenPointwiseSource_right_endpoint_eq_half_inv_mul_fourier
    (a : ℝ) (ha : 0 ≤ a) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) :
    timeBandEigenPointwiseSource a f χ hχ heig a =
      (χ⁻¹ * 𝓕 (timeBandEigenPointwiseSource a f χ hχ heig) a) / 2 := by
  rw [timeBandEigenPointwiseSource_right_endpoint,
    fourier_timeBandEigenPointwiseSource_eq_representative a ha f χ hχ heig a]

/-- Integral coordinate of a canonical nonzero time-band eigenmode source. -/
noncomputable def timeBandEigenSourceIntegral
    (a : ℝ) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) : ℂ :=
  ∫ x : ℝ, timeBandEigenPointwiseSource a f χ hχ heig x

/-- The universal unnormalized two-mode CCM contrast. Its coefficients are the opposite source
integrals, so cancellation of the total integral is algebraic and does not use asymptotics. -/
noncomputable def timeBandTwoModeConstrainedSource
    (a : ℝ)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) (x : ℝ) : ℂ :=
  timeBandEigenSourceIntegral a f₁ χ₁ hχ₁ heig₁ *
      timeBandEigenPointwiseSource a f₀ χ₀ hχ₀ heig₀ x -
    timeBandEigenSourceIntegral a f₀ χ₀ hχ₀ heig₀ *
      timeBandEigenPointwiseSource a f₁ χ₁ hχ₁ heig₁ x

theorem integrable_timeBandTwoModeConstrainedSource
    (a : ℝ) (ha : 0 ≤ a)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    Integrable (timeBandTwoModeConstrainedSource a f₀ χ₀ hχ₀ heig₀
      f₁ χ₁ hχ₁ heig₁) := by
  have h₀ := integrable_timeBandEigenPointwiseSource a ha f₀ χ₀ hχ₀ heig₀
  have h₁ := integrable_timeBandEigenPointwiseSource a ha f₁ χ₁ hχ₁ heig₁
  exact (h₀.const_mul (timeBandEigenSourceIntegral a f₁ χ₁ hχ₁ heig₁)).sub
    (h₁.const_mul (timeBandEigenSourceIntegral a f₀ χ₀ hχ₀ heig₀))

theorem hasCompactSupport_timeBandTwoModeConstrainedSource
    (a : ℝ) (ha : 0 ≤ a)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    HasCompactSupport (timeBandTwoModeConstrainedSource a f₀ χ₀ hχ₀ heig₀
      f₁ χ₁ hχ₁ heig₁) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro x hx
  have h₀ := timeBandEigenPointwiseSource_eq_zero_of_not_mem_Icc
    a ha f₀ χ₀ hχ₀ heig₀ hx
  have h₁ := timeBandEigenPointwiseSource_eq_zero_of_not_mem_Icc
    a ha f₁ χ₁ hχ₁ heig₁ hx
  simp only [timeBandTwoModeConstrainedSource, h₀, h₁, mul_zero, sub_zero]

theorem even_timeBandTwoModeConstrainedSource
    (a : ℝ)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    Function.Even (timeBandTwoModeConstrainedSource a f₀ χ₀ hχ₀ heig₀
      f₁ χ₁ hχ₁ heig₁) := by
  intro x
  rw [timeBandTwoModeConstrainedSource, timeBandTwoModeConstrainedSource,
    even_timeBandEigenPointwiseSource a f₀ χ₀ hχ₀ heig₀ x,
    even_timeBandEigenPointwiseSource a f₁ χ₁ hχ₁ heig₁ x]

theorem integral_timeBandTwoModeConstrainedSource_eq_zero
    (a : ℝ) (ha : 0 ≤ a)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    ∫ x : ℝ, timeBandTwoModeConstrainedSource a f₀ χ₀ hχ₀ heig₀
      f₁ χ₁ hχ₁ heig₁ x = 0 := by
  have h₀ := integrable_timeBandEigenPointwiseSource a ha f₀ χ₀ hχ₀ heig₀
  have h₁ := integrable_timeBandEigenPointwiseSource a ha f₁ χ₁ hχ₁ heig₁
  simp only [timeBandTwoModeConstrainedSource]
  rw [integral_sub
    (h₀.const_mul (timeBandEigenSourceIntegral a f₁ χ₁ hχ₁ heig₁))
    (h₁.const_mul (timeBandEigenSourceIntegral a f₀ χ₀ hχ₀ heig₀)),
    integral_const_mul, integral_const_mul]
  change timeBandEigenSourceIntegral a f₁ χ₁ hχ₁ heig₁ *
      timeBandEigenSourceIntegral a f₀ χ₀ hχ₀ heig₀ -
    timeBandEigenSourceIntegral a f₀ χ₀ hχ₀ heig₀ *
      timeBandEigenSourceIntegral a f₁ χ₁ hχ₁ heig₁ = 0
  ring

theorem contDiff_fourier_timeBandTwoModeConstrainedSource
    (a : ℝ) (ha : 0 ≤ a)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    ContDiff ℝ (⊤ : ℕ∞)
      (𝓕 (timeBandTwoModeConstrainedSource a f₀ χ₀ hχ₀ heig₀
        f₁ χ₁ hχ₁ heig₁)) := by
  exact contDiff_fourier_compactSupport
    (integrable_timeBandTwoModeConstrainedSource a ha
      f₀ χ₀ hχ₀ heig₀ f₁ χ₁ hχ₁ heig₁)
    (fun x hx => by
      have h₀ := timeBandEigenPointwiseSource_eq_zero_of_not_mem_Icc
        a ha f₀ χ₀ hχ₀ heig₀ hx
      have h₁ := timeBandEigenPointwiseSource_eq_zero_of_not_mem_Icc
        a ha f₁ χ₁ hχ₁ heig₁ hx
      simp only [timeBandTwoModeConstrainedSource, h₀, h₁, mul_zero, sub_zero])

theorem iteratedDeriv_fourier_timeBandTwoModeConstrainedSource
    (a : ℝ) (ha : 0 ≤ a)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) (n : ℕ) :
    iteratedDeriv n
      (𝓕 (timeBandTwoModeConstrainedSource a f₀ χ₀ hχ₀ heig₀
        f₁ χ₁ hχ₁ heig₁)) =
      𝓕 (fun x : ℝ =>
        (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ n •
          timeBandTwoModeConstrainedSource a f₀ χ₀ hχ₀ heig₀
            f₁ χ₁ hχ₁ heig₁ x) := by
  exact iteratedDeriv_fourier_compactSupport
    (integrable_timeBandTwoModeConstrainedSource a ha
      f₀ χ₀ hχ₀ heig₀ f₁ χ₁ hχ₁ heig₁)
    (fun x hx => by
      have h₀ := timeBandEigenPointwiseSource_eq_zero_of_not_mem_Icc
        a ha f₀ χ₀ hχ₀ heig₀ hx
      have h₁ := timeBandEigenPointwiseSource_eq_zero_of_not_mem_Icc
        a ha f₁ χ₁ hχ₁ heig₁ hx
      simp only [timeBandTwoModeConstrainedSource, h₀, h₁, mul_zero, sub_zero]) n

theorem contDiffOn_timeBandTwoModeConstrainedSource_interior
    {a : ℝ} (ha : 0 ≤ a)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (timeBandTwoModeConstrainedSource a f₀ χ₀ hχ₀ heig₀
        f₁ χ₁ hχ₁ heig₁) (Ioo (-a) a) := by
  have h₀ := contDiffOn_timeBandEigenPointwiseSource_interior
    ha f₀ χ₀ hχ₀ heig₀
  have h₁ := contDiffOn_timeBandEigenPointwiseSource_interior
    ha f₁ χ₁ hχ₁ heig₁
  exact (contDiffOn_const.mul h₀).sub (contDiffOn_const.mul h₁)

/-- The Fourier transform of the constrained two-mode source is the same opposite-integral
contrast of the two canonical continuous Fourier representatives. -/
theorem fourier_timeBandTwoModeConstrainedSource_eq
    (a : ℝ) (ha : 0 ≤ a)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) (w : ℝ) :
    𝓕 (timeBandTwoModeConstrainedSource a f₀ χ₀ hχ₀ heig₀
      f₁ χ₁ hχ₁ heig₁) w =
      timeBandEigenSourceIntegral a f₁ χ₁ hχ₁ heig₁ *
          timeBandEigenFourierRepresentative a f₀ χ₀ hχ₀ heig₀ w -
        timeBandEigenSourceIntegral a f₀ χ₀ hχ₀ heig₀ *
          timeBandEigenFourierRepresentative a f₁ χ₁ hχ₁ heig₁ w := by
  let g₀ := timeBandEigenPointwiseSource a f₀ χ₀ hχ₀ heig₀
  let g₁ := timeBandEigenPointwiseSource a f₁ χ₁ hχ₁ heig₁
  let c₀ := timeBandEigenSourceIntegral a f₁ χ₁ hχ₁ heig₁
  let c₁ := timeBandEigenSourceIntegral a f₀ χ₀ hχ₀ heig₀
  let φ : ℝ → ℂ := fun x => Complex.exp (↑(-2 * Real.pi * x * w) * Complex.I)
  have hφ : Continuous φ := by
    dsimp only [φ]
    fun_prop
  have hφnorm : ∀ x, ‖φ x‖ = 1 := by
    intro x
    simp only [φ, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self,
      Real.exp_zero]
  have hg₀ := integrable_timeBandEigenPointwiseSource a ha f₀ χ₀ hχ₀ heig₀
  have hg₁ := integrable_timeBandEigenPointwiseSource a ha f₁ χ₁ hχ₁ heig₁
  have hφg₀ : Integrable (φ • g₀) :=
    hg₀.bdd_smul 1 hφ.aestronglyMeasurable
      (Eventually.of_forall fun x => (hφnorm x).le)
  have hφg₁ : Integrable (φ • g₁) :=
    hg₁.bdd_smul 1 hφ.aestronglyMeasurable
      (Eventually.of_forall fun x => (hφnorm x).le)
  rw [Real.fourier_real_eq_integral_exp_smul]
  change (∫ x : ℝ, φ x • (c₀ * g₀ x - c₁ * g₁ x)) = _
  have hpoint : (fun x : ℝ => φ x • (c₀ * g₀ x - c₁ * g₁ x)) =
      fun x => c₀ * (φ x * g₀ x) - c₁ * (φ x * g₁ x) := by
    funext x
    simp only [smul_eq_mul]
    ring
  have hterm₀ : Integrable (fun x => c₀ * (φ x * g₀ x)) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! hφg₀.const_mul c₀
  have hterm₁ : Integrable (fun x => c₁ * (φ x * g₁ x)) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! hφg₁.const_mul c₁
  rw [hpoint, integral_sub hterm₀ hterm₁,
    integral_const_mul, integral_const_mul]
  have hFg₀ : (∫ x : ℝ, φ x * g₀ x) = 𝓕 g₀ w := by
    simpa only [φ, smul_eq_mul] using
      (Real.fourier_real_eq_integral_exp_smul g₀ w).symm
  have hFg₁ : (∫ x : ℝ, φ x * g₁ x) = 𝓕 g₁ w := by
    simpa only [φ, smul_eq_mul] using
      (Real.fourier_real_eq_integral_exp_smul g₁ w).symm
  rw [hFg₀, hFg₁]
  simp only [g₀, g₁, c₀, c₁,
    fourier_timeBandEigenPointwiseSource_eq_representative a ha]

/-- Continuous profile underneath the half-endpoint two-mode CCM source. -/
noncomputable def timeBandTwoModeContinuousProfile
    (a : ℝ)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) (x : ℝ) : ℂ :=
  timeBandEigenSourceIntegral a f₁ χ₁ hχ₁ heig₁ *
      (χ₀⁻¹ * timeBandEigenFourierRepresentative a f₀ χ₀ hχ₀ heig₀ x) -
    timeBandEigenSourceIntegral a f₀ χ₀ hχ₀ heig₀ *
      (χ₁⁻¹ * timeBandEigenFourierRepresentative a f₁ χ₁ hχ₁ heig₁ x)

theorem continuous_timeBandTwoModeContinuousProfile
    (a : ℝ)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    Continuous (timeBandTwoModeContinuousProfile a f₀ χ₀ hχ₀ heig₀
      f₁ χ₁ hχ₁ heig₁) := by
  apply Continuous.sub
  · apply Continuous.mul continuous_const
    apply Continuous.mul continuous_const
    exact continuous_evenTimeLimitedFourierRepresentative a f₀
      (mem_evenTimeLimitedSubspace_of_timeBand_eigen a f₀ χ₀ hχ₀ heig₀)
  · apply Continuous.mul continuous_const
    apply Continuous.mul continuous_const
    exact continuous_evenTimeLimitedFourierRepresentative a f₁
      (mem_evenTimeLimitedSubspace_of_timeBand_eigen a f₁ χ₁ hχ₁ heig₁)

theorem even_timeBandTwoModeContinuousProfile
    (a : ℝ)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    Function.Even (timeBandTwoModeContinuousProfile a f₀ χ₀ hχ₀ heig₀
      f₁ χ₁ hχ₁ heig₁) := by
  intro x
  simp only [timeBandTwoModeContinuousProfile]
  rw [even_timeBandEigenFourierRepresentative a f₀ χ₀ hχ₀ heig₀ x,
    even_timeBandEigenFourierRepresentative a f₁ χ₁ hχ₁ heig₁ x]

/-- Universal half-endpoint factorization of the constrained two-mode CCM source. -/
theorem timeBandTwoModeConstrainedSource_eq_halfEndpointCutoff
    (a : ℝ)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    timeBandTwoModeConstrainedSource a f₀ χ₀ hχ₀ heig₀ f₁ χ₁ hχ₁ heig₁ =
      GaloisForLFunctions.HTGeometry.symmetricHalfEndpointCutoff a
        (timeBandTwoModeContinuousProfile a f₀ χ₀ hχ₀ heig₀ f₁ χ₁ hχ₁ heig₁) := by
  funext x
  simp only [timeBandTwoModeConstrainedSource, timeBandEigenPointwiseSource,
    GaloisForLFunctions.HTGeometry.symmetricHalfEndpointCutoff,
    timeBandTwoModeContinuousProfile]
  split_ifs <;> ring

/-- Integer-aperture collisions create no Poisson jump: paired endpoint terms exchange exactly. -/
theorem continuousAt_l1Periodization_timeBandTwoModeConstrainedSource_zero
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    ContinuousAt
      (GaloisForLFunctions.HTGeometry.l1Periodization (fun y =>
        timeBandTwoModeConstrainedSource a f₀ χ₀ hχ₀ heig₀
          f₁ χ₁ hχ₁ heig₁ (y / b))) 0 := by
  rw [timeBandTwoModeConstrainedSource_eq_halfEndpointCutoff]
  exact GaloisForLFunctions.HTGeometry.continuousAt_l1Periodization_symmetricHalfEndpointCutoff_zero
    ha hb
    (continuous_timeBandTwoModeContinuousProfile a f₀ χ₀ hχ₀ heig₀
      f₁ χ₁ hχ₁ heig₁)
    (even_timeBandTwoModeContinuousProfile a f₀ χ₀ hχ₀ heig₀
      f₁ χ₁ hχ₁ heig₁)

/-- Real source extracted from the canonical complex two-mode CCM contrast. -/
noncomputable def timeBandTwoModeConstrainedRealSource
    (a : ℝ)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) (x : ℝ) : ℝ :=
  (timeBandTwoModeConstrainedSource a f₀ χ₀ hχ₀ heig₀
    f₁ χ₁ hχ₁ heig₁ x).re

/-- Real part of the continuous profile underneath the canonical CCM source. -/
noncomputable def timeBandTwoModeContinuousRealProfile
    (a : ℝ)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) (x : ℝ) : ℝ :=
  (timeBandTwoModeContinuousProfile a f₀ χ₀ hχ₀ heig₀
    f₁ χ₁ hχ₁ heig₁ x).re

theorem continuous_timeBandTwoModeContinuousRealProfile
    (a : ℝ)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    Continuous (timeBandTwoModeContinuousRealProfile a f₀ χ₀ hχ₀ heig₀
      f₁ χ₁ hχ₁ heig₁) := by
  exact Complex.continuous_re.comp
    (continuous_timeBandTwoModeContinuousProfile a f₀ χ₀ hχ₀ heig₀
      f₁ χ₁ hχ₁ heig₁)

theorem even_timeBandTwoModeContinuousRealProfile
    (a : ℝ)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    Function.Even (timeBandTwoModeContinuousRealProfile a f₀ χ₀ hχ₀ heig₀
      f₁ χ₁ hχ₁ heig₁) := by
  intro x
  simp only [timeBandTwoModeContinuousRealProfile]
  rw [even_timeBandTwoModeContinuousProfile a f₀ χ₀ hχ₀ heig₀
    f₁ χ₁ hχ₁ heig₁ x]

theorem timeBandTwoModeConstrainedRealSource_eq_halfEndpointCutoff
    (a : ℝ)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    timeBandTwoModeConstrainedRealSource a f₀ χ₀ hχ₀ heig₀ f₁ χ₁ hχ₁ heig₁ =
      GaloisForLFunctions.HTGeometry.realSymmetricHalfEndpointCutoff a
        (timeBandTwoModeContinuousRealProfile a f₀ χ₀ hχ₀ heig₀ f₁ χ₁ hχ₁ heig₁) := by
  funext x
  simp only [timeBandTwoModeConstrainedRealSource]
  rw [congrFun (timeBandTwoModeConstrainedSource_eq_halfEndpointCutoff
    a f₀ χ₀ hχ₀ heig₀ f₁ χ₁ hχ₁ heig₁) x]
  simp only [GaloisForLFunctions.HTGeometry.symmetricHalfEndpointCutoff,
    GaloisForLFunctions.HTGeometry.realSymmetricHalfEndpointCutoff,
    timeBandTwoModeContinuousRealProfile]
  split_ifs <;> norm_num

theorem integrable_timeBandTwoModeConstrainedRealSource
    (a : ℝ) (ha : 0 ≤ a)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    Integrable (timeBandTwoModeConstrainedRealSource a f₀ χ₀ hχ₀ heig₀
      f₁ χ₁ hχ₁ heig₁) := by
  exact (integrable_timeBandTwoModeConstrainedSource a ha
    f₀ χ₀ hχ₀ heig₀ f₁ χ₁ hχ₁ heig₁).re

theorem even_timeBandTwoModeConstrainedRealSource
    (a : ℝ)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    Function.Even (timeBandTwoModeConstrainedRealSource a f₀ χ₀ hχ₀ heig₀
      f₁ χ₁ hχ₁ heig₁) := by
  intro x
  simp only [timeBandTwoModeConstrainedRealSource]
  rw [even_timeBandTwoModeConstrainedSource a f₀ χ₀ hχ₀ heig₀
    f₁ χ₁ hχ₁ heig₁ x]

theorem hasCompactSupport_timeBandTwoModeConstrainedRealSource
    (a : ℝ) (ha : 0 ≤ a)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    HasCompactSupport (timeBandTwoModeConstrainedRealSource a f₀ χ₀ hχ₀ heig₀
      f₁ χ₁ hχ₁ heig₁) := by
  refine HasCompactSupport.intro (K := Icc (-a) a) isCompact_Icc ?_
  intro x hx
  have h₀ := timeBandEigenPointwiseSource_eq_zero_of_not_mem_Icc
    a ha f₀ χ₀ hχ₀ heig₀ hx
  have h₁ := timeBandEigenPointwiseSource_eq_zero_of_not_mem_Icc
    a ha f₁ χ₁ hχ₁ heig₁ hx
  simp only [timeBandTwoModeConstrainedRealSource,
    timeBandTwoModeConstrainedSource, h₀, h₁, mul_zero, sub_zero, Complex.zero_re]

theorem integral_timeBandTwoModeConstrainedRealSource_eq_zero
    (a : ℝ) (ha : 0 ≤ a)
    (f₀ : evenSubspace) (χ₀ : ℂ) (hχ₀ : χ₀ ≠ 0)
    (heig₀ : evenTimeBandFourier a f₀ = χ₀ • f₀)
    (f₁ : evenSubspace) (χ₁ : ℂ) (hχ₁ : χ₁ ≠ 0)
    (heig₁ : evenTimeBandFourier a f₁ = χ₁ • f₁) :
    ∫ x : ℝ, timeBandTwoModeConstrainedRealSource a f₀ χ₀ hχ₀ heig₀
      f₁ χ₁ hχ₁ heig₁ x = 0 := by
  have hg := integrable_timeBandTwoModeConstrainedSource a ha
    f₀ χ₀ hχ₀ heig₀ f₁ χ₁ hχ₁ heig₁
  change (∫ x : ℝ, (timeBandTwoModeConstrainedSource a f₀ χ₀ hχ₀ heig₀
    f₁ χ₁ hχ₁ heig₁ x).re) = 0
  rw [← RCLike.re_eq_complex_re, integral_re hg,
    integral_timeBandTwoModeConstrainedSource_eq_zero a ha
      f₀ χ₀ hχ₀ heig₀ f₁ χ₁ hχ₁ heig₁]
  norm_num

/-! ## Canonical representatives of the actual signed prolate modes -/

theorem eventually_evenProlateSignedValue_ne_zero (n : ℕ) :
    ∀ᶠ a : ℝ in atTop, evenProlateSignedValue a n ≠ 0 := by
  have hmem : ∀ᶠ a : ℝ in atTop,
      evenProlateSignedValue a n ^ 2 ∈ Ioo (1 / 2 : ℝ) (3 / 2 : ℝ) :=
    (evenProlateSignedValue_sq_tendsto_one n)
      (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hmem] with a ha
  intro hzero
  rw [hzero] at ha
  norm_num at ha

theorem evenProlateSignedMode_norm_eq_one
    {a : ℝ} {n : ℕ} (hvalue : evenProlateSignedValue a n ≠ 0) :
    ‖evenProlateSignedMode a n‖ = 1 := by
  rcases evenProlateSignedMode_norm_zero_or_one a n with hzero | hone
  · exact absurd (ContinuousLinearMap.sgVal_zero_of_dead hzero) hvalue
  · exact hone

def evenProlateSignedFourierRepresentative
    (a : ℝ) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) : ℝ →ᵇ ℂ :=
  timeBandEigenFourierRepresentative a (evenProlateSignedMode a n)
    (evenProlateSignedValue a n : ℂ) (Complex.ofReal_ne_zero.mpr hvalue)
    (evenTimeBandFourier_apply_signedMode a n)

def evenProlateSignedPointwiseSource
    (a : ℝ) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) : ℝ → ℂ :=
  timeBandEigenPointwiseSource a (evenProlateSignedMode a n)
    (evenProlateSignedValue a n : ℂ) (Complex.ofReal_ne_zero.mpr hvalue)
    (evenTimeBandFourier_apply_signedMode a n)

theorem even_evenProlateSignedFourierRepresentative
    (a : ℝ) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    Function.Even (evenProlateSignedFourierRepresentative a n hvalue) := by
  exact even_timeBandEigenFourierRepresentative a (evenProlateSignedMode a n)
    (evenProlateSignedValue a n : ℂ) (Complex.ofReal_ne_zero.mpr hvalue)
    (evenTimeBandFourier_apply_signedMode a n)

theorem even_evenProlateSignedPointwiseSource
    (a : ℝ) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    Function.Even (evenProlateSignedPointwiseSource a n hvalue) := by
  exact even_timeBandEigenPointwiseSource a (evenProlateSignedMode a n)
    (evenProlateSignedValue a n : ℂ) (Complex.ofReal_ne_zero.mpr hvalue)
    (evenTimeBandFourier_apply_signedMode a n)

theorem hasCompactSupport_evenProlateSignedPointwiseSource
    (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    HasCompactSupport (evenProlateSignedPointwiseSource a n hvalue) := by
  exact hasCompactSupport_timeBandEigenPointwiseSource a ha (evenProlateSignedMode a n)
    (evenProlateSignedValue a n : ℂ) (Complex.ofReal_ne_zero.mpr hvalue)
    (evenTimeBandFourier_apply_signedMode a n)

theorem integrable_evenProlateSignedPointwiseSource
    (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    Integrable (evenProlateSignedPointwiseSource a n hvalue) := by
  exact integrable_timeBandEigenPointwiseSource a ha (evenProlateSignedMode a n)
    (evenProlateSignedValue a n : ℂ) (Complex.ofReal_ne_zero.mpr hvalue)
    (evenTimeBandFourier_apply_signedMode a n)

theorem ae_eq_evenProlateSignedPointwiseSource
    (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    evenProlateSignedPointwiseSource a n hvalue =ᵐ[volume]
      (((evenProlateSignedMode a n : evenSubspace) : SoninL2) : ℝ → ℂ) := by
  exact ae_eq_timeBandEigenPointwiseSource a ha (evenProlateSignedMode a n)
    (evenProlateSignedValue a n : ℂ) (Complex.ofReal_ne_zero.mpr hvalue)
    (evenTimeBandFourier_apply_signedMode a n)

theorem integral_norm_sq_evenProlateSignedPointwiseSource_eq_one
    (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    ∫ x : ℝ, ‖evenProlateSignedPointwiseSource a n hvalue x‖ ^ 2 = 1 := by
  have hae := ae_eq_evenProlateSignedPointwiseSource a ha n hvalue
  have hnormae :
      (fun x : ℝ => ‖evenProlateSignedPointwiseSource a n hvalue x‖ ^ 2) =ᵐ[volume]
        (fun x : ℝ => ‖(((evenProlateSignedMode a n : evenSubspace) : SoninL2) : ℝ → ℂ) x‖ ^ 2) :=
    hae.fun_comp fun z : ℂ => ‖z‖ ^ 2
  rw [integral_congr_ae hnormae,
    ← RHTower.norm_sq_lp_eq_integral_norm_sq
      (((evenProlateSignedMode a n : evenSubspace) : SoninL2))]
  change ‖evenProlateSignedMode a n‖ ^ 2 = 1
  rw [evenProlateSignedMode_norm_eq_one hvalue]
  norm_num

theorem evenProlateSignedFourierRepresentative_exterior_energy_eq_leakage
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    (∫ y in Iic (-a), ‖evenProlateSignedFourierRepresentative a n hvalue y‖ ^ 2) +
        ∫ y in Ioi a, ‖evenProlateSignedFourierRepresentative a n hvalue y‖ ^ 2 =
      1 - evenProlateSignedValue a n ^ 2 := by
  have htime := evenProlateSignedMode_mem_timeLimited_of_value_ne_zero a hvalue
  have h := evenTimeLimitedFourierRepresentative_exterior_energy
    ha (evenProlateSignedMode a n) htime
  simp only [evenProlateSignedFourierRepresentative,
    timeBandEigenFourierRepresentative] at ⊢
  rw [h, evenProlateSignedMode_norm_eq_one hvalue,
    evenTimeBandFourier_apply_signedMode, norm_smul,
    evenProlateSignedMode_norm_eq_one hvalue]
  simp only [Complex.norm_real, Real.norm_eq_abs, mul_one, one_pow, sq_abs]

theorem fourier_evenProlateSignedPointwiseSource_eq_representative
    (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) (w : ℝ) :
    𝓕 (evenProlateSignedPointwiseSource a n hvalue) w =
      evenProlateSignedFourierRepresentative a n hvalue w := by
  exact fourier_timeBandEigenPointwiseSource_eq_representative a ha
    (evenProlateSignedMode a n) (evenProlateSignedValue a n : ℂ)
    (Complex.ofReal_ne_zero.mpr hvalue) (evenTimeBandFourier_apply_signedMode a n) w

theorem evenProlateSignedPointwiseSource_eq_inv_mul_fourier_interior
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0)
    {x : ℝ} (hx : x ∈ Ioo (-a) a) :
    evenProlateSignedPointwiseSource a n hvalue x =
      (evenProlateSignedValue a n : ℂ)⁻¹ *
        𝓕 (evenProlateSignedPointwiseSource a n hvalue) x := by
  exact timeBandEigenPointwiseSource_eq_inv_mul_fourier_interior a ha
    (evenProlateSignedMode a n) (evenProlateSignedValue a n : ℂ)
    (Complex.ofReal_ne_zero.mpr hvalue) (evenTimeBandFourier_apply_signedMode a n) hx

theorem evenProlateSignedPointwiseSource_unitScale_eigen
    {a : ℝ} (ha : 0 < a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    a • ∫ t in Icc (-1 : ℝ) 1,
        𝐞 (-((a * t) * (a * x))) •
          evenProlateSignedPointwiseSource a n hvalue (a * t) =
      (evenProlateSignedValue a n : ℂ) *
        evenProlateSignedPointwiseSource a n hvalue (a * x) := by
  exact timeBandEigenPointwiseSource_unitScale_eigen ha
    (evenProlateSignedMode a n) (evenProlateSignedValue a n : ℂ)
    (Complex.ofReal_ne_zero.mpr hvalue) (evenTimeBandFourier_apply_signedMode a n) hx

theorem hasDerivAt_evenProlateSignedFourierRepresentative
    (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) (w : ℝ) :
    HasDerivAt (evenProlateSignedFourierRepresentative a n hvalue)
      (𝓕 (compactFourierFirstMoment
        (evenProlateSignedPointwiseSource a n hvalue)) w) w := by
  exact hasDerivAt_timeBandEigenFourierRepresentative a ha
    (evenProlateSignedMode a n) (evenProlateSignedValue a n : ℂ)
    (Complex.ofReal_ne_zero.mpr hvalue) (evenTimeBandFourier_apply_signedMode a n) w

theorem contDiff_evenProlateSignedFourierRepresentative
    (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (evenProlateSignedFourierRepresentative a n hvalue) := by
  exact contDiff_timeBandEigenFourierRepresentative a ha
    (evenProlateSignedMode a n) (evenProlateSignedValue a n : ℂ)
    (Complex.ofReal_ne_zero.mpr hvalue) (evenTimeBandFourier_apply_signedMode a n)

theorem iteratedDeriv_evenProlateSignedFourierRepresentative
    (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) (m : ℕ) :
    iteratedDeriv m (evenProlateSignedFourierRepresentative a n hvalue) =
      𝓕 (fun x : ℝ =>
        (-2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) ^ m •
          evenProlateSignedPointwiseSource a n hvalue x) := by
  exact iteratedDeriv_timeBandEigenFourierRepresentative a ha
    (evenProlateSignedMode a n) (evenProlateSignedValue a n : ℂ)
    (Complex.ofReal_ne_zero.mpr hvalue) (evenTimeBandFourier_apply_signedMode a n) m

theorem contDiffOn_evenProlateSignedPointwiseSource_interior
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (evenProlateSignedPointwiseSource a n hvalue) (Ioo (-a) a) := by
  exact contDiffOn_timeBandEigenPointwiseSource_interior ha
    (evenProlateSignedMode a n) (evenProlateSignedValue a n : ℂ)
    (Complex.ofReal_ne_zero.mpr hvalue) (evenTimeBandFourier_apply_signedMode a n)

theorem hasDerivAt_evenProlateSignedFourierFirstDerivative
    (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0) (w : ℝ) :
    HasDerivAt (deriv (evenProlateSignedFourierRepresentative a n hvalue))
      (𝓕 (compactFourierSecondMoment
        (evenProlateSignedPointwiseSource a n hvalue)) w) w := by
  exact hasDerivAt_timeBandEigenFourierFirstDerivative a ha
    (evenProlateSignedMode a n) (evenProlateSignedValue a n : ℂ)
    (Complex.ofReal_ne_zero.mpr hvalue) (evenTimeBandFourier_apply_signedMode a n) w

theorem hasDerivAt_evenProlateSignedPointwiseSource_interior
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0)
    {x : ℝ} (hx : x ∈ Ioo (-a) a) :
    HasDerivAt (evenProlateSignedPointwiseSource a n hvalue)
      ((evenProlateSignedValue a n : ℂ)⁻¹ *
        𝓕 (compactFourierFirstMoment
          (evenProlateSignedPointwiseSource a n hvalue)) x) x := by
  exact hasDerivAt_timeBandEigenPointwiseSource_interior ha
    (evenProlateSignedMode a n) (evenProlateSignedValue a n : ℂ)
    (Complex.ofReal_ne_zero.mpr hvalue) (evenTimeBandFourier_apply_signedMode a n) hx

theorem hasDerivAt_evenProlateSignedPointwiseSourceFirstDerivative_interior
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ) (hvalue : evenProlateSignedValue a n ≠ 0)
    {x : ℝ} (hx : x ∈ Ioo (-a) a) :
    HasDerivAt (deriv (evenProlateSignedPointwiseSource a n hvalue))
      ((evenProlateSignedValue a n : ℂ)⁻¹ *
        𝓕 (compactFourierSecondMoment
          (evenProlateSignedPointwiseSource a n hvalue)) x) x := by
  exact hasDerivAt_timeBandEigenPointwiseSourceFirstDerivative_interior ha
    (evenProlateSignedMode a n) (evenProlateSignedValue a n : ℂ)
    (Complex.ofReal_ne_zero.mpr hvalue) (evenTimeBandFourier_apply_signedMode a n) hx

end RHTower
