import GaloisForLFunctions.RHTower.ConstrainedProlateOperator
import GaloisForLFunctions.RHTower.L2FourierIntegralBridge
import GaloisForLFunctions.HTGeometry.SymmetricHalfEndpointPeriodization

noncomputable section

open MeasureTheory Set FourierTransform Filter Topology
open scoped ENNReal BoundedContinuousFunction FourierTransform

namespace RHTower

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
open scoped ENNReal BoundedContinuousFunction FourierTransform

namespace RHTower

theorem even_timeBandEigenFourierRepresentative
    (a : ℝ) (f : evenSubspace) (χ : ℂ) (hχ : χ ≠ 0)
    (heig : evenTimeBandFourier a f = χ • f) :
    Function.Even (timeBandEigenFourierRepresentative a f χ hχ heig) := by
  let G : ℝ → ℂ := timeBandEigenFourierRepresentative a f χ hχ heig
  have htime := mem_evenTimeLimitedSubspace_of_timeBand_eigen a f χ hχ heig
  have hbridge := ae_eq_evenTimeLimitedFourierRepresentative a f htime
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
    have hxG : G x = evenTimeLimitedFourierRepresentative a f htime x := rfl
    have hnegG : G (-x) = evenTimeLimitedFourierRepresentative a f htime (-x) := rfl
    rw [hnegG, ← hxneg, ← href, hx, ← hxG]
  have hright : Continuous G := by
    simpa only [G, timeBandEigenFourierRepresentative] using
      continuous_evenTimeLimitedFourierRepresentative a f htime
  have hleft : Continuous (fun x : ℝ => G (-x)) :=
    hright.comp continuous_neg
  exact congrFun ((hleft.ae_eq_iff_eq volume hright).mp hGae)

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

end RHTower
