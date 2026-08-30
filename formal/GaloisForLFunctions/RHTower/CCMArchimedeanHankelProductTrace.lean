import GaloisForLFunctions.RHTower.CCMArchimedeanHankelTrace
import GaloisForLFunctions.RHTower.CCMArchimedeanFourierCrossBlock
import GaloisForLFunctions.RHTower.FiniteTimeBandFourierCompact
import GaloisForLFunctions.HTGeometry.SeparableBuresIncidenceLaw
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Exact traces of products of CCM Hankel blocks

The trace of a product of two positive-quadrant Hankel operators is the first moment of the
product of their kernels:

`Tr(H_g H_h) = integral_0^infinity t g(t) h(t) dt`.

This is proved inside the actual operator trace.  Each Hankel block is identified both with an
`L2` synthesis operator and with the conjugate-kernel observer operator on the literal restricted
half-line carrier.  Hilbert--Schmidt cyclicity reduces the trace to the `L2` overlap of those two
kernel fields.  A measure-preserving additive shear then collapses the positive quadrant to the
first moment.  No diagonal-kernel trace principle is assumed.

This is classical Helton--Howe/Hankel trace infrastructure and carries no novelty claim.
-/

noncomputable section

open Complex ContinuousLinearMap Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Real SchwartzMap Topology

namespace RHTower

local instance cCMArchimedeanHankelProductTraceLocalInst1 : SFinite ccmPositiveMeasure := by
  unfold ccmPositiveMeasure
  infer_instance

local instance cCMArchimedeanHankelProductTraceLocalInst2 : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩

local instance cCMArchimedeanHankelProductTraceLocalInst3 : TopologicalSpace.SeparableSpace CCMPositiveL2 := inferInstance

/-! ## Literal restriction and extension of the positive half-line -/

/-- Restriction from full real-line `L2` to the literal positive-half-line measure. -/
def ccmPositiveRestriction : SoninL2 →L[ℂ] CCMPositiveL2 :=
  LpToLpRestrictCLM ℝ ℂ ℂ (volume : Measure ℝ) 2 (Ici 0)

/-- Extension by zero from the literal positive-half-line carrier. -/
def ccmPositiveExtension : CCMPositiveL2 →L[ℂ] SoninL2 :=
  lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) (volume : Measure ℝ) 2
    (Ici 0) measurableSet_Ici

theorem ccmPositiveRestriction_extension (f : CCMPositiveL2) :
    ccmPositiveRestriction (ccmPositiveExtension f) = f := by
  apply Lp.ext
  have hext : (ccmPositiveExtension f : ℝ → ℂ) =ᵐ[volume]
      (Ici 0).indicator f := by
    exact lpExtendByZeroCLM_coeFn (F := ℂ) (𝕜 := ℂ)
      (volume : Measure ℝ) 2 (Ici 0) measurableSet_Ici f
  have hextRestrict :
      ccmPositiveExtension f =ᵐ[ccmPositiveMeasure] fun x => f x := by
    change ∀ᵐ x ∂(volume : Measure ℝ).restrict (Ici 0),
      ccmPositiveExtension f x = f x
    rw [ae_restrict_iff' measurableSet_Ici]
    filter_upwards [hext] with x hx hxi
    simpa [hxi] using hx
  filter_upwards [
    LpToLpRestrictCLM_coeFn (μ := (volume : Measure ℝ)) (p := (2 : ENNReal))
      ℂ (Ici 0) (ccmPositiveExtension f),
    hextRestrict] with x hres hextx
  exact hres.trans hextx

theorem ccmPositiveExtension_restriction (f : SoninL2) :
    ccmPositiveExtension (ccmPositiveRestriction f) =
      ccmPositiveHalfLineProjection f := by
  apply Lp.ext
  have hext :
      (ccmPositiveExtension (ccmPositiveRestriction f) : ℝ → ℂ) =ᵐ[volume]
        (Ici 0).indicator (ccmPositiveRestriction f) := by
    exact lpExtendByZeroCLM_coeFn (F := ℂ) (𝕜 := ℂ)
      (volume : Measure ℝ) 2 (Ici 0) measurableSet_Ici (ccmPositiveRestriction f)
  have hresRestrict := LpToLpRestrictCLM_coeFn
    (μ := (volume : Measure ℝ)) (p := (2 : ENNReal)) ℂ (Ici 0) f
  have hres : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ici (0 : ℝ) →
      ccmPositiveRestriction f x = f x := by
    rw [← ae_restrict_iff' measurableSet_Ici]
    exact hresRestrict
  have hcut := indicatorCutoff_ae (Ici (0 : ℝ)) measurableSet_Ici f
  filter_upwards [hext, hres, hcut] with x hextx hresx hcutx
  rw [hextx]
  by_cases hx : x ∈ Ici (0 : ℝ)
  · rw [Set.indicator_of_mem hx, hresx hx]
    simpa only [ccmPositiveHalfLineProjection, Set.indicator_of_mem hx] using hcutx.symm
  · rw [Set.indicator_of_notMem hx]
    simpa only [ccmPositiveHalfLineProjection, Set.indicator_of_notMem hx] using hcutx.symm

/-! ## Hilbert--Schmidt value-kernel field -/

/-- The literal positive-half-line translate `x |-> g(x+t)`. -/
def ccmHankelValueSlice (g : 𝓢(ℝ, ℂ)) (t : ℝ) : CCMPositiveL2 :=
  ccmPositiveRestriction
    ((SchwartzMap.translateCLM ℂ t g).toLp 2 (volume : Measure ℝ))

theorem continuous_ccmHankelValueSlice (g : 𝓢(ℝ, ℂ)) :
    Continuous (ccmHankelValueSlice g) := by
  exact ccmPositiveRestriction.continuous.comp
    ((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).continuous.comp
      (continuous_ccmTranslateOrbit g))

theorem ccmHankelValueSlice_coeFn (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    (ccmHankelValueSlice g t : ℝ → ℂ) =ᵐ[ccmPositiveMeasure]
      fun x => g (x + t) := by
  have hres := LpToLpRestrictCLM_coeFn
    (μ := (volume : Measure ℝ)) (p := (2 : ENNReal)) ℂ (Ici 0)
      ((SchwartzMap.translateCLM ℂ t g).toLp 2 (volume : Measure ℝ))
  have hlp :
      (((SchwartzMap.translateCLM ℂ t g).toLp 2 (volume : Measure ℝ) : SoninL2) :
          ℝ → ℂ) =ᵐ[ccmPositiveMeasure]
        fun x => g (x + t) := by
    exact ae_restrict_of_ae
      (SchwartzMap.coeFn_toLp (SchwartzMap.translateCLM ℂ t g) 2 (volume : Measure ℝ))
  filter_upwards [hres, hlp] with x hresx hlpx
  exact hresx.trans hlpx

private theorem ccmHankelValue_pointwise_sq_le
    (g : 𝓢(ℝ, ℂ)) {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    ‖g (x + t)‖ ^ 2 ≤
      ccmValueDecayConstant g ^ 2 * (1 + x ^ 2)⁻¹ * (1 + t ^ 2)⁻¹ := by
  let C := ccmValueDecayConstant g
  let X := (1 + x ^ 2)⁻¹
  let T := (1 + t ^ 2)⁻¹
  have hC : 0 ≤ C := ccmValueDecayConstant_nonneg g
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hX1 : X ≤ 1 := by
    dsimp [X]
    exact (inv_le_one₀ (by positivity : 0 < 1 + x ^ 2)).2
      (by nlinarith [sq_nonneg x])
  have hT1 : T ≤ 1 := by
    dsimp [T]
    exact (inv_le_one₀ (by positivity : 0 < 1 + t ^ 2)).2
      (by nlinarith [sq_nonneg t])
  have hval : ‖g (x + t)‖ ≤ C * X * T := by
    simpa [C, X, T] using ccm_value_l1_majorant g hx ht
  calc
    ‖g (x + t)‖ ^ 2 ≤ (C * X * T) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg hC hX0) hT0)).2 hval
    _ = C ^ 2 * X ^ 2 * T ^ 2 := by ring
    _ ≤ C ^ 2 * X * T := by
      gcongr
      · nlinarith [mul_nonneg hX0 (sub_nonneg.mpr hX1)]
      · nlinarith [mul_nonneg hT0 (sub_nonneg.mpr hT1)]
    _ = ccmValueDecayConstant g ^ 2 * (1 + x ^ 2)⁻¹ * (1 + t ^ 2)⁻¹ := by
      rfl

theorem norm_ccmHankelValueSlice_sq_le
    (g : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 ≤ t) :
    ‖ccmHankelValueSlice g t‖ ^ 2 ≤
      ccmValueDecayConstant g ^ 2 * (1 + t ^ 2)⁻¹ * Real.pi := by
  rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  calc
    (∫ x : ℝ, ‖ccmHankelValueSlice g t x‖ ^ 2 ∂ccmPositiveMeasure) ≤
        ∫ x : ℝ, ccmValueDecayConstant g ^ 2 * (1 + t ^ 2)⁻¹ *
          (1 + x ^ 2)⁻¹ ∂ccmPositiveMeasure := by
      apply integral_mono_ae
      · exact (memLp_two_iff_integrable_sq_norm
          (Lp.aestronglyMeasurable (ccmHankelValueSlice g t))).mp
            (Lp.memLp (ccmHankelValueSlice g t))
      · exact (integrable_inv_one_add_sq.const_mul _).integrableOn
      · filter_upwards [ccmHankelValueSlice_coeFn g t,
          ae_restrict_mem measurableSet_Ici] with x hxval hx
        rw [hxval]
        simpa only [mul_assoc, mul_comm, mul_left_comm] using
          ccmHankelValue_pointwise_sq_le g hx ht
    _ = ccmValueDecayConstant g ^ 2 * (1 + t ^ 2)⁻¹ * (Real.pi / 2) := by
      rw [ccmPositiveMeasure, integral_const_mul, integral_Ici_eq_integral_Ioi,
        integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero]
    _ ≤ ccmValueDecayConstant g ^ 2 * (1 + t ^ 2)⁻¹ * Real.pi := by
      gcongr
      exact (half_le_self (le_of_lt Real.pi_pos))

theorem ccmHankelValueSlice_memLp (g : 𝓢(ℝ, ℂ)) :
    MemLp (ccmHankelValueSlice g) 2 ccmPositiveMeasure := by
  refine (memLp_two_iff_integrable_sq_norm
    (continuous_ccmHankelValueSlice g).aestronglyMeasurable).mpr ?_
  refine Integrable.mono'
    ((integrable_inv_one_add_sq.const_mul
      (ccmValueDecayConstant g ^ 2 * Real.pi)).integrableOn)
    ((continuous_ccmHankelValueSlice g).norm.pow 2).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖ccmHankelValueSlice g t‖)]
  calc
    ‖ccmHankelValueSlice g t‖ ^ 2 ≤
        ccmValueDecayConstant g ^ 2 * (1 + t ^ 2)⁻¹ * Real.pi :=
      norm_ccmHankelValueSlice_sq_le g ht
    _ = (ccmValueDecayConstant g ^ 2 * Real.pi) * (1 + t ^ 2)⁻¹ := by ring

/-- The square-integrable field of positive Hankel value slices. -/
def ccmHankelValueField (g : 𝓢(ℝ, ℂ)) :
    Lp CCMPositiveL2 2 ccmPositiveMeasure :=
  (ccmHankelValueSlice_memLp g).toLp (ccmHankelValueSlice g)

/-- Positive-half-line Hankel operator in value-kernel synthesis form. -/
def ccmHankelValueSynthesis (g : 𝓢(ℝ, ℂ)) :
    CCMPositiveL2 →L[ℂ] CCMPositiveL2 :=
  l2Synthesis ccmPositiveMeasure (ccmHankelValueField g)

/-- Positive-half-line Hankel operator in conjugate-kernel observer form. -/
def ccmHankelValueObserver (g : 𝓢(ℝ, ℂ)) :
    CCMPositiveL2 →L[ℂ] CCMPositiveL2 :=
  l2ObserverAnalysis ccmPositiveMeasure
    (ccmHankelValueField (SchwartzMap.conjSLM g))

theorem ccmHankelValueSynthesis_isHilbertSchmidt (g : 𝓢(ℝ, ℂ)) :
    (ccmHankelValueSynthesis g).IsHilbertSchmidt :=
  l2Synthesis_isHilbertSchmidt ccmPositiveMeasure (ccmHankelValueField g)

theorem ccmHankelValueObserver_isHilbertSchmidt (g : 𝓢(ℝ, ℂ)) :
    (ccmHankelValueObserver g).IsHilbertSchmidt :=
  l2ObserverAnalysis_isHilbertSchmidt ccmPositiveMeasure
    (ccmHankelValueField (SchwartzMap.conjSLM g))

/-! ## Exact synthesis and observer realizations -/

theorem ccmPositiveRestriction_schwartz_coeFn (f : 𝓢(ℝ, ℂ)) :
    (ccmPositiveRestriction (f.toLp 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[ccmPositiveMeasure] f := by
  have hres := LpToLpRestrictCLM_coeFn
    (μ := (volume : Measure ℝ)) (p := (2 : ENNReal)) ℂ (Ici 0)
      (f.toLp 2 (volume : Measure ℝ))
  have hlp : ((f.toLp 2 (volume : Measure ℝ) : SoninL2) : ℝ → ℂ)
      =ᵐ[ccmPositiveMeasure] f := by
    exact ae_restrict_of_ae (SchwartzMap.coeFn_toLp f 2 (volume : Measure ℝ))
  filter_upwards [hres, hlp] with x hresx hlpx
  exact hresx.trans hlpx

theorem ccmHankelValueField_coeFn (g : 𝓢(ℝ, ℂ)) :
    (ccmHankelValueField g : ℝ → CCMPositiveL2)
      =ᵐ[ccmPositiveMeasure] ccmHankelValueSlice g := by
  exact (ccmHankelValueSlice_memLp g).coeFn_toLp

theorem inner_ccmPositiveRestriction_schwartz_ccmHankelValueSlice
    (g h : 𝓢(ℝ, ℂ)) (t : ℝ) :
    inner ℂ (ccmPositiveRestriction (h.toLp 2 (volume : Measure ℝ)))
        (ccmHankelValueSlice g t) =
      ∫ x, g (x + t) * starRingEnd ℂ (h x) ∂ccmPositiveMeasure := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ccmPositiveRestriction_schwartz_coeFn h,
    ccmHankelValueSlice_coeFn g t] with x hh hg
  rw [hh, hg]
  simp only [RCLike.inner_apply]

theorem inner_ccmPositiveExtension (h : SoninL2) (v : CCMPositiveL2) :
    inner ℂ h (ccmPositiveExtension v) =
      inner ℂ (ccmPositiveRestriction h) v := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have hext : (ccmPositiveExtension v : ℝ → ℂ) =ᵐ[volume]
      (Ici 0).indicator v := by
    exact lpExtendByZeroCLM_coeFn (F := ℂ) (𝕜 := ℂ)
      (volume : Measure ℝ) 2 (Ici 0) measurableSet_Ici v
  have hres := LpToLpRestrictCLM_coeFn
    (μ := (volume : Measure ℝ)) (p := (2 : ENNReal)) ℂ (Ici 0) h
  have hres' : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ici (0 : ℝ) →
      ccmPositiveRestriction h x = h x := by
    rw [← ae_restrict_iff' measurableSet_Ici]
    exact hres
  calc
    (∫ x : ℝ, inner ℂ (h x) (ccmPositiveExtension v x)) =
        ∫ x : ℝ, (Ici 0).indicator (fun x => inner ℂ (h x) (v x)) x := by
      apply integral_congr_ae
      filter_upwards [hext] with x hx
      rw [hx]
      by_cases hxi : x ∈ Ici (0 : ℝ)
      · simp [hxi]
      · simp [hxi]
    _ = ∫ x : ℝ in Ici 0, inner ℂ (h x) (v x) :=
      integral_indicator measurableSet_Ici
    _ = ∫ x : ℝ, inner ℂ (ccmPositiveRestriction h x) (v x)
        ∂ccmPositiveMeasure := by
      change (∫ x : ℝ in Ici 0, inner ℂ (h x) (v x)) =
        ∫ x : ℝ in Ici 0, inner ℂ (ccmPositiveRestriction h x) (v x)
      apply setIntegral_congr_ae measurableSet_Ici
      filter_upwards [hres'] with x hx
      intro hxi
      rw [hx hxi]

/-- Full-line realization of the positive Hankel block through its value-kernel synthesis. -/
def ccmPositiveHankelSynthesisFull (g : 𝓢(ℝ, ℂ)) : SoninL2 →L[ℂ] SoninL2 :=
  ccmPositiveExtension ∘L ccmHankelValueSynthesis g ∘L ccmPositiveRestriction

theorem inner_ccmPositiveHankelSynthesisFull_schwartz
    (g u h : 𝓢(ℝ, ℂ)) :
    inner ℂ (h.toLp 2 (volume : Measure ℝ))
        (ccmPositiveHankelSynthesisFull g (u.toLp 2 (volume : Measure ℝ))) =
      ∫ y, u y *
        (∫ x, g (x + y) * starRingEnd ℂ (h x) ∂ccmPositiveMeasure)
        ∂ccmPositiveMeasure := by
  rw [ccmPositiveHankelSynthesisFull, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, inner_ccmPositiveExtension,
    ccmHankelValueSynthesis, l2Synthesis_apply]
  have hint : Integrable (fun y =>
      ccmPositiveRestriction (u.toLp 2 (volume : Measure ℝ)) y •
        ccmHankelValueField g y) ccmPositiveMeasure := by
    exact memLp_one_iff_integrable.mp
      ((Lp.memLp (ccmHankelValueField g)).smul
        (Lp.memLp (ccmPositiveRestriction (u.toLp 2 (volume : Measure ℝ)))))
  calc
    inner ℂ (ccmPositiveRestriction (h.toLp 2 (volume : Measure ℝ)))
        (∫ y, ccmPositiveRestriction (u.toLp 2 (volume : Measure ℝ)) y •
          ccmHankelValueField g y ∂ccmPositiveMeasure) =
        ∫ y, inner ℂ (ccmPositiveRestriction (h.toLp 2 (volume : Measure ℝ)))
          (ccmPositiveRestriction (u.toLp 2 (volume : Measure ℝ)) y •
            ccmHankelValueField g y) ∂ccmPositiveMeasure :=
      (integral_inner (𝕜 := ℂ) hint
        (ccmPositiveRestriction (h.toLp 2 (volume : Measure ℝ)))).symm
    _ = ∫ y, u y *
        (∫ x, g (x + y) * starRingEnd ℂ (h x) ∂ccmPositiveMeasure)
        ∂ccmPositiveMeasure := by
      apply integral_congr_ae
      filter_upwards [ccmPositiveRestriction_schwartz_coeFn u,
        ccmHankelValueField_coeFn g] with y hu hg
      rw [hu, hg, inner_smul_right,
        inner_ccmPositiveRestriction_schwartz_ccmHankelValueSlice]

theorem ccmPositiveHankelSynthesisFull_eq (g : 𝓢(ℝ, ℂ)) :
    ccmPositiveHankelSynthesisFull g = ccmPositiveHankel g := by
  apply ContinuousLinearMap.ext
  intro v
  let p : SoninL2 → Prop := fun v =>
    ccmPositiveHankelSynthesisFull g v = ccmPositiveHankel g v
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) v
  · exact isClosed_eq (ccmPositiveHankelSynthesisFull g).continuous
      (ccmPositiveHankel g).continuous
  · intro u
    apply sub_eq_zero.mp
    refine DenseRange.eq_zero_of_inner_right ℂ
      (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) ?_
    intro h
    rw [inner_sub_right]
    change inner ℂ (h.toLp 2 (volume : Measure ℝ))
          (ccmPositiveHankelSynthesisFull g (u.toLp 2 (volume : Measure ℝ))) -
        inner ℂ (h.toLp 2 (volume : Measure ℝ))
          (ccmPositiveHankel g (u.toLp 2 (volume : Measure ℝ))) = 0
    rw [inner_ccmPositiveHankelSynthesisFull_schwartz,
      inner_ccmPositiveHankel_schwartz, sub_self]

theorem ccmPositiveHankel_isHilbertSchmidt (g : 𝓢(ℝ, ℂ)) :
    (ccmPositiveHankel g).IsHilbertSchmidt := by
  rw [← ccmPositiveHankelSynthesisFull_eq g]
  exact ((ccmHankelValueSynthesis_isHilbertSchmidt g).comp_left
    ccmPositiveExtension).comp_right ccmPositiveRestriction

theorem ccmHankelValueObserver_schwartz_coeFn (g u : 𝓢(ℝ, ℂ)) :
    (ccmHankelValueObserver g
        (ccmPositiveRestriction (u.toLp 2 (volume : Measure ℝ))) : ℝ → ℂ)
      =ᵐ[ccmPositiveMeasure] fun x =>
        ∫ y, g (y + x) * u y ∂ccmPositiveMeasure := by
  have hobs := l2ObserverAnalysis_coeFn ccmPositiveMeasure
    (ccmHankelValueField (SchwartzMap.conjSLM g))
      (ccmPositiveRestriction (u.toLp 2 (volume : Measure ℝ)))
  filter_upwards [hobs, ccmHankelValueField_coeFn (SchwartzMap.conjSLM g)]
      with x hobsx hfieldx
  rw [ccmHankelValueObserver, hobsx, hfieldx, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ccmHankelValueSlice_coeFn (SchwartzMap.conjSLM g) x,
    ccmPositiveRestriction_schwartz_coeFn u] with y hgy huy
  rw [hgy, huy]
  simp only [RCLike.inner_apply, SchwartzMap.conjSLM_apply]
  rw [starRingEnd_apply, starRingEnd_apply, star_star, mul_comm]

/-- Full-line realization of the positive Hankel block through conjugate-kernel analysis. -/
def ccmPositiveHankelObserverFull (g : 𝓢(ℝ, ℂ)) : SoninL2 →L[ℂ] SoninL2 :=
  ccmPositiveExtension ∘L ccmHankelValueObserver g ∘L ccmPositiveRestriction

theorem inner_ccmPositiveHankelObserverFull_schwartz
    (g u h : 𝓢(ℝ, ℂ)) :
    inner ℂ (h.toLp 2 (volume : Measure ℝ))
        (ccmPositiveHankelObserverFull g (u.toLp 2 (volume : Measure ℝ))) =
      ∫ y, u y *
        (∫ x, g (x + y) * starRingEnd ℂ (h x) ∂ccmPositiveMeasure)
        ∂ccmPositiveMeasure := by
  rw [ccmPositiveHankelObserverFull, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, inner_ccmPositiveExtension,
    MeasureTheory.L2.inner_def]
  calc
    (∫ x, inner ℂ
        (ccmPositiveRestriction (h.toLp 2 (volume : Measure ℝ)) x)
        (ccmHankelValueObserver g
          (ccmPositiveRestriction (u.toLp 2 (volume : Measure ℝ))) x)
        ∂ccmPositiveMeasure) =
        ∫ x, ∫ y, ccmHankelPairKernel g u h x y
          ∂ccmPositiveMeasure ∂ccmPositiveMeasure := by
      apply integral_congr_ae
      filter_upwards [ccmPositiveRestriction_schwartz_coeFn h,
        ccmHankelValueObserver_schwartz_coeFn g u] with x hh hobs
      rw [hh, hobs, RCLike.inner_apply, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with y
      simp only [ccmHankelPairKernel]
      ring
    _ = ∫ y, ∫ x, ccmHankelPairKernel g u h x y
          ∂ccmPositiveMeasure ∂ccmPositiveMeasure :=
      ccm_hankel_pair_fubini g u h
    _ = ∫ y, u y *
        (∫ x, g (x + y) * starRingEnd ℂ (h x) ∂ccmPositiveMeasure)
        ∂ccmPositiveMeasure := by
      apply integral_congr_ae
      filter_upwards with y
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      simp only [ccmHankelPairKernel]
      ring

theorem ccmPositiveHankelObserverFull_eq (g : 𝓢(ℝ, ℂ)) :
    ccmPositiveHankelObserverFull g = ccmPositiveHankel g := by
  apply ContinuousLinearMap.ext
  intro v
  let p : SoninL2 → Prop := fun v =>
    ccmPositiveHankelObserverFull g v = ccmPositiveHankel g v
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) v
  · exact isClosed_eq (ccmPositiveHankelObserverFull g).continuous
      (ccmPositiveHankel g).continuous
  · intro u
    apply sub_eq_zero.mp
    refine DenseRange.eq_zero_of_inner_right ℂ
      (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) ?_
    intro h
    rw [inner_sub_right]
    change inner ℂ (h.toLp 2 (volume : Measure ℝ))
          (ccmPositiveHankelObserverFull g (u.toLp 2 (volume : Measure ℝ))) -
        inner ℂ (h.toLp 2 (volume : Measure ℝ))
          (ccmPositiveHankel g (u.toLp 2 (volume : Measure ℝ))) = 0
    rw [inner_ccmPositiveHankelObserverFull_schwartz,
      inner_ccmPositiveHankel_schwartz, sub_self]

theorem adjoint_ccmPositiveExtension :
    ContinuousLinearMap.adjoint ccmPositiveExtension = ccmPositiveRestriction := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff
    ccmPositiveRestriction ccmPositiveExtension).mpr
  intro h v
  exact (inner_ccmPositiveExtension h v).symm

theorem adjoint_ccmPositiveRestriction :
    ContinuousLinearMap.adjoint ccmPositiveRestriction = ccmPositiveExtension := by
  rw [← adjoint_ccmPositiveExtension,
    ContinuousLinearMap.adjoint_adjoint]

private theorem ccmProductTrace_l2Reflection_ae (v : SoninL2) :
    l2Reflection v =ᵐ[volume] fun x : ℝ => v (-x) :=
  MeasureTheory.Lp.coeFn_compMeasurePreserving v
    (Measure.measurePreserving_neg (volume : Measure ℝ))

private theorem ccmProductTrace_l2Reflection_involutive (v : SoninL2) :
    l2Reflection (l2Reflection v) = v := by
  apply Lp.ext
  have hinner := (ccmProductTrace_l2Reflection_ae v).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [ccmProductTrace_l2Reflection_ae (l2Reflection v), hinner]
      with x hout hin
  rw [hout]
  simpa [Function.comp_apply] using hin

theorem adjoint_ccmL2Reflection :
    ContinuousLinearMap.adjoint l2Reflection = l2Reflection := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff l2Reflection l2Reflection).mpr
  intro f g
  calc
    inner ℂ (l2Reflection f) g =
        inner ℂ (l2Reflection (l2Reflection f)) (l2Reflection g) :=
      (l2ReflectionIsometry.inner_map_map (l2Reflection f) g).symm
    _ = inner ℂ f (l2Reflection g) := by
      rw [ccmProductTrace_l2Reflection_involutive]

theorem adjoint_ccmPositiveHankel (g : 𝓢(ℝ, ℂ)) :
    ContinuousLinearMap.adjoint (ccmPositiveHankel g) =
      ccmPositiveHankel (SchwartzMap.conjSLM g) := by
  rw [← ccmPositiveHankelSynthesisFull_eq g,
    ccmPositiveHankelSynthesisFull,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    adjoint_ccmPositiveRestriction,
    ccmHankelValueSynthesis,
    adjoint_l2Synthesis,
    adjoint_ccmPositiveExtension,
    ← ccmPositiveHankelObserverFull_eq (SchwartzMap.conjSLM g)]
  unfold ccmPositiveHankelObserverFull ccmHankelValueObserver
  have hc : SchwartzMap.conjSLM (SchwartzMap.conjSLM g) = g := by
    ext x
    simp
  rw [hc]
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem opTrace_ccmPositiveHankel_comp_eq_inner_valueFields
    (g h : 𝓢(ℝ, ℂ)) :
    opTrace (ccmPositiveHankel g ∘L ccmPositiveHankel h) =
      inner ℂ (ccmHankelValueField (SchwartzMap.conjSLM h))
        (ccmHankelValueField g) := by
  let A : CCMPositiveL2 →L[ℂ] SoninL2 :=
    ccmPositiveExtension ∘L ccmHankelValueSynthesis g
  let B : SoninL2 →L[ℂ] CCMPositiveL2 :=
    ccmHankelValueObserver h ∘L ccmPositiveRestriction
  have hA : A.IsHilbertSchmidt :=
    (ccmHankelValueSynthesis_isHilbertSchmidt g).comp_left ccmPositiveExtension
  have hB : B.IsHilbertSchmidt :=
    (ccmHankelValueObserver_isHilbertSchmidt h).comp_right ccmPositiveRestriction
  have hprod : ccmPositiveHankel g ∘L ccmPositiveHankel h = A ∘L B := by
    rw [← ccmPositiveHankelSynthesisFull_eq g,
      ← ccmPositiveHankelObserverFull_eq h]
    apply ContinuousLinearMap.ext
    intro v
    simp only [ccmPositiveHankelSynthesisFull, ccmPositiveHankelObserverFull,
      A, B, ContinuousLinearMap.comp_apply]
    rw [ccmPositiveRestriction_extension]
  rw [hprod, ContinuousLinearMap.opTrace_comp_comm hA hB]
  have hBA : B ∘L A =
      ccmHankelValueObserver h ∘L ccmHankelValueSynthesis g := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [A, B, ContinuousLinearMap.comp_apply]
    rw [ccmPositiveRestriction_extension]
  rw [hBA]
  simpa only [ccmHankelValueObserver, ccmHankelValueSynthesis,
    l2SheetTargetIncidence, sheetTargetIncidence, adjoint_l2Synthesis] using
    (opTrace_l2SheetTargetIncidence_eq_inner ccmPositiveMeasure
      (ccmHankelValueField (SchwartzMap.conjSLM h))
      (ccmHankelValueField g))

theorem inner_ccmHankelValueSlice_conj_eq_integral
    (g h : 𝓢(ℝ, ℂ)) (t : ℝ) :
    inner ℂ (ccmHankelValueSlice (SchwartzMap.conjSLM h) t)
        (ccmHankelValueSlice g t) =
      ∫ x, g (x + t) * h (x + t) ∂ccmPositiveMeasure := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ccmHankelValueSlice_coeFn (SchwartzMap.conjSLM h) t,
    ccmHankelValueSlice_coeFn g t] with x hh hg
  rw [hh, hg]
  simp only [RCLike.inner_apply, SchwartzMap.conjSLM_apply]
  rw [starRingEnd_apply, starRingEnd_apply, star_star]

theorem inner_ccmHankelValueFields_eq_integral_integral
    (g h : 𝓢(ℝ, ℂ)) :
    inner ℂ (ccmHankelValueField (SchwartzMap.conjSLM h))
        (ccmHankelValueField g) =
      ∫ t, ∫ x, g (x + t) * h (x + t)
        ∂ccmPositiveMeasure ∂ccmPositiveMeasure := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ccmHankelValueField_coeFn (SchwartzMap.conjSLM h),
    ccmHankelValueField_coeFn g] with t hh hg
  rw [hh, hg, inner_ccmHankelValueSlice_conj_eq_integral]

/-- Pointwise product of two complex Schwartz functions. -/
def ccmSchwartzProduct (g h : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (g : ℝ → ℂ) h

@[simp] theorem ccmSchwartzProduct_apply (g h : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ccmSchwartzProduct g h x = g x * h x := by
  rw [ccmSchwartzProduct,
    SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth, smul_eq_mul]

theorem integrable_ccmPositiveSumKernel (q : 𝓢(ℝ, ℂ)) :
    Integrable (fun p : ℝ × ℝ => q (p.1 + p.2))
      (ccmPositiveMeasure.prod ccmPositiveMeasure) := by
  let C : ℝ := ccmValueDecayConstant q
  have hC : 0 ≤ C := ccmValueDecayConstant_nonneg q
  have hinv : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) ccmPositiveMeasure :=
    integrable_inv_one_add_sq.integrableOn
  have hmajor : Integrable (fun p : ℝ × ℝ =>
      C * (1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹)
      (ccmPositiveMeasure.prod ccmPositiveMeasure) := by
    simpa only [mul_assoc] using (hinv.mul_prod hinv).const_mul C
  refine Integrable.mono' hmajor
    ((q.continuous.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable) ?_
  rw [ccmPositiveMeasure, Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ici.prod measurableSet_Ici)] with p hp
  simpa only [C] using ccm_value_l1_majorant q hp.1 hp.2

private theorem integral_ccmPositiveSumKernel_eq_firstMoment (q : 𝓢(ℝ, ℂ)) :
    (∫ t, ∫ x, q (x + t) ∂ccmPositiveMeasure ∂ccmPositiveMeasure) =
      ∫ s, (s : ℂ) * q s ∂ccmPositiveMeasure := by
  let μ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume
  let Q : Set (ℝ × ℝ) := Ici 0 ×ˢ Ici 0
  let T : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ p.2}
  let raw : ℝ × ℝ → ℂ := fun p => q (p.2 + p.1)
  let G : ℝ × ℝ → ℂ := Q.indicator raw
  let F : ℝ × ℝ → ℂ := T.indicator (fun p => q p.2)
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ := MeasurableEquiv.shearAddRight ℝ
  have hQ : MeasurableSet Q := measurableSet_Ici.prod measurableSet_Ici
  have hT : MeasurableSet T := by
    exact (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_snd)
  have hraw : Integrable raw (ccmPositiveMeasure.prod ccmPositiveMeasure) := by
    simpa only [raw, add_comm] using integrable_ccmPositiveSumKernel q
  have hG : Integrable G μ := by
    have hrawOn : IntegrableOn raw Q μ := by
      change Integrable raw (μ.restrict Q)
      simpa only [μ, Q, ccmPositiveMeasure, Measure.prod_restrict] using hraw
    exact hrawOn.integrable_indicator hQ
  have hFmeas : AEStronglyMeasurable F μ := by
    exact ((q.continuous.comp continuous_snd).measurable.indicator hT).aestronglyMeasurable
  have hshear (p : ℝ × ℝ) : F (e p) = G p := by
    dsimp [F, G, T, Q, raw, e]
    rw [show MeasurableEquiv.shearAddRight ℝ p = (p.1, p.1 + p.2) by rfl]
    simp only [Set.indicator, mem_setOf_eq, mem_prod, mem_Ici]
    by_cases hp : 0 ≤ p.1
    · by_cases hq : 0 ≤ p.2
      · have hadd : p.1 ≤ p.1 + p.2 := by linarith
        rw [if_pos ⟨hp, hadd⟩, if_pos ⟨hp, hq⟩]
        congr 1
        ring
      · have hnot : ¬ p.1 ≤ p.1 + p.2 := by linarith
        rw [if_neg (fun h => hnot h.2), if_neg (fun h => hq h.2)]
    · rw [if_neg (fun h => hp h.1), if_neg (fun h => hp h.1)]
  have hmp : MeasurePreserving e μ μ := by
    exact measurePreserving_prod_add volume volume
  have hF : Integrable F μ := by
    apply (hmp.integrable_comp hFmeas).mp
    have hc : F ∘ e = G := funext hshear
    rw [hc]
    exact hG
  have hshearIntegral : (∫ p, G p ∂μ) = ∫ p, F p ∂μ := by
    calc
      (∫ p, G p ∂μ) = ∫ p, F (e p) ∂μ := by
        apply integral_congr_ae
        filter_upwards with p
        exact (hshear p).symm
      _ = ∫ p, F p ∂μ := hmp.integral_comp' F
  have hinner (s : ℝ) :
      (∫ t : ℝ, F (t, s)) =
        (Ici 0).indicator (fun s : ℝ => (s : ℂ) * q s) s := by
    dsimp [F, T]
    simp only [Set.indicator, mem_setOf_eq, Prod.fst, Prod.snd]
    by_cases hs : 0 ≤ s
    · have hsmem : s ∈ Ici (0 : ℝ) := hs
      rw [if_pos hsmem]
      have hfun : (fun t : ℝ => if 0 ≤ t ∧ t ≤ s then q s else 0) =
          (Icc 0 s).indicator (fun _ => q s) := by
        funext t
        simp only [Set.indicator, mem_Icc]
      rw [hfun, integral_indicator measurableSet_Icc, integral_const]
      simp [hs]
    · have hsnot : s ∉ Ici (0 : ℝ) := hs
      rw [if_neg hsnot]
      have hfun : (fun t : ℝ => if 0 ≤ t ∧ t ≤ s then q s else 0) = 0 := by
        funext t
        simp only [Pi.zero_apply]
        rw [if_neg]
        intro h
        linarith [h.1, h.2]
      rw [hfun]
      simp
  calc
    (∫ t, ∫ x, q (x + t) ∂ccmPositiveMeasure ∂ccmPositiveMeasure) =
        ∫ p, raw p ∂(ccmPositiveMeasure.prod ccmPositiveMeasure) := by
      rw [integral_prod raw hraw]
    _ = ∫ p, G p ∂μ := by
      change (∫ p, raw p ∂(ccmPositiveMeasure.prod ccmPositiveMeasure)) =
        ∫ p, Q.indicator raw p ∂μ
      rw [integral_indicator hQ]
      simpa only [μ, Q, ccmPositiveMeasure, Measure.prod_restrict]
    _ = ∫ p, F p ∂μ := hshearIntegral
    _ = ∫ s : ℝ, ∫ t : ℝ, F (t, s) := by
      exact integral_prod_symm F hF
    _ = ∫ s : ℝ, (Ici 0).indicator (fun s : ℝ => (s : ℂ) * q s) s := by
      apply integral_congr_ae
      filter_upwards with s
      exact hinner s
    _ = ∫ s : ℝ in Ici 0, (s : ℂ) * q s :=
      integral_indicator measurableSet_Ici
    _ = ∫ s, (s : ℂ) * q s ∂ccmPositiveMeasure := rfl

/-- Exact trace of a product of two literal positive-quadrant CCM Hankel blocks. -/
theorem opTrace_ccmPositiveHankel_comp (g h : 𝓢(ℝ, ℂ)) :
    opTrace (ccmPositiveHankel g ∘L ccmPositiveHankel h) =
      ∫ t, (t : ℂ) * g t * h t ∂ccmPositiveMeasure := by
  rw [opTrace_ccmPositiveHankel_comp_eq_inner_valueFields,
    inner_ccmHankelValueFields_eq_integral_integral]
  calc
    (∫ t, ∫ x, g (x + t) * h (x + t)
        ∂ccmPositiveMeasure ∂ccmPositiveMeasure) =
        ∫ t, ∫ x, ccmSchwartzProduct g h (x + t)
          ∂ccmPositiveMeasure ∂ccmPositiveMeasure := by
      simp only [ccmSchwartzProduct_apply]
    _ = ∫ t, (t : ℂ) * ccmSchwartzProduct g h t ∂ccmPositiveMeasure :=
      integral_ccmPositiveSumKernel_eq_firstMoment (ccmSchwartzProduct g h)
    _ = ∫ t, (t : ℂ) * g t * h t ∂ccmPositiveMeasure := by
      simp only [ccmSchwartzProduct_apply, mul_assoc]

end RHTower
