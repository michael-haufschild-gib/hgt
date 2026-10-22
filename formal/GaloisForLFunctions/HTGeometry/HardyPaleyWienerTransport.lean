import GaloisForLFunctions.HTGeometry.HardyHorizontalLayerLeakage
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelCompressionBridge
import GaloisForLFunctions.HTGeometry.HalfLineExponentialGram

open Complex Filter Topology MeasureTheory Set
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

abbrev HalfLineExponentialL2 := Lp ℂ 2 halfLineLaplaceMeasure

def paleyWienerScale : ℝ := 2 * Real.pi

theorem paleyWienerScale_pos : 0 < paleyWienerScale := by
  unfold paleyWienerScale
  positivity

def paleyPositiveDatumIsometry : HalfLineExponentialL2 →ₗᵢ[ℂ] RealLineL2 :=
  (RHTower.dilation paleyWienerScale paleyWienerScale_pos).comp
    RHTower.suzukiPositiveZeroExtensionIsometry

theorem paleyPositiveDatum_mem_halfLineL2 (f : HalfLineExponentialL2) :
    paleyPositiveDatumIsometry f ∈ RHTower.halfLineL2 := by
  rw [RHTower.mem_halfLineL2_iff]
  change ∀ᵐ x : ℝ, x < 0 →
    (((RHTower.dilation paleyWienerScale paleyWienerScale_pos)
      (RHTower.suzukiPositiveZeroExtension f) : RealLineL2) : ℝ → ℂ) x = 0
  have hz := (RHTower.suzukiPositiveZeroExtension_ae f).comp_tendsto
    (RHTower.realMul_quasiMeasurePreserving paleyWienerScale
      paleyWienerScale_pos.ne').tendsto_ae
  have hd := RHTower.dilation_ae paleyWienerScale paleyWienerScale_pos
    (RHTower.suzukiPositiveZeroExtension f)
  filter_upwards [hz, hd] with x hx hdx hneg
  rw [hdx]
  have hsneg : paleyWienerScale * x < 0 :=
    mul_neg_of_pos_of_neg paleyWienerScale_pos hneg
  have hx' : RHTower.suzukiPositiveZeroExtension f (paleyWienerScale * x) =
      RHTower.suzukiPositiveZeroExtensionFun f (paleyWienerScale * x) := by
    simpa only [Function.comp_apply] using hx
  rw [hx', RHTower.suzukiPositiveZeroExtensionFun,
    indicator_of_notMem (show paleyWienerScale * x ∉ Ioi (0 : ℝ) by simpa using hsneg.le)]
  simp

def paleyNegativeDatumIsometry : HalfLineExponentialL2 →ₗᵢ[ℂ] RealLineL2 :=
  RHTower.l2ReflectionIsometry.comp paleyPositiveDatumIsometry

theorem paleyNegativeDatum_mem_lowerHalfLineL2 (f : HalfLineExponentialL2) :
    paleyNegativeDatumIsometry f ∈ RHTower.lowerHalfLineL2 := by
  rw [RHTower.mem_lowerHalfLineL2_iff]
  change ∀ᵐ x : ℝ, 0 < x →
    ((RHTower.l2Reflection (paleyPositiveDatumIsometry f) : RealLineL2) : ℝ → ℂ) x = 0
  have hp := paleyPositiveDatum_mem_halfLineL2 f
  rw [RHTower.mem_halfLineL2_iff] at hp
  have hp' := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hp
  filter_upwards [RHTower.l2Reflection_ae (paleyPositiveDatumIsometry f), hp'] with
      x href hx hpos
  rw [href]
  exact hx (by linarith)

def lowerHardyPaleyWienerIsometry : HalfLineExponentialL2 →ₗᵢ[ℂ] LowerHardyL2 where
  toFun f := ⟨RHTower.fourierUnitary (paleyPositiveDatumIsometry f), by
    change RHTower.fourierUnitary (paleyPositiveDatumIsometry f) ∈ RHTower.hardyL2ᗮ
    rw [RHTower.hardyL2_orthogonal]
    exact ⟨paleyPositiveDatumIsometry f, paleyPositiveDatum_mem_halfLineL2 f, rfl⟩⟩
  map_add' f g := by
    apply Subtype.ext
    simp
  map_smul' c f := by
    apply Subtype.ext
    simp
  norm_map' f := by
    change ‖RHTower.fourierUnitary (paleyPositiveDatumIsometry f)‖ = ‖f‖
    rw [RHTower.fourierUnitary.norm_map, paleyPositiveDatumIsometry.norm_map]

def upperHardyPaleyWienerIsometry : HalfLineExponentialL2 →ₗᵢ[ℂ] UpperHardyL2 where
  toFun f := ⟨RHTower.fourierUnitary (paleyNegativeDatumIsometry f), by
    exact ⟨paleyNegativeDatumIsometry f, paleyNegativeDatum_mem_lowerHalfLineL2 f, rfl⟩⟩
  map_add' f g := by
    apply Subtype.ext
    simp
  map_smul' c f := by
    apply Subtype.ext
    simp
  norm_map' f := by
    change ‖RHTower.fourierUnitary (paleyNegativeDatumIsometry f)‖ = ‖f‖
    rw [RHTower.fourierUnitary.norm_map, paleyNegativeDatumIsometry.norm_map]

theorem dilation_mem_halfLineL2 {q : ℝ} (hq : 0 < q) {f : RealLineL2}
    (hf : f ∈ RHTower.halfLineL2) :
    RHTower.dilation q hq f ∈ RHTower.halfLineL2 := by
  rw [RHTower.mem_halfLineL2_iff] at hf ⊢
  have hf' := (RHTower.realMul_quasiMeasurePreserving q hq.ne').ae hf
  filter_upwards [RHTower.dilation_ae q hq f, hf'] with x hd hzero hx
  rw [hd, hzero (mul_neg_of_pos_of_neg hq hx)]
  simp

theorem suzukiPositiveZeroExtension_soninHalfLine_eq_of_mem_halfLineL2
    {f : RealLineL2} (hf : f ∈ RHTower.halfLineL2) :
    RHTower.suzukiPositiveZeroExtension (RHTower.soninHalfLine f) = f := by
  apply Lp.ext
  rw [RHTower.mem_halfLineL2_iff] at hf
  have hrestrict := (ae_restrict_iff' measurableSet_Ioi).mp
    (RHTower.coeFn_soninHalfLine f)
  filter_upwards [RHTower.suzukiPositiveZeroExtension_ae (RHTower.soninHalfLine f),
    hrestrict, hf, volume.ae_ne (0 : ℝ)] with x hext hrestrict hzero hx0
  rw [hext, RHTower.suzukiPositiveZeroExtensionFun]
  by_cases hx : 0 < x
  · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) by exact hx)]
    exact hrestrict hx
  · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
    rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) by simpa using hx), hzero hxneg]

theorem paleyPositiveDatumIsometry_surjective_halfLine
    (g : RHTower.halfLineL2) :
    ∃ f : HalfLineExponentialL2,
      paleyPositiveDatumIsometry f = (g : RealLineL2) := by
  let z : RealLineL2 := RHTower.dilation paleyWienerScale⁻¹
    (inv_pos.mpr paleyWienerScale_pos) (g : RealLineL2)
  have hz : z ∈ RHTower.halfLineL2 :=
    dilation_mem_halfLineL2 (inv_pos.mpr paleyWienerScale_pos) g.property
  let f : HalfLineExponentialL2 := RHTower.soninHalfLine z
  refine ⟨f, ?_⟩
  change RHTower.dilation paleyWienerScale paleyWienerScale_pos
      (RHTower.suzukiPositiveZeroExtension f) = (g : RealLineL2)
  have hext : RHTower.suzukiPositiveZeroExtension f = z := by
    exact suzukiPositiveZeroExtension_soninHalfLine_eq_of_mem_halfLineL2 hz
  rw [hext]
  exact RHTower.dilation_dilation_inv paleyWienerScale paleyWienerScale_pos g

theorem lowerHardyPaleyWienerIsometry_surjective :
    Function.Surjective lowerHardyPaleyWienerIsometry := by
  intro g
  have hg : (g : RealLineL2) ∈ RHTower.hardyL2ᗮ := g.property
  rw [RHTower.hardyL2_orthogonal] at hg
  rcases hg with ⟨d, hd, hfourier⟩
  rcases paleyPositiveDatumIsometry_surjective_halfLine ⟨d, hd⟩ with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  apply Subtype.ext
  change RHTower.fourierUnitary (paleyPositiveDatumIsometry f) = (g : RealLineL2)
  rw [hf]
  exact hfourier

def lowerHardyPaleyWienerUnitary : HalfLineExponentialL2 ≃ₗᵢ[ℂ] LowerHardyL2 :=
  LinearIsometryEquiv.ofSurjective lowerHardyPaleyWienerIsometry
    lowerHardyPaleyWienerIsometry_surjective

theorem l2Reflection_mem_halfLineL2_of_mem_lowerHalfLineL2 {f : RealLineL2}
    (hf : f ∈ RHTower.lowerHalfLineL2) :
    RHTower.l2Reflection f ∈ RHTower.halfLineL2 := by
  rw [RHTower.mem_lowerHalfLineL2_iff] at hf
  rw [RHTower.mem_halfLineL2_iff]
  have hf' := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hf
  filter_upwards [RHTower.l2Reflection_ae f, hf'] with x href hzero hx
  rw [href]
  exact hzero (by linarith)

theorem upperHardyPaleyWienerIsometry_surjective :
    Function.Surjective upperHardyPaleyWienerIsometry := by
  intro g
  rcases g.property with ⟨d, hd, hfourier⟩
  let p : RealLineL2 := RHTower.l2Reflection d
  have hp : p ∈ RHTower.halfLineL2 :=
    l2Reflection_mem_halfLineL2_of_mem_lowerHalfLineL2 hd
  rcases paleyPositiveDatumIsometry_surjective_halfLine ⟨p, hp⟩ with ⟨f, hf⟩
  have hnegative : paleyNegativeDatumIsometry f = d := by
    change RHTower.l2Reflection (paleyPositiveDatumIsometry f) = d
    rw [hf]
    exact RHTower.l2Reflection_involutive d
  refine ⟨f, ?_⟩
  apply Subtype.ext
  change RHTower.fourierUnitary (paleyNegativeDatumIsometry f) = (g : RealLineL2)
  rw [hnegative]
  exact hfourier

def upperHardyPaleyWienerUnitary : HalfLineExponentialL2 ≃ₗᵢ[ℂ] UpperHardyL2 :=
  LinearIsometryEquiv.ofSurjective upperHardyPaleyWienerIsometry
    upperHardyPaleyWienerIsometry_surjective

def paleyWienerSqrtScale : ℝ := Real.sqrt paleyWienerScale

theorem paleyWienerSqrtScale_pos : 0 < paleyWienerSqrtScale := by
  unfold paleyWienerSqrtScale
  exact Real.sqrt_pos.mpr paleyWienerScale_pos

theorem paleyWienerSqrtScale_sq : paleyWienerSqrtScale ^ (2 : ℕ) = paleyWienerScale := by
  unfold paleyWienerSqrtScale
  exact Real.sq_sqrt paleyWienerScale_pos.le

theorem paleyPositiveDatum_expFeature {a : ℝ} (ha : 0 < a) :
    paleyPositiveDatumIsometry (expFeature a ha) =
      ((-I) / (paleyWienerSqrtScale : ℂ)) •
        (RHTower.memLp_cauchyDatumUpper
          (show 0 < ((a : ℂ) * I).im by simpa using ha)).toLp
            (RHTower.cauchyDatumUpper ((a : ℂ) * I)) := by
  apply Lp.ext
  let v : ℂ := (a : ℂ) * I
  have hv : 0 < v.im := by simp [v, ha]
  have hfeatureRestrict :
      (expFeature a ha : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun x => Complex.exp (-(a : ℂ) * (x : ℂ)) := by
    have hraw := (halfLineLaplaceFeatureRaw_memLp
      (w := (a : ℂ)) (by simpa using ha)).coeFn_toLp
    have hraw' : (expFeature a ha : ℝ → ℂ) =ᵐ[halfLineLaplaceMeasure]
        halfLineLaplaceFeatureRaw (a : ℂ) := by
      simpa only [expFeature, halfLineLaplaceFeature] using hraw
    have hraw'' : (expFeature a ha : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        halfLineLaplaceFeatureRaw (a : ℂ) := by
      simpa only [halfLineLaplaceMeasure] using hraw'
    filter_upwards [hraw''] with x hx
    rw [hx]
    unfold halfLineLaplaceFeatureRaw
    congr 1
    simp
  have hfeature : ∀ᵐ x ∂volume, x ∈ Ioi (0 : ℝ) →
      (expFeature a ha : ℝ → ℂ) x = Complex.exp (-(a : ℂ) * (x : ℂ)) := by
    exact (ae_restrict_iff' measurableSet_Ioi).mp hfeatureRestrict
  have hz := (RHTower.suzukiPositiveZeroExtension_ae (expFeature a ha)).comp_tendsto
    (RHTower.realMul_quasiMeasurePreserving paleyWienerScale
      paleyWienerScale_pos.ne').tendsto_ae
  have hf := (RHTower.realMul_quasiMeasurePreserving paleyWienerScale
    paleyWienerScale_pos.ne').ae hfeature
  have hd := RHTower.dilation_ae paleyWienerScale paleyWienerScale_pos
    (RHTower.suzukiPositiveZeroExtension (expFeature a ha))
  have hc := (RHTower.memLp_cauchyDatumUpper hv).coeFn_toLp
  have hs := Lp.coeFn_smul ((-I) / (paleyWienerSqrtScale : ℂ))
    ((RHTower.memLp_cauchyDatumUpper hv).toLp (RHTower.cauchyDatumUpper v))
  filter_upwards [hz, hf, hd, hc, hs] with x hz hf hd hc hs
  change ((((RHTower.dilation paleyWienerScale paleyWienerScale_pos)
    (RHTower.suzukiPositiveZeroExtension (expFeature a ha)) : RealLineL2) : ℝ → ℂ) x) = _
  rw [hd, hs, Pi.smul_apply, smul_eq_mul, hc]
  by_cases hx : 0 < x
  · have hqx : paleyWienerScale * x ∈ Ioi (0 : ℝ) := by
      exact mul_pos paleyWienerScale_pos hx
    have hz' : RHTower.suzukiPositiveZeroExtension (expFeature a ha)
        (paleyWienerScale * x) =
        RHTower.suzukiPositiveZeroExtensionFun (expFeature a ha)
          (paleyWienerScale * x) := by
      simpa only [Function.comp_apply] using hz
    have hf' : (expFeature a ha : ℝ → ℂ) (paleyWienerScale * x) =
        Complex.exp (-(a : ℂ) * ((paleyWienerScale * x : ℝ) : ℂ)) := by
      exact hf hqx
    rw [hz', RHTower.suzukiPositiveZeroExtensionFun, indicator_of_mem hqx]
    have hdatum : RHTower.cauchyDatumUpper v x =
        (2 * (Real.pi : ℂ) * I) *
          Complex.exp (2 * (Real.pi : ℂ) * I * v * (x : ℂ)) := by
      rw [RHTower.cauchyDatumUpper,
        indicator_of_mem (show x ∈ Ioi (0 : ℝ) by exact hx)]
    rw [hdatum]
    have hsqC : (paleyWienerSqrtScale : ℂ) ^ (2 : ℕ) = paleyWienerScale := by
      exact_mod_cast paleyWienerSqrtScale_sq
    have hsne : (paleyWienerSqrtScale : ℂ) ≠ 0 := by
      exact_mod_cast paleyWienerSqrtScale_pos.ne'
    have hexp :
        Complex.exp (-(a : ℂ) * ((paleyWienerScale * x : ℝ) : ℂ)) =
          Complex.exp (2 * (Real.pi : ℂ) * I * v * (x : ℂ)) := by
      congr 1
      simp only [paleyWienerScale, v]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    calc
      (Real.sqrt paleyWienerScale : ℂ) *
          (expFeature a ha : ℝ → ℂ) (paleyWienerScale * x) =
          (Real.sqrt paleyWienerScale : ℂ) *
            Complex.exp (-(a : ℂ) * ((paleyWienerScale * x : ℝ) : ℂ)) := by
              exact congrArg (fun z : ℂ => (Real.sqrt paleyWienerScale : ℂ) * z) hf'
      _ = (Real.sqrt paleyWienerScale : ℂ) *
            Complex.exp (2 * (Real.pi : ℂ) * I * v * (x : ℂ)) := by rw [hexp]
      _ = (-I / (paleyWienerSqrtScale : ℂ)) *
            (2 * (Real.pi : ℂ) * I *
              Complex.exp (2 * (Real.pi : ℂ) * I * v * (x : ℂ))) := by
            change (paleyWienerSqrtScale : ℂ) * _ = _
            field_simp
            rw [hsqC]
            simp only [paleyWienerScale]
            rw [Complex.I_sq]
            push_cast
            ring
  · have hxnot : x ∉ Ioi (0 : ℝ) := by simpa using hx
    have hqxnot : paleyWienerScale * x ∉ Ioi (0 : ℝ) := by
      simp only [mem_Ioi, not_lt]
      exact mul_nonpos_of_nonneg_of_nonpos paleyWienerScale_pos.le (le_of_not_gt hx)
    have hz' : RHTower.suzukiPositiveZeroExtension (expFeature a ha)
        (paleyWienerScale * x) =
        RHTower.suzukiPositiveZeroExtensionFun (expFeature a ha)
          (paleyWienerScale * x) := by
      simpa only [Function.comp_apply] using hz
    rw [hz', RHTower.suzukiPositiveZeroExtensionFun, indicator_of_notMem hqxnot,
      RHTower.cauchyDatumUpper, indicator_of_notMem hxnot]
    simp

theorem l2Reflection_cauchyDatumUpper_eq_neg_cauchyDatum {a : ℝ} (ha : 0 < a) :
    RHTower.l2Reflection
        ((RHTower.memLp_cauchyDatumUpper
          (show 0 < ((a : ℂ) * I).im by simpa using ha)).toLp
            (RHTower.cauchyDatumUpper ((a : ℂ) * I))) =
      -((RHTower.memLp_cauchyDatum
          (show (-(a : ℂ) * I).im < 0 by simpa using ha)).toLp
            (RHTower.cauchyDatum (-(a : ℂ) * I))) := by
  apply Lp.ext
  let v : ℂ := (a : ℂ) * I
  let w : ℂ := -(a : ℂ) * I
  have hv : 0 < v.im := by simp [v, ha]
  have hw : w.im < 0 := by simp [w, ha]
  have href := RHTower.l2Reflection_ae
    ((RHTower.memLp_cauchyDatumUpper hv).toLp (RHTower.cauchyDatumUpper v))
  have hu := (RHTower.memLp_cauchyDatumUpper hv).coeFn_toLp
  have huNeg := hu.comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  have hl := (RHTower.memLp_cauchyDatum hw).coeFn_toLp
  have hneg := Lp.coeFn_neg
    ((RHTower.memLp_cauchyDatum hw).toLp (RHTower.cauchyDatum w))
  filter_upwards [href, huNeg, hl, hneg] with x href hu hl hneg
  rw [href, hneg, Pi.neg_apply, hl]
  have hu' :
      ((RHTower.memLp_cauchyDatumUpper hv).toLp
        (RHTower.cauchyDatumUpper v) : ℝ → ℂ) (-x) =
          RHTower.cauchyDatumUpper v (-x) := by
    simpa only [Function.comp_apply] using hu
  rw [hu']
  by_cases hx : x < 0
  · have hnx : -x ∈ Ioi (0 : ℝ) := by simpa using neg_pos.mpr hx
    have hxmem : x ∈ Iio (0 : ℝ) := hx
    rw [RHTower.cauchyDatumUpper, indicator_of_mem hnx,
      RHTower.cauchyDatum, indicator_of_mem hxmem]
    simp only [neg_mul, neg_neg]
    congr 1
    apply congrArg Complex.exp
    simp only [v, w]
    push_cast
    ring_nf
  · have hxnonneg : 0 ≤ x := le_of_not_gt hx
    have hnx : -x ∉ Ioi (0 : ℝ) := by simpa using neg_nonpos.mpr hxnonneg
    have hxnot : x ∉ Iio (0 : ℝ) := by simpa using hx
    rw [RHTower.cauchyDatumUpper, indicator_of_notMem hnx,
      RHTower.cauchyDatum, indicator_of_notMem hxnot]
    simp

theorem paleyNegativeDatum_expFeature {a : ℝ} (ha : 0 < a) :
    paleyNegativeDatumIsometry (expFeature a ha) =
      (I / (paleyWienerSqrtScale : ℂ)) •
        (RHTower.memLp_cauchyDatum
          (show (-(a : ℂ) * I).im < 0 by simpa using ha)).toLp
            (RHTower.cauchyDatum (-(a : ℂ) * I)) := by
  change RHTower.l2Reflection (paleyPositiveDatumIsometry (expFeature a ha)) = _
  rw [paleyPositiveDatum_expFeature ha, map_smul,
    l2Reflection_cauchyDatumUpper_eq_neg_cauchyDatum ha]
  module

theorem lowerHardyPaleyWiener_expFeature {a : ℝ} (ha : 0 < a) :
    lowerHardyPaleyWienerIsometry (expFeature a ha) =
      ((-I) / (paleyWienerSqrtScale : ℂ)) • upperCauchyFeature a ha := by
  have hF : RHTower.fourierUnitary
        ((RHTower.memLp_cauchyDatumUpper
          (show 0 < ((a : ℂ) * I).im by simpa using ha)).toLp
            (RHTower.cauchyDatumUpper ((a : ℂ) * I))) =
      ((upperCauchyFeature a ha : LowerHardyL2) : RealLineL2) := by
    change (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
        ((RHTower.memLp_cauchyDatumUpper
          (show 0 < ((a : ℂ) * I).im by simpa using ha)).toLp
            (RHTower.cauchyDatumUpper ((a : ℂ) * I))) =
      (RHTower.memLp_cauchyKernel
        (show ((a : ℂ) * I).im ≠ 0 by simpa using ha.ne')).toLp
          (fun x : ℝ => (((x : ℝ) : ℂ) - (a : ℂ) * I)⁻¹)
    exact RHTower.fourierTransform_cauchyDatumUpper
      (v := (a : ℂ) * I) (by simpa using ha)
  apply Subtype.ext
  change RHTower.fourierUnitary (paleyPositiveDatumIsometry (expFeature a ha)) = _
  rw [paleyPositiveDatum_expFeature ha, map_smul, hF]
  rfl

theorem upperHardyPaleyWiener_expFeature {a : ℝ} (ha : 0 < a) :
    upperHardyPaleyWienerIsometry (expFeature a ha) =
      (I / (paleyWienerSqrtScale : ℂ)) • lowerCauchyFeature a ha := by
  have hF : RHTower.fourierUnitary
        ((RHTower.memLp_cauchyDatum
          (show (-(a : ℂ) * I).im < 0 by simpa using ha)).toLp
            (RHTower.cauchyDatum (-(a : ℂ) * I))) =
      ((lowerCauchyFeature a ha : UpperHardyL2) : RealLineL2) := by
    change (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ)
        ((RHTower.memLp_cauchyDatum
          (show (-(a : ℂ) * I).im < 0 by simpa using ha)).toLp
            (RHTower.cauchyDatum (-(a : ℂ) * I))) =
      (RHTower.memLp_cauchyKernel
        (show (-(a : ℂ) * I).im ≠ 0 by simpa using ha.ne')).toLp
          (fun x : ℝ => (((x : ℝ) : ℂ) - (-(a : ℂ) * I))⁻¹)
    exact RHTower.fourierTransform_cauchyDatum
      (w := -(a : ℂ) * I) (by simpa using ha)
  apply Subtype.ext
  change RHTower.fourierUnitary (paleyNegativeDatumIsometry (expFeature a ha)) = _
  rw [paleyNegativeDatum_expFeature ha, map_smul, hF]
  rfl

theorem upperCauchyFeature_eq_paleyWiener {a : ℝ} (ha : 0 < a) :
    upperCauchyFeature a ha =
      (I * (paleyWienerSqrtScale : ℂ)) •
        lowerHardyPaleyWienerIsometry (expFeature a ha) := by
  rw [lowerHardyPaleyWiener_expFeature ha, smul_smul]
  have hsne : (paleyWienerSqrtScale : ℂ) ≠ 0 := by
    exact_mod_cast paleyWienerSqrtScale_pos.ne'
  field_simp
  rw [Complex.I_sq]
  ring_nf
  simp

theorem lowerCauchyFeature_eq_paleyWiener {a : ℝ} (ha : 0 < a) :
    lowerCauchyFeature a ha =
      (-I * (paleyWienerSqrtScale : ℂ)) •
        upperHardyPaleyWienerIsometry (expFeature a ha) := by
  rw [upperHardyPaleyWiener_expFeature ha, smul_smul]
  have hsne : (paleyWienerSqrtScale : ℂ) ≠ 0 := by
    exact_mod_cast paleyWienerSqrtScale_pos.ne'
  field_simp
  rw [Complex.I_sq]
  ring_nf
  simp

theorem paleyWiener_rankOne_intertwining {a : ℝ} (ha : 0 < a)
    (f : HalfLineExponentialL2) :
    (((-(Real.pi : ℂ)⁻¹) •
        InnerProductSpace.rankOne ℂ (upperCauchyFeature a ha)
          (lowerCauchyFeature a ha))
        (upperHardyPaleyWienerIsometry f)) =
      lowerHardyPaleyWienerIsometry
        (((2 : ℂ) • InnerProductSpace.rankOne ℂ (expFeature a ha)
          (expFeature a ha)) f) := by
  rw [smul_apply, InnerProductSpace.rankOne_apply,
    lowerCauchyFeature_eq_paleyWiener ha,
    upperCauchyFeature_eq_paleyWiener ha]
  rw [inner_smul_left
    (upperHardyPaleyWienerIsometry (expFeature a ha))
    (upperHardyPaleyWienerIsometry f)
    (-I * (paleyWienerSqrtScale : ℂ)),
    upperHardyPaleyWienerIsometry.inner_map_map]
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal,
    neg_neg, smul_smul]
  rw [smul_apply, InnerProductSpace.rankOne_apply, map_smul]
  simp only [map_smul, smul_smul]
  have hsqC : (paleyWienerSqrtScale : ℂ) ^ (2 : ℕ) = paleyWienerScale := by
    exact_mod_cast paleyWienerSqrtScale_sq
  congr 1
  ring_nf
  rw [Complex.I_sq]
  rw [hsqC]
  simp only [paleyWienerScale]
  field_simp
  push_cast
  ring

end GaloisForLFunctions.HTGeometry
