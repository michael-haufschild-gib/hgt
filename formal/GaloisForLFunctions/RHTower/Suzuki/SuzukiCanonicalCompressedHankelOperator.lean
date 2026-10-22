import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalCompressedHankel
import GaloisForLFunctions.RHTower.SoninDilationContinuity
import GaloisForLFunctions.RHTower.SoninTimeBandHilbertSchmidt

/-!
# Suzuki's compressed canonical Hankel operator

This module constructs the literal integral operator from Suzuki's Lemma 4.2:

`(H_{ω,a} f)(x) = ∫₀ᵃ h_ω(xy) f(y) dy`.

For every `ω > 1/2`, it proves unconditionally that the operator is Hilbert–Schmidt and
self-adjoint.  The construction uses the local `L²` theorem for the arithmetic kernel rather
than replacing the kernel by an abstract representative.  For `a ≤ 1`, the source kernel
vanishes throughout the square and the operator is definitionally selected to be zero.
-/

open ArithmeticFunction Complex MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

theorem memLp_suzukiCompressedHankelBase (omega a : ℝ) (homega : 1 / 2 < omega) (ha : 1 < a) :
    MemLp ((Ioc 1 (a ^ 2)).indicator (suzukiSourceHFinite omega)) 2 volume := by
  rw [memLp_indicator_iff_restrict measurableSet_Ioc]
  exact memLp_suzukiSourceHFinite_local_two homega (by nlinarith)

def suzukiCompressedHankelBase (omega a : ℝ) (homega : 1 / 2 < omega) (ha : 1 < a) : RealL2 :=
  (memLp_suzukiCompressedHankelBase omega a homega ha).toLp
    ((Ioc 1 (a ^ 2)).indicator (suzukiSourceHFinite omega))

theorem suzukiCompressedHankelBase_ae (omega a : ℝ) (homega : 1 / 2 < omega) (ha : 1 < a) :
    (suzukiCompressedHankelBase omega a homega ha : ℝ → ℂ) =ᵐ[volume]
      (Ioc 1 (a ^ 2)).indicator (suzukiSourceHFinite omega) := by
  exact MemLp.coeFn_toLp (memLp_suzukiCompressedHankelBase omega a homega ha)

def suzukiCompressedHankelRow (omega a : ℝ) (homega : 1 / 2 < omega) (ha : 1 < a) (x : ℝ) :
    IntervalL2 0 a :=
  if 0 < x then
    (((Real.sqrt x)⁻¹ : ℝ) : ℂ) •
      restrictToClosedInterval 0 a (rayDilate x (suzukiCompressedHankelBase omega a homega ha))
  else 0

theorem suzukiCompressedHankelRow_eq_zero {omega a x : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) (hx0 : 0 < x) (hxa : x * a ≤ 1) :
    suzukiCompressedHankelRow omega a homega ha x = 0 := by
  rw [suzukiCompressedHankelRow, if_pos hx0]
  apply Lp.ext
  have hmp := measurePreserving_subtype_coe
    (μa := (volume : Measure ℝ)) (s := Icc 0 a) measurableSet_Icc
  have hbaseVol := (suzukiCompressedHankelBase_ae omega a homega ha).comp_tendsto
    (realMul_quasiMeasurePreserving x hx0.ne').tendsto_ae
  have hbase := hmp.quasiMeasurePreserving.ae (ae_restrict_of_ae hbaseVol)
  filter_upwards [Lp.coeFn_smul
      ((((Real.sqrt x)⁻¹ : ℝ) : ℂ))
      (restrictToClosedInterval 0 a (rayDilate x (suzukiCompressedHankelBase omega a homega ha))),
    restrictToClosedInterval_coeFn 0 a (rayDilate x (suzukiCompressedHankelBase omega a homega ha)),
    hmp.quasiMeasurePreserving.ae (ae_restrict_of_ae
      (rayDilate_ae hx0 (suzukiCompressedHankelBase omega a homega ha))), hbase,
    Lp.coeFn_zero ℂ 2 (volume : Measure (ClosedInterval 0 a))] with
      y hsmul hres hdil hbase hzero
  rw [hsmul, Pi.smul_apply, hres, hdil]
  have hbase' : (suzukiCompressedHankelBase omega a homega ha : ℝ → ℂ) (x * (y : ℝ)) =
      (Ioc 1 (a ^ 2)).indicator (suzukiSourceHFinite omega) (x * (y : ℝ)) := by
    simpa only [Function.comp_apply] using hbase
  rw [hbase']
  have hxy : x * (y : ℝ) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left y.property.2 hx0.le) hxa
  rw [Set.indicator_of_notMem]
  · simp only [smul_eq_mul, mul_zero, hzero, Pi.zero_apply]
  · exact fun h => (not_lt_of_ge hxy) h.1

theorem suzukiCompressedHankelRow_ae {omega a x : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) (hx0 : 0 < x) (hxa : x ≤ a) :
    (suzukiCompressedHankelRow omega a homega ha x : ClosedInterval 0 a → ℂ) =ᵐ[volume]
      fun y => suzukiSourceHFinite omega (x * (y : ℝ)) := by
  rw [suzukiCompressedHankelRow, if_pos hx0]
  have hmp := measurePreserving_subtype_coe
    (μa := (volume : Measure ℝ)) (s := Icc 0 a) measurableSet_Icc
  have hbaseVol := (suzukiCompressedHankelBase_ae omega a homega ha).comp_tendsto
    (realMul_quasiMeasurePreserving x hx0.ne').tendsto_ae
  have hbase := hmp.quasiMeasurePreserving.ae (ae_restrict_of_ae hbaseVol)
  filter_upwards [Lp.coeFn_smul
      ((((Real.sqrt x)⁻¹ : ℝ) : ℂ))
      (restrictToClosedInterval 0 a (rayDilate x (suzukiCompressedHankelBase omega a homega ha))),
    restrictToClosedInterval_coeFn 0 a (rayDilate x (suzukiCompressedHankelBase omega a homega ha)),
    hmp.quasiMeasurePreserving.ae (ae_restrict_of_ae
      (rayDilate_ae hx0 (suzukiCompressedHankelBase omega a homega ha))), hbase] with y hsmul hres hdil hbase
  rw [hsmul, Pi.smul_apply, hres, hdil]
  have hbase' : (suzukiCompressedHankelBase omega a homega ha : ℝ → ℂ) (x * (y : ℝ)) =
      (Ioc 1 (a ^ 2)).indicator (suzukiSourceHFinite omega) (x * (y : ℝ)) := by
    simpa only [Function.comp_apply] using hbase
  rw [hbase']
  have hsqrt : (((Real.sqrt x)⁻¹ : ℝ) : ℂ) * (Real.sqrt x : ℂ) = 1 := by
    norm_cast
    exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hx0)
  change (((Real.sqrt x)⁻¹ : ℝ) : ℂ) *
      ((Real.sqrt x : ℂ) *
        (Ioc 1 (a ^ 2)).indicator (suzukiSourceHFinite omega) (x * (y : ℝ))) = _
  rw [← mul_assoc, hsqrt, one_mul]
  by_cases hxy : x * (y : ℝ) ∈ Ioc 1 (a ^ 2)
  · rw [Set.indicator_of_mem hxy]
  · rw [Set.indicator_of_notMem hxy]
    rw [suzukiSourceHFinite, if_neg]
    intro hnot
    apply hxy
    have hupper : x * (y : ℝ) ≤ a ^ 2 := by
      have := mul_le_mul hxa y.property.2 y.property.1 (le_trans zero_le_one ha.le)
      nlinarith
    exact ⟨hnot, hupper⟩

theorem continuousOn_suzukiCompressedHankelRow {omega a : ℝ}
    (homega : 1 / 2 < omega) (ha : 1 < a) :
    ContinuousOn (suzukiCompressedHankelRow omega a homega ha) (Icc 0 a) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hx0
  · have hainv : 0 < 1 / a := one_div_pos.mpr (lt_trans zero_lt_one ha)
    have hev : suzukiCompressedHankelRow omega a homega ha =ᶠ[𝓝[Icc 0 a] 0]
        fun _ => 0 := by
      have hIio : ∀ᶠ z in 𝓝[Icc 0 a] 0, z ∈ Iio (1 / a) :=
        Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hainv)
      filter_upwards [hIio, self_mem_nhdsWithin] with z hz hzIcc
      by_cases hz0 : 0 < z
      · exact suzukiCompressedHankelRow_eq_zero homega ha hz0
          ((lt_div_iff₀ (lt_trans zero_lt_one ha)).mp hz).le
      · rw [suzukiCompressedHankelRow, if_neg hz0]
    exact continuousWithinAt_const.congr_of_eventuallyEq hev (by
      rw [suzukiCompressedHankelRow, if_neg (lt_irrefl 0)])
  · let posRow : ℝ → IntervalL2 0 a := fun z =>
      ((((Real.sqrt z)⁻¹ : ℝ) : ℂ)) •
        restrictToClosedInterval 0 a (rayDilate z (suzukiCompressedHankelBase omega a homega ha))
    have hscalar : ContinuousAt (fun z : ℝ => ((((Real.sqrt z)⁻¹ : ℝ) : ℂ))) x := by
      exact Complex.continuous_ofReal.continuousAt.comp
        (Real.continuous_sqrt.continuousAt.inv₀ (Real.sqrt_ne_zero'.mpr hx0))
    have hdil : ContinuousAt
      (fun z : ℝ => rayDilate z (suzukiCompressedHankelBase omega a homega ha)) x :=
      (continuousOn_rayDilate (suzukiCompressedHankelBase omega a homega ha)).continuousAt
        (Ioi_mem_nhds hx0)
    have hpos : ContinuousAt posRow x :=
      hscalar.smul ((restrictToClosedInterval 0 a).continuous.continuousAt.comp hdil)
    have hev : suzukiCompressedHankelRow omega a homega ha =ᶠ[𝓝 x] posRow := by
      filter_upwards [Ioi_mem_nhds hx0] with z hz
      have hz0 : 0 < z := hz
      change (if 0 < z then
          (((Real.sqrt z)⁻¹ : ℝ) : ℂ) •
            restrictToClosedInterval 0 a (rayDilate z (suzukiCompressedHankelBase omega a homega ha))
        else 0) = posRow z
      rw [if_pos hz0]
    exact (hpos.congr_of_eventuallyEq hev).continuousWithinAt

def suzukiCompressedHankelRowContinuous (omega a : ℝ) (homega : 1 / 2 < omega) (ha : 1 < a) :
    C(ClosedInterval 0 a, IntervalL2 0 a) where
  toFun x := suzukiCompressedHankelRow omega a homega ha x
  continuous_toFun := continuousOn_iff_continuous_restrict.mp
    (continuousOn_suzukiCompressedHankelRow homega ha)

theorem suzukiCompressedHankelRowContinuous_ae (omega a : ℝ) (homega : 1 / 2 < omega) (ha : 1 < a)
    (x : ClosedInterval 0 a) :
    (suzukiCompressedHankelRowContinuous omega a homega ha x : ClosedInterval 0 a → ℂ) =ᵐ[volume]
      fun y => suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) := by
  rcases eq_or_lt_of_le x.property.1 with hxzero | hxpos
  · have hzeroMem : (0 : ℝ) ∈ Icc 0 a :=
      ⟨le_rfl, le_trans zero_le_one ha.le⟩
    have hx : x = (⟨0, hzeroMem⟩ : ClosedInterval 0 a) :=
      Subtype.ext hxzero.symm
    subst x
    have hzero : suzukiCompressedHankelRow omega a homega ha 0 = 0 := by
      rw [suzukiCompressedHankelRow, if_neg (lt_irrefl 0)]
    change (suzukiCompressedHankelRow omega a homega ha 0 : ClosedInterval 0 a → ℂ) =ᵐ[volume]
      fun y => suzukiSourceHFinite omega (0 * (y : ℝ))
    rw [hzero]
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure (ClosedInterval 0 a))] with y hy
    rw [hy]
    simp [suzukiSourceHFinite]
  · exact suzukiCompressedHankelRow_ae homega ha hxpos x.property.2

def suzukiCompressedHankelFunctionalContinuous (omega a : ℝ)
    (homega : 1 / 2 < omega) (ha : 1 < a) :
    C(ClosedInterval 0 a, IntervalL2 0 a →L[ℂ] ℂ) where
  toFun x := (complexMulBilinear.lpPairing volume 2 2)
    (suzukiCompressedHankelRowContinuous omega a homega ha x)
  continuous_toFun :=
    (complexMulBilinear.lpPairing volume 2 2).continuous.comp
      (suzukiCompressedHankelRowContinuous omega a homega ha).continuous

def suzukiCompressedHankelFunctionalField (omega a : ℝ)
    (homega : 1 / 2 < omega) (ha : 1 < a) :
    Lp (IntervalL2 0 a →L[ℂ] ℂ) 2 (volume : Measure (ClosedInterval 0 a)) :=
  ContinuousMap.toLp 2 volume ℂ (suzukiCompressedHankelFunctionalContinuous omega a homega ha)

def suzukiCompressedHankelOperatorAboveOne (omega a : ℝ)
    (homega : 1 / 2 < omega) (ha : 1 < a) :
    IntervalL2 0 a →L[ℂ] IntervalL2 0 a :=
  kernelOperator (volume : Measure (ClosedInterval 0 a))
    (suzukiCompressedHankelFunctionalField omega a homega ha)

theorem suzukiCompressedHankelOperatorAboveOne_coeFn (omega a : ℝ)
    (homega : 1 / 2 < omega) (ha : 1 < a) (f : IntervalL2 0 a) :
    (suzukiCompressedHankelOperatorAboveOne omega a homega ha f : ClosedInterval 0 a → ℂ) =ᵐ[volume]
      fun x => ∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * f y ∂volume := by
  filter_upwards [
    (evalBilinear (𝕜 := ℂ) (E := IntervalL2 0 a)).coeFn_holder
      (r := (2 : ENNReal)) (suzukiCompressedHankelFunctionalField omega a homega ha)
      (Lp.const ∞ (volume : Measure (ClosedInterval 0 a)) f),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure (ClosedInterval 0 a)))
      (suzukiCompressedHankelFunctionalContinuous omega a homega ha),
    Lp.coeFn_const (p := ∞) (volume : Measure (ClosedInterval 0 a)) f
  ] with x hholder hfield hconst
  rw [suzukiCompressedHankelOperatorAboveOne, kernelOperator, kernelOperatorMap_apply,
    hholder, suzukiCompressedHankelFunctionalField, hfield, hconst]
  change (complexMulBilinear.lpPairing volume 2 2
    (suzukiCompressedHankelRowContinuous omega a homega ha x)) f = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [suzukiCompressedHankelRowContinuous_ae omega a homega ha x] with y hy
  rw [hy]
  simp [complexMulBilinear]

theorem suzukiCompressedHankelOperatorAboveOne_isHilbertSchmidt (omega a : ℝ)
    (homega : 1 / 2 < omega) (ha : 1 < a) :
    (suzukiCompressedHankelOperatorAboveOne omega a homega ha).IsHilbertSchmidt := by
  exact isHilbertSchmidt_kernelOperator
    (volume : Measure (ClosedInterval 0 a))
    (suzukiCompressedHankelFunctionalField omega a homega ha)

theorem memLp_suzukiCompressedHankelKernel_subtype_two (omega a : ℝ)
    (homega : 1 / 2 < omega) (ha : 1 < a) :
    MemLp (fun p : ClosedInterval 0 a × ClosedInterval 0 a =>
      suzukiSourceHFinite omega ((p.1 : ℝ) * (p.2 : ℝ))) 2
      ((volume : Measure (ClosedInterval 0 a)).prod
        (volume : Measure (ClosedInterval 0 a))) := by
  have hK : MemLp (fun p : ℝ × ℝ =>
      suzukiSourceHFinite omega (p.1 * p.2)) 2
      (((volume : Measure ℝ).restrict (Icc 0 a)).prod
        ((volume : Measure ℝ).restrict (Icc 0 a))) := by
    simpa only [restrict_Ioc_eq_restrict_Icc] using
      memLp_suzukiCompressedHankelKernel_two homega ha
  let hmp : MeasurePreserving ((↑) : ClosedInterval 0 a → ℝ)
      (volume : Measure (ClosedInterval 0 a))
      ((volume : Measure ℝ).restrict (Icc 0 a)) :=
    measurePreserving_subtype_coe (μa := (volume : Measure ℝ))
      (s := Icc 0 a) measurableSet_Icc
  have hcomp := hK.comp_measurePreserving (hmp.prod hmp)
  change MemLp (fun p : ClosedInterval 0 a × ClosedInterval 0 a =>
      suzukiSourceHFinite omega ((p.1 : ℝ) * (p.2 : ℝ))) 2
      ((volume : Measure (ClosedInterval 0 a)).prod
        (volume : Measure (ClosedInterval 0 a))) at hcomp
  exact hcomp

theorem memLp_suzukiCompressedHankelConjTensor_two (a : ℝ) (f g : IntervalL2 0 a) :
    MemLp (fun p : ClosedInterval 0 a × ClosedInterval 0 a =>
      (starRingEnd ℂ) (f p.2) * g p.1) 2
      ((volume : Measure (ClosedInterval 0 a)).prod
        (volume : Measure (ClosedInterval 0 a))) := by
  let mu : Measure (ClosedInterval 0 a) := volume
  let Q : ClosedInterval 0 a × ClosedInterval 0 a → ℂ := fun p =>
    (starRingEnd ℂ) (f p.2) * g p.1
  have hQae : AEStronglyMeasurable Q (mu.prod mu) :=
    (Complex.continuous_conj.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable f)).comp_snd.mul
        (Lp.aestronglyMeasurable g).comp_fst
  apply (memLp_two_iff_integrable_sq_norm hQae).2
  have hf2 : Integrable (fun y => ‖f y‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)
  have hg2 : Integrable (fun x => ‖g x‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).1 (Lp.memLp g)
  have hprod := hg2.mul_prod hf2
  refine hprod.congr ?_
  filter_upwards with p
  dsimp only [Q]
  rw [norm_mul, RCLike.norm_conj]
  ring

theorem integrable_suzukiCompressedHankel_innerKernel (omega a : ℝ)
    (homega : 1 / 2 < omega) (ha : 1 < a) (f g : IntervalL2 0 a) :
    Integrable (fun p : ClosedInterval 0 a × ClosedInterval 0 a =>
      (starRingEnd ℂ)
          (suzukiSourceHFinite omega ((p.1 : ℝ) * (p.2 : ℝ)) * f p.2) *
        g p.1)
      ((volume : Measure (ClosedInterval 0 a)).prod
        (volume : Measure (ClosedInterval 0 a))) := by
  let mu : Measure (ClosedInterval 0 a) := volume
  let K : ClosedInterval 0 a × ClosedInterval 0 a → ℂ := fun p =>
    suzukiSourceHFinite omega ((p.1 : ℝ) * (p.2 : ℝ))
  let Q : ClosedInterval 0 a × ClosedInterval 0 a → ℂ := fun p =>
    (starRingEnd ℂ) (f p.2) * g p.1
  have hK : MemLp K 2 (mu.prod mu) := memLp_suzukiCompressedHankelKernel_subtype_two omega a homega ha
  have hQ : MemLp Q 2 (mu.prod mu) := memLp_suzukiCompressedHankelConjTensor_two a f g
  have hKQ : MemLp (Q * K) 1 (mu.prod mu) := hK.mul hQ
  have hInt : Integrable (Q * K) (mu.prod mu) := memLp_one_iff_integrable.mp hKQ
  refine hInt.congr (Filter.Eventually.of_forall fun p => ?_)
  dsimp only [K, Q, Pi.mul_apply]
  rw [map_mul, conj_suzukiSourceHFinite]
  ring

theorem suzukiCompressedHankelOperatorAboveOne_isSelfAdjoint (omega a : ℝ)
    (homega : 1 / 2 < omega) (ha : 1 < a) :
    IsSelfAdjoint (suzukiCompressedHankelOperatorAboveOne omega a homega ha) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  let mu : Measure (ClosedInterval 0 a) := volume
  let K : ClosedInterval 0 a → ClosedInterval 0 a → ℂ := fun x y =>
    suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ))
  let D : ClosedInterval 0 a → ClosedInterval 0 a → ℂ := fun x y =>
    (starRingEnd ℂ) (K x y * f y) * g x
  have hD : Integrable (Function.uncurry D) (mu.prod mu) :=
    integrable_suzukiCompressedHankel_innerKernel omega a homega ha f g
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ x, inner ℂ (suzukiCompressedHankelOperatorAboveOne omega a homega ha f x) (g x) ∂mu) =
        ∫ x, ∫ y, D x y ∂mu ∂mu := by
      apply integral_congr_ae
      filter_upwards [suzukiCompressedHankelOperatorAboveOne_coeFn omega a homega ha f] with x hx
      rw [hx]
      rw [RCLike.inner_apply]
      change g x * (starRingEnd ℂ) (∫ y, K x y * f y ∂mu) = _
      rw [← integral_conj, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      dsimp only [D]
      ring
    _ = ∫ y, ∫ x, D x y ∂mu ∂mu := integral_integral_swap hD
    _ = ∫ y, ∫ x, (K y x * g x) * (starRingEnd ℂ) (f y) ∂mu ∂mu := by
      apply integral_congr_ae
      filter_upwards with y
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [D, K]
      rw [map_mul, conj_suzukiSourceHFinite]
      rw [mul_comm (x : ℝ) (y : ℝ)]
      ring
    _ = ∫ y, inner ℂ (f y) (suzukiCompressedHankelOperatorAboveOne omega a homega ha g y) ∂mu := by
      apply integral_congr_ae
      filter_upwards [suzukiCompressedHankelOperatorAboveOne_coeFn omega a homega ha g] with y hy
      rw [hy]
      rw [RCLike.inner_apply]
      change (∫ x, (K y x * g x) * (starRingEnd ℂ) (f y) ∂mu) =
        (∫ x, K y x * g x ∂mu) * (starRingEnd ℂ) (f y)
      rw [integral_mul_const]

/-- Suzuki's compressed Hankel operator with literal kernel `h_ω(xy)` on `L²(0,a)`.

The piecewise definition merely handles the source's support cutoff: when `a ≤ 1`, the
kernel is zero on the full square. -/
def suzukiCompressedHankelOperator (omega a : ℝ) (homega : 1 / 2 < omega) :
    IntervalL2 0 a →L[ℂ] IntervalL2 0 a :=
  if ha : 1 < a then suzukiCompressedHankelOperatorAboveOne omega a homega ha else 0

/-- Below the support threshold `a = 1`, Suzuki's compressed operator is zero. -/
theorem suzukiCompressedHankelOperator_eq_zero_of_le_one {omega a : ℝ}
    (homega : 1 / 2 < omega) (ha : a ≤ 1) :
    suzukiCompressedHankelOperator omega a homega = 0 := by
  rw [suzukiCompressedHankelOperator, dif_neg (not_lt_of_ge ha)]

/-- Exact almost-everywhere integral formula for Suzuki's compressed operator. -/
theorem suzukiCompressedHankelOperator_coeFn (omega a : ℝ)
    (homega : 1 / 2 < omega) (ha0 : 0 < a) (f : IntervalL2 0 a) :
    (suzukiCompressedHankelOperator omega a homega f : ClosedInterval 0 a → ℂ) =ᵐ[volume]
      fun x => ∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * f y ∂volume := by
  by_cases ha : 1 < a
  · rw [suzukiCompressedHankelOperator, dif_pos ha]
    exact suzukiCompressedHankelOperatorAboveOne_coeFn omega a homega ha f
  · have ha1 : a ≤ 1 := le_of_not_gt ha
    rw [suzukiCompressedHankelOperator, dif_neg ha]
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure (ClosedInterval 0 a))] with x hx
    simp only [_root_.zero_apply]
    rw [hx]
    have hkernel : (fun y : ClosedInterval 0 a =>
        suzukiSourceHFinite omega ((x : ℝ) * (y : ℝ)) * f y) = 0 := by
      funext y
      rw [suzukiSourceHFinite, if_neg]
      · simp
      · apply not_lt_of_ge
        have hxy : (x : ℝ) * (y : ℝ) ≤ a ^ 2 := by
          have := mul_le_mul x.property.2 y.property.2 y.property.1 ha0.le
          nlinarith
        nlinarith
    rw [hkernel]
    change (0 : ℂ) = ∫ _y : ClosedInterval 0 a, (0 : ℂ) ∂volume
    symm
    exact integral_zero (ClosedInterval 0 a) ℂ

/-- Suzuki Lemma 4.2, Hilbert–Schmidt part, for every real `ω > 1/2`. -/
theorem suzukiCompressedHankelOperator_isHilbertSchmidt (omega a : ℝ)
    (homega : 1 / 2 < omega) :
    (suzukiCompressedHankelOperator omega a homega).IsHilbertSchmidt := by
  by_cases ha : 1 < a
  · rw [suzukiCompressedHankelOperator, dif_pos ha]
    exact suzukiCompressedHankelOperatorAboveOne_isHilbertSchmidt omega a homega ha
  · rw [suzukiCompressedHankelOperator, dif_neg ha]
    exact ContinuousLinearMap.isHilbertSchmidt_zero

/-- Suzuki Lemma 4.2, self-adjointness part, for every real `ω > 1/2`. -/
theorem suzukiCompressedHankelOperator_isSelfAdjoint (omega a : ℝ)
    (homega : 1 / 2 < omega) :
    IsSelfAdjoint (suzukiCompressedHankelOperator omega a homega) := by
  by_cases ha : 1 < a
  · rw [suzukiCompressedHankelOperator, dif_pos ha]
    exact suzukiCompressedHankelOperatorAboveOne_isSelfAdjoint omega a homega ha
  · rw [suzukiCompressedHankelOperator, dif_neg ha]
    exact IsSelfAdjoint.zero _

end RHTower
