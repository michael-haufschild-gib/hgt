import GaloisForLFunctions.RHTower.SuzukiCanonicalLogSourceL1Derivative
import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelL1Smoothing
import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelPhysicalKernel
import GaloisForLFunctions.RHTower.SuzukiCanonicalHankelL1Resolvent

/-!
# Strong `L¹` derivative of Suzuki's literal boundary row

This module transports global logarithmic `L¹` translation differentiation to a finite physical
window. It constructs the bounded pullback `F(r) ↦ F(log y)`, including the Jacobian estimate
`‖Q_B F‖₁ ≤ B ‖F‖₁`, and identifies a localized smooth extension exactly with Suzuki's literal
boundary row. Consequently the boundary source has a strong `L¹` aperture derivative throughout
the interior of the fixed window, without excluding arithmetic cusps and without strengthening
`omega > 1` to an `L²` derivative assumption.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

theorem integrable_suzukiLogPullback
    {B : ℝ} (hB : 0 < B) (F : ℝ → ℂ) (hF : Integrable F) :
    Integrable (fun y : ClosedInterval 0 B => F (Real.log (y : ℝ))) := by
  change Integrable (fun y : Icc 0 B => F (Real.log (y : ℝ)))
  let c : ℝ := -Real.log B
  let f : ℝ → ℝ := fun t => Real.exp (-t)
  let f' : ℝ → ℝ := fun t => -Real.exp (-t)
  have hf' : ∀ t ∈ Ici c, HasDerivWithinAt f (f' t) (Ici c) t := by
    intro t _
    convert ((Real.hasDerivAt_exp (-t)).comp t
      (hasDerivAt_neg t)).hasDerivWithinAt using 1 <;> first | rfl | ring
  have hinj : Set.InjOn f (Ici c) := by
    intro x _ y _ hxy
    have hlog := congrArg Real.log hxy
    dsimp only [f] at hlog
    simp only [Real.log_exp] at hlog
    linarith
  have himage : f '' Ici c = Ioc 0 B := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : c ≤ t := ht
      constructor
      · exact Real.exp_pos _
      · dsimp only [c] at ht'
        rw [← Real.exp_log hB]
        exact Real.exp_le_exp.mpr (by linarith)
    · intro hy
      refine ⟨-Real.log y, ?_, ?_⟩
      · change c ≤ -Real.log y
        dsimp only [c]
        have hlog : Real.log y ≤ Real.log B :=
          Real.strictMonoOn_log.monotoneOn hy.1 hB hy.2
        linarith
      · change Real.exp (-(-Real.log y)) = y
        rw [neg_neg, Real.exp_log hy.1]
  have hweighted : IntegrableOn
      (fun t => |f' t| • F (Real.log (f t))) (Ici c) := by
    have hbase : Integrable (fun t : ℝ => F (-t)) := hF.comp_neg
    have hbaseOn : Integrable (fun t : ℝ => F (-t))
        (volume.restrict (Ici c)) := hbase.integrableOn
    have hcoefMeas : AEStronglyMeasurable (fun t : ℝ => |f' t|)
        (volume.restrict (Ici c)) :=
      ((continuous_abs.comp (by fun_prop : Continuous f')).aestronglyMeasurable.mono_measure
        (Measure.restrict_le_self))
    have hcoefBound : ∀ᵐ t ∂volume.restrict (Ici c), ‖|f' t|‖ ≤ B :=
      ae_restrict_of_forall_mem measurableSet_Ici fun t ht => by
        have ht' : c ≤ t := ht
        dsimp only [f', c]
        rw [abs_neg, abs_of_pos (Real.exp_pos _), Real.norm_of_nonneg (Real.exp_pos _).le,
          ← Real.exp_log hB]
        exact Real.exp_le_exp.mpr (by linarith)
    have hmul := hbaseOn.bdd_smul B hcoefMeas hcoefBound
    apply hmul.congr
    filter_upwards with t
    change |f' t| • F (-t) = |f' t| • F (Real.log (f t))
    dsimp only [f]
    rw [Real.log_exp]
  have hIoc : IntegrableOn (fun y : ℝ => F (Real.log y)) (Ioc 0 B) := by
    rw [← himage]
    exact (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ici hf' hinj (fun y : ℝ => F (Real.log y))).mpr hweighted
  have hIcc : IntegrableOn (fun y : ℝ => F (Real.log y)) (Icc 0 B) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mpr hIoc
  let hmp : MeasurePreserving ((↑) : Icc 0 B → ℝ)
      (volume : Measure (Icc 0 B))
      ((volume : Measure ℝ).restrict (Icc 0 B)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  exact (hmp.integrable_comp hIcc.1).mpr hIcc

theorem integral_norm_suzukiLogPullback_le
    {B : ℝ} (hB : 0 < B) (F : ℝ → ℂ) (hF : Integrable F) :
    (∫ y : ClosedInterval 0 B, ‖F (Real.log (y : ℝ))‖) ≤
      B * ∫ r : ℝ, ‖F r‖ := by
  change (∫ y : Icc 0 B, ‖F (Real.log (y : ℝ))‖) ≤ _
  let c : ℝ := -Real.log B
  let f : ℝ → ℝ := fun t => Real.exp (-t)
  let f' : ℝ → ℝ := fun t => -Real.exp (-t)
  have hf' : ∀ t ∈ Ici c, HasDerivWithinAt f (f' t) (Ici c) t := by
    intro t _
    convert ((Real.hasDerivAt_exp (-t)).comp t
      (hasDerivAt_neg t)).hasDerivWithinAt using 1 <;> first | rfl | ring
  have hanti : AntitoneOn f (Ici c) := by
    intro u _ v _ huv
    exact Real.exp_le_exp.mpr (neg_le_neg huv)
  have himage : f '' Ici c = Ioc 0 B := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : c ≤ t := ht
      constructor
      · exact Real.exp_pos _
      · dsimp only [c] at ht'
        rw [← Real.exp_log hB]
        exact Real.exp_le_exp.mpr (by linarith)
    · intro hy
      refine ⟨-Real.log y, ?_, ?_⟩
      · change c ≤ -Real.log y
        dsimp only [c]
        have hlog : Real.log y ≤ Real.log B :=
          Real.strictMonoOn_log.monotoneOn hy.1 hB hy.2
        linarith
      · change Real.exp (-(-Real.log y)) = y
        rw [neg_neg, Real.exp_log hy.1]
  have hcov := MeasureTheory.integral_image_eq_integral_deriv_smul_of_antitoneOn
    measurableSet_Ici hf' hanti (fun y : ℝ => ‖F (Real.log y)‖)
  rw [himage] at hcov
  dsimp only [f, f'] at hcov
  simp only [neg_neg, Real.log_exp, smul_eq_mul] at hcov
  have hleft : (∫ y : Icc 0 B, ‖F (Real.log (y : ℝ))‖) =
      ∫ y in Ioc 0 B, ‖F (Real.log y)‖ := by
    calc
      (∫ y : Icc 0 B, ‖F (Real.log (y : ℝ))‖) =
          ∫ y in Icc 0 B, ‖F (Real.log y)‖ :=
        MeasureTheory.integral_subtype measurableSet_Icc
          (fun y : ℝ => ‖F (Real.log y)‖)
      _ = ∫ y in Ioc 0 B, ‖F (Real.log y)‖ :=
        MeasureTheory.integral_Icc_eq_integral_Ioc
  rw [hleft, hcov]
  have hbase : Integrable (fun t : ℝ => ‖F (-t)‖) := (hF.comp_neg).norm
  have hcoefMeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-t))
      (volume.restrict (Ici c)) :=
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-t)).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self)
  have hcoefBound : ∀ᵐ t ∂volume.restrict (Ici c), ‖Real.exp (-t)‖ ≤ B :=
    ae_restrict_of_forall_mem measurableSet_Ici fun t ht => by
      have ht' : c ≤ t := ht
      rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_log hB]
      dsimp only [c] at ht'
      exact Real.exp_le_exp.mpr (by linarith)
  have hweighted : Integrable (fun t : ℝ => Real.exp (-t) * ‖F (-t)‖)
      (volume.restrict (Ici c)) :=
    hbase.integrableOn.bdd_mul hcoefMeas hcoefBound
  have hupper : Integrable (fun t : ℝ => B * ‖F (-t)‖)
      (volume.restrict (Ici c)) := (hbase.const_mul B).integrableOn
  have hpoint : (fun t : ℝ => Real.exp (-t) * ‖F (-t)‖) ≤ᵐ[volume.restrict (Ici c)]
      fun t => B * ‖F (-t)‖ :=
    ae_restrict_of_forall_mem measurableSet_Ici fun t ht => by
      have ht' : c ≤ t := ht
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [← Real.exp_log hB]
      dsimp only [c] at ht'
      exact Real.exp_le_exp.mpr (by linarith)
  calc
    (∫ t in Ici c, Real.exp (-t) * ‖F (-t)‖) ≤
        ∫ t in Ici c, B * ‖F (-t)‖ :=
      integral_mono_ae hweighted hupper hpoint
    _ ≤ ∫ t : ℝ, B * ‖F (-t)‖ :=
      setIntegral_le_integral (hbase.const_mul B)
        (Eventually.of_forall fun t => mul_nonneg hB.le (norm_nonneg _))
    _ = B * ∫ t : ℝ, ‖F (-t)‖ := by rw [integral_const_mul]
    _ = B * ∫ r : ℝ, ‖F r‖ := by
      congr 1
      exact (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
        (Homeomorph.neg ℝ).measurableEmbedding (fun r : ℝ => ‖F r‖)

theorem ae_suzukiLogPullback_of_ae
    {B : ℝ} (_hB : 0 < B) {F G : ℝ → ℂ} (hFG : F =ᵐ[volume] G) :
    (fun y : ClosedInterval 0 B => F (Real.log (y : ℝ))) =ᵐ[volume]
      fun y => G (Real.log (y : ℝ)) := by
  change (fun y : Icc 0 B => F (Real.log (y : ℝ))) =ᵐ[volume]
    fun y => G (Real.log (y : ℝ))
  have hlogRestrict := realLog_restrict_Ioi_quasiMeasurePreserving.ae hFG
  have hlogWhole := (ae_restrict_iff' measurableSet_Ioi).mp hlogRestrict
  let hmp : MeasurePreserving ((↑) : Icc 0 B → ℝ)
      (volume : Measure (Icc 0 B))
      ((volume : Measure ℝ).restrict (Icc 0 B)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hlogSub := hmp.quasiMeasurePreserving.ae (ae_restrict_of_ae hlogWhole)
  have hne := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae ((volume : Measure ℝ).ae_ne 0))
  filter_upwards [hlogSub, hne] with y hy hne
  exact hy (lt_of_le_of_ne y.property.1 (Ne.symm hne))

theorem integrable_realL1_coe (F : Lp ℂ 1 (volume : Measure ℝ)) :
    Integrable (F : ℝ → ℂ) :=
  memLp_one_iff_integrable.mp (Lp.memLp F)

def suzukiLogPullbackL1Value
    (B : ℝ) (hB : 0 < B) (F : Lp ℂ 1 (volume : Measure ℝ)) : IntervalL1 0 B :=
  (integrable_suzukiLogPullback hB (F : ℝ → ℂ) (integrable_realL1_coe F)).toL1
    (fun y : ClosedInterval 0 B => F (Real.log (y : ℝ)))

theorem suzukiLogPullbackL1Value_ae
    (B : ℝ) (hB : 0 < B) (F : Lp ℂ 1 (volume : Measure ℝ)) :
    (suzukiLogPullbackL1Value B hB F : ClosedInterval 0 B → ℂ) =ᵐ[volume]
      fun y => F (Real.log (y : ℝ)) :=
  (integrable_suzukiLogPullback hB (F : ℝ → ℂ) (integrable_realL1_coe F)).coeFn_toL1

def suzukiLogPullbackL1Linear
    (B : ℝ) (hB : 0 < B) :
    Lp ℂ 1 (volume : Measure ℝ) →ₗ[ℂ] IntervalL1 0 B where
  toFun := suzukiLogPullbackL1Value B hB
  map_add' F G := by
    apply Lp.ext
    have hsource := ae_suzukiLogPullback_of_ae hB (Lp.coeFn_add F G)
    filter_upwards [suzukiLogPullbackL1Value_ae B hB (F + G),
      suzukiLogPullbackL1Value_ae B hB F,
      suzukiLogPullbackL1Value_ae B hB G,
      Lp.coeFn_add (suzukiLogPullbackL1Value B hB F)
        (suzukiLogPullbackL1Value B hB G), hsource] with y hleft hF hG hout hsrc
    rw [hleft, hout]
    simp only [Pi.add_apply] at hsrc ⊢
    rw [hF, hG, hsrc]
  map_smul' c F := by
    apply Lp.ext
    have hsource := ae_suzukiLogPullback_of_ae hB (Lp.coeFn_smul c F)
    filter_upwards [suzukiLogPullbackL1Value_ae B hB (c • F),
      suzukiLogPullbackL1Value_ae B hB F,
      Lp.coeFn_smul c (suzukiLogPullbackL1Value B hB F), hsource] with
        y hleft hF hout hsrc
    rw [hleft]
    simp only [RingHom.id_apply]
    rw [hout]
    simp only [Pi.smul_apply] at hsrc ⊢
    rw [hF, hsrc]

theorem norm_suzukiLogPullbackL1Value_le
    (B : ℝ) (hB : 0 < B) (F : Lp ℂ 1 (volume : Measure ℝ)) :
    ‖suzukiLogPullbackL1Value B hB F‖ ≤ B * ‖F‖ := by
  rw [L1.norm_eq_integral_norm]
  calc
    (∫ y : ClosedInterval 0 B, ‖(suzukiLogPullbackL1Value B hB F) y‖) =
        ∫ y : ClosedInterval 0 B, ‖F (Real.log (y : ℝ))‖ := by
      apply integral_congr_ae
      exact (suzukiLogPullbackL1Value_ae B hB F).fun_comp norm
    _ ≤ B * ∫ r : ℝ, ‖F r‖ :=
      integral_norm_suzukiLogPullback_le hB (F : ℝ → ℂ) (integrable_realL1_coe F)
    _ = B * ‖F‖ := by rw [L1.norm_eq_integral_norm]

def suzukiLogPullbackL1
    (B : ℝ) (hB : 0 < B) :
    Lp ℂ 1 (volume : Measure ℝ) →L[ℂ] IntervalL1 0 B :=
  (suzukiLogPullbackL1Linear B hB).mkContinuous B
    (norm_suzukiLogPullbackL1Value_le B hB)

@[simp] theorem suzukiLogPullbackL1_apply
    (B : ℝ) (hB : 0 < B) (F : Lp ℂ 1 (volume : Measure ℝ)) :
    suzukiLogPullbackL1 B hB F = suzukiLogPullbackL1Value B hB F := rfl

theorem suzukiLogPullbackL1_ae
    (B : ℝ) (hB : 0 < B) (F : Lp ℂ 1 (volume : Measure ℝ)) :
    (suzukiLogPullbackL1 B hB F : ClosedInterval 0 B → ℂ) =ᵐ[volume]
      fun y => F (Real.log (y : ℝ)) := by
  rw [suzukiLogPullbackL1_apply]
  exact suzukiLogPullbackL1Value_ae B hB F

theorem suzukiLogPullbackL1_realL1Translate_integrableToL1_ae
    (B : ℝ) (hB : 0 < B) (f : ℝ → ℂ) (hf : Integrable f) (t : ℝ) :
    (suzukiLogPullbackL1 B hB
        (realL1Translate t (integrableToL1 f hf)) : ClosedInterval 0 B → ℂ) =ᵐ[volume]
      fun y => f (t + Real.log (y : ℝ)) := by
  have htranslate := ae_suzukiLogPullback_of_ae hB
    (realL1Translate_ae t (integrableToL1 f hf) |>.trans <|
      (measurePreserving_realAddTranslationFamily t).quasiMeasurePreserving.ae
        (integrableToL1_ae f hf))
  filter_upwards [suzukiLogPullbackL1_ae B hB
      (realL1Translate t (integrableToL1 f hf)), htranslate] with y hleft hright
  rw [hleft]
  simpa only [realAddTranslationFamily_apply] using hright

theorem hasDerivAt_suzukiLogPullbackL1_realL1Translate_of_integral_eq_sub
    (B : ℝ) (hB : 0 < B) (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g)
    (hFTC : ∀ x y : ℝ, (∫ r in x..y, g r) = f y - f x) (s : ℝ) :
    HasDerivAt
      (fun t : ℝ => suzukiLogPullbackL1 B hB
        (realL1Translate t (integrableToL1 f hf)))
      (suzukiLogPullbackL1 B hB
        (realL1Translate s (integrableToL1 g hg))) s := by
  have hglobal := hasDerivAt_realL1Translate_of_integral_eq_sub f g hf hg hFTC s
  exact ((suzukiLogPullbackL1 B hB).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    s hglobal

def suzukiFixedWindowBoundarySourceL1
    (omega B : ℝ) (homega : 1 < omega) (hB : 1 < B) (a : ℝ) : IntervalL1 0 B :=
  suzukiIntervalL2AsL1 B
    (suzukiFixedWindowBoundarySource omega B (by linarith) hB a)

theorem suzukiFixedWindowBoundarySourceL1_ae
    {omega B a : ℝ} (homega : 1 < omega) (hB : 1 < B)
    (ha : 0 < a) (haB : a ≤ B) :
    (suzukiFixedWindowBoundarySourceL1 omega B homega hB a :
        ClosedInterval 0 B → ℂ) =ᵐ[volume]
      fun y => suzukiSourceHFinite omega (a * (y : ℝ)) := by
  filter_upwards [suzukiIntervalL2AsL1_ae B
      (suzukiFixedWindowBoundarySource omega B (by linarith) hB a),
    suzukiCompressedHankelRow_ae (omega := omega) (a := B) (x := a)
      (by linarith) hB ha haB] with y hL1 hrow
  exact hL1.trans hrow

def suzukiSourceLogExtensionHorizon (B s : ℝ) : ℝ :=
  max 0 (s + Real.log B) + 1

theorem suzukiSourceLogExtensionHorizon_nonneg (B s : ℝ) :
    0 ≤ suzukiSourceLogExtensionHorizon B s := by
  unfold suzukiSourceLogExtensionHorizon
  linarith [le_max_left 0 (s + Real.log B)]

theorem lt_suzukiSourceLogExtensionHorizon (B s : ℝ) :
    s + Real.log B < suzukiSourceLogExtensionHorizon B s := by
  unfold suzukiSourceLogExtensionHorizon
  linarith [le_max_right 0 (s + Real.log B)]

theorem suzukiFixedWindowBoundarySourceL1_eq_logPullback_smoothExtension
    {omega B R t : ℝ} (homega : 1 < omega) (hB : 1 < B)
    (hR : 0 ≤ R) (htB : Real.exp t ≤ B) (htR : t + Real.log B ≤ R) :
    suzukiFixedWindowBoundarySourceL1 omega B homega hB (Real.exp t) =
      suzukiLogPullbackL1 B (by linarith)
        (realL1Translate t
          (integrableToL1 (suzukiSourceHLogSmoothExtension omega R)
            (integrable_suzukiSourceHLogSmoothExtension homega R))) := by
  apply Lp.ext
  have hsource := suzukiFixedWindowBoundarySourceL1_ae homega hB
    (Real.exp_pos t) htB
  have hpull := suzukiLogPullbackL1_realL1Translate_integrableToL1_ae
    B (by linarith) (suzukiSourceHLogSmoothExtension omega R)
      (integrable_suzukiSourceHLogSmoothExtension homega R) t
  let hmp : MeasurePreserving ((↑) : ClosedInterval 0 B → ℝ)
      (volume : Measure (ClosedInterval 0 B))
      ((volume : Measure ℝ).restrict (Icc 0 B)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  have hne := hmp.quasiMeasurePreserving.ae
    (ae_restrict_of_ae ((volume : Measure ℝ).ae_ne 0))
  filter_upwards [hsource, hpull, hne] with y hsource hpull hyne
  rw [hsource, hpull]
  have hypos : 0 < (y : ℝ) :=
    lt_of_le_of_ne y.property.1 (Ne.symm hyne)
  have hylog : Real.log (y : ℝ) ≤ Real.log B :=
    Real.strictMonoOn_log.monotoneOn hypos (lt_trans zero_lt_one hB) y.property.2
  rw [suzukiSourceHLogSmoothExtension_eq_sourceHFinite_exp omega hR (by linarith),
    Real.exp_add, Real.exp_log hypos]

def suzukiFixedWindowBoundarySourceLogDerivativeL1
    (omega B : ℝ) (homega : 1 < omega) (hB : 1 < B) (s : ℝ) : IntervalL1 0 B :=
  let R := suzukiSourceLogExtensionHorizon B s
  suzukiLogPullbackL1 B (by linarith)
    (realL1Translate s
      (integrableToL1 (suzukiSourceHLogSmoothExtensionDerivative omega R)
        (integrable_suzukiSourceHLogSmoothExtensionDerivative homega R)))

/-- Literal fixed-window boundary row, parametrized by logarithmic aperture, has an unconditional
strong `L¹` derivative at every aperture strictly inside the fixed window. -/
theorem hasDerivAt_suzukiFixedWindowBoundarySourceL1_exp
    {omega B s : ℝ} (homega : 1 < omega) (hB : 1 < B)
    (hsB : Real.exp s < B) :
    HasDerivAt
      (fun t : ℝ => suzukiFixedWindowBoundarySourceL1 omega B homega hB (Real.exp t))
      (suzukiFixedWindowBoundarySourceLogDerivativeL1 omega B homega hB s) s := by
  let R := suzukiSourceLogExtensionHorizon B s
  have hR : 0 ≤ R := suzukiSourceLogExtensionHorizon_nonneg B s
  have hsR : s + Real.log B < R := lt_suzukiSourceLogExtensionHorizon B s
  have hglobal := hasDerivAt_suzukiLogPullbackL1_realL1Translate_of_integral_eq_sub
    B (by linarith) (suzukiSourceHLogSmoothExtension omega R)
      (suzukiSourceHLogSmoothExtensionDerivative omega R)
      (integrable_suzukiSourceHLogSmoothExtension homega R)
      (integrable_suzukiSourceHLogSmoothExtensionDerivative homega R)
      (integral_suzukiSourceHLogSmoothExtensionDerivative_eq_sub homega R) s
  have hexpEvent : ∀ᶠ t : ℝ in nhds s, Real.exp t < B :=
    Real.continuous_exp.continuousAt.eventually (Iio_mem_nhds hsB)
  have hhorEvent : ∀ᶠ t : ℝ in nhds s, t + Real.log B < R :=
    (continuousAt_id.add continuousAt_const).eventually (Iio_mem_nhds hsR)
  have hev : (fun t : ℝ =>
      suzukiFixedWindowBoundarySourceL1 omega B homega hB (Real.exp t)) =ᶠ[nhds s]
      fun t => suzukiLogPullbackL1 B (by linarith)
        (realL1Translate t
          (integrableToL1 (suzukiSourceHLogSmoothExtension omega R)
            (integrable_suzukiSourceHLogSmoothExtension homega R))) := by
    filter_upwards [hexpEvent, hhorEvent] with t htB htR
    exact suzukiFixedWindowBoundarySourceL1_eq_logPullback_smoothExtension
      homega hB hR htB.le htR.le
  change HasDerivAt _
    (suzukiLogPullbackL1 B (by linarith)
      (realL1Translate s
        (integrableToL1 (suzukiSourceHLogSmoothExtensionDerivative omega R)
          (integrable_suzukiSourceHLogSmoothExtensionDerivative homega R)))) s
  exact hglobal.congr_of_eventuallyEq hev

def suzukiFixedWindowBoundarySourceDerivativeL1
    (omega B : ℝ) (homega : 1 < omega) (hB : 1 < B) (a : ℝ) : IntervalL1 0 B :=
  (a⁻¹ : ℝ) •
    suzukiFixedWindowBoundarySourceLogDerivativeL1 omega B homega hB (Real.log a)

/-- Literal fixed-window boundary row has a strong `L¹` physical-aperture derivative at every
positive aperture strictly inside the window.  No cusp exclusion is needed in `L¹`. -/
theorem hasDerivAt_suzukiFixedWindowBoundarySourceL1
    {omega B a : ℝ} (homega : 1 < omega) (hB : 1 < B)
    (ha : 0 < a) (haB : a < B) :
    HasDerivAt (suzukiFixedWindowBoundarySourceL1 omega B homega hB)
      (suzukiFixedWindowBoundarySourceDerivativeL1 omega B homega hB a) a := by
  have hexpB : Real.exp (Real.log a) < B := by rw [Real.exp_log ha]; exact haB
  have hlog := hasDerivAt_suzukiFixedWindowBoundarySourceL1_exp homega hB hexpB
  have hcomp := hlog.hasFDerivAt.comp_hasDerivAt_of_eq a
    (Real.hasDerivAt_log ha.ne') rfl
  have hev : suzukiFixedWindowBoundarySourceL1 omega B homega hB =ᶠ[nhds a]
      fun z : ℝ => suzukiFixedWindowBoundarySourceL1 omega B homega hB
        (Real.exp (Real.log z)) := by
    filter_upwards [Ioi_mem_nhds ha] with z hz
    rw [Real.exp_log hz]
  change HasDerivAt _
    ((a⁻¹ : ℝ) •
      suzukiFixedWindowBoundarySourceLogDerivativeL1 omega B homega hB (Real.log a)) a
  exact hcomp.congr_of_eventuallyEq hev

end RHTower
