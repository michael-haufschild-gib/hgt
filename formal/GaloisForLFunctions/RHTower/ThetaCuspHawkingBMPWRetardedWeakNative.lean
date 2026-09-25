import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPWFullFutureWeakNative

/-!
# PW-B retarded full/native weak law

Time reflection transports the exact full-circle Goursat contact to the
future cone of a source event. The literal retarded response consequently
satisfies a compact-test weak equation with the native coupling retained.
This does not admit a response as test or identify the ordered top-time cap.
-/

open MeasureTheory Set
open scoped ContDiff
namespace RHTower.D4BMPWRetardedWeakNative
open D4BMGeneralTemporalTransposition D4BMFullAngularGoursatTransposition
open D4BMFullAngularReconstruction D4BMModularCore D4BMGlobalAngularResponse
open D4BMFullAngularCausalPeierls D4BMJointSource
open D4BMFullAngularCircle D4BMCausalKernel D4BMFullSourceAdvanced
open D4BMLiteralCyclicPeierls D4BMFullAngularGrowth D4BMNativeCircle
noncomputable section
set_option autoImplicit false

abbrev Event := ℝ × ℝ

private def timeFlip : Event →L[ℝ] Event :=
  (-(ContinuousLinearMap.fst ℝ ℝ ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

private def timeFlipHomeo : Event ≃ₜ Event :=
  Homeomorph.prodCongr (Homeomorph.neg ℝ) (Homeomorph.refl ℝ)

@[simp] private theorem timeFlip_apply (p : Event) : timeFlip p = (-p.1,p.2) := rfl
@[simp] private theorem timeFlipHomeo_apply (p : Event) : timeFlipHomeo p = timeFlip p := rfl
@[simp] private theorem timeFlip_involutive (p : Event) : timeFlip (timeFlip p) = p := by
  ext <;> simp

private theorem timeFlip_time : timeFlip (1,0) = -(1,0) := by
  ext <;> simp

private theorem timeFlip_space : timeFlip (0,1) = (0,1) := by
  ext <;> simp

private theorem eventDir_timeFlip (phi : Event → ℂ)
    (hp : ContDiff ℝ ∞ phi) (v p : Event) :
    eventDir v (fun z => phi (timeFlip z)) p =
      eventDir (timeFlip v) phi (timeFlip p) := by
  have hcomp : HasFDerivAt (fun z : Event => phi (timeFlip z))
      ((fderiv ℝ phi (timeFlip p)).comp timeFlip) p :=
    ((hp.differentiable (by simp) (timeFlip p)).hasFDerivAt).comp p
      timeFlip.hasFDerivAt
  rw [eventDir, hcomp.fderiv]
  rfl

private theorem eventDir_neg_fun (phi : Event → ℂ) (v p : Event) :
    eventDir v (fun z => -phi z) p = -eventDir v phi p := by
  simp [eventDir]

private theorem eventWave_timeFlip (phi : Event → ℂ)
    (hp : ContDiff ℝ ∞ phi) (p : Event) :
    eventWave (fun z => phi (timeFlip z)) (timeFlip p) = eventWave phi p := by
  have htime : eventDir (1,0) (fun z => phi (timeFlip z)) =
      fun z => -eventDir (1,0) phi (timeFlip z) := by
    funext z
    rw [eventDir_timeFlip phi hp]
    rw [timeFlip_time]
    change (fderiv ℝ phi (timeFlip z)) (-(1,0)) =
      -(fderiv ℝ phi (timeFlip z)) (1,0)
    simp only [map_neg]
  have hspace : eventDir (0,1) (fun z => phi (timeFlip z)) =
      fun z => eventDir (0,1) phi (timeFlip z) := by
    funext z
    rw [eventDir_timeFlip phi hp]
    simp
  have ht : ContDiff ℝ ∞ (eventDir (1,0) phi) :=
    (hp.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hx : ContDiff ℝ ∞ (eventDir (0,1) phi) :=
    (hp.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  unfold eventWave
  rw [htime, hspace, eventDir_neg_fun,
    eventDir_timeFlip (eventDir (1,0) phi) ht,
    eventDir_timeFlip (eventDir (0,1) phi) hx]
  rw [timeFlip_time]
  simp only [timeFlip_involutive, timeFlip_space, eventDir, map_neg, neg_neg]

private theorem integral_timeFlip (F : Event → ℂ) :
    (∫ p : Event, F (timeFlip p)) = ∫ p : Event, F p := by
  change (∫ p : Event, F (-p.1,p.2)) = _
  rw [Measure.volume_eq_prod ℝ ℝ]
  exact ((Measure.measurePreserving_neg volume).prod (MeasurePreserving.id volume)).integral_comp
    (((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ)).measurableEmbedding) F

private def reflectedTest (phi : Event → ℂ) : Event → ℂ :=
  fun p => phi (timeFlip p)

private theorem reflectedTest_smooth (phi : Event → ℂ) (hp : ContDiff ℝ ∞ phi) :
    ContDiff ℝ ∞ (reflectedTest phi) :=
  hp.comp timeFlip.contDiff

private theorem reflectedTest_compact (phi : Event → ℂ) (hc : HasCompactSupport phi) :
    HasCompactSupport (reflectedTest phi) := by
  exact hc.comp_homeomorph timeFlipHomeo

private def futureResidual (q : XiZeroCopy) (branch : Bool)
    (s y X k : ℝ) (phi : Event → ℂ) (p : Event) : ℂ :=
  fullDirichletTemporalResidual q branch (-s) y X k (reflectedTest phi) (timeFlip p)

private theorem futureResidual_kernel (q : XiZeroCopy) (branch : Bool)
    (s y X k : ℝ) (phi : Event → ℂ) (hp : ContDiff ℝ ∞ phi) (p : Event) :
    futureResidual q branch s y X k phi p =
      angularDirichletKernel q branch (p.1-s) p.2 y X k * eventWave phi p -
        parameter q branch *
          (angularDirichletKernel q branch (p.1-s) p.2 y X k +
            D4BMNativeCircle.nativeDirichletCausalKernel q (p.1-s) p.2 y X k) /
          (Real.cosh p.2 : ℂ)^(2 : ℕ) * phi p := by
  unfold futureResidual
  rw [fullDirichletTemporalResidual_kernel]
  have hw : eventWave (reflectedTest phi) (timeFlip p) = eventWave phi p :=
    eventWave_timeFlip phi hp p
  rw [hw]
  simp only [timeFlip_apply, reflectedTest, neg_neg]
  ring

theorem futureResidual_integral (q : XiZeroCopy) (branch : Bool)
    (s y X k : ℝ) (phi : Event → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    (∫ p : Event, futureResidual q branch s y X k phi p) =
      fullAngularField q branch ![X, Real.exp k] *
        (phi (s,y)-phi (s,-y)) := by
  have h := fullDirichletTemporalResidual_integral q branch (-s) y X k
    (reflectedTest phi) (reflectedTest_smooth phi hp) (reflectedTest_compact phi hc)
  rw [← integral_timeFlip] at h
  simpa [futureResidual, reflectedTest] using h

private theorem futureResidual_integrable (q : XiZeroCopy) (branch : Bool)
    (s y X k : ℝ) (phi : Event → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    Integrable (futureResidual q branch s y X k phi) := by
  have hs := reflectedTest_smooth phi hp
  have hc' := reflectedTest_compact phi hc
  have h : Integrable
      (fullDirichletTemporalResidual q branch (-s) y X k (reflectedTest phi)) := by
    unfold fullDirichletTemporalResidual
    exact ((fullTemporalConeResidual_integrable q branch (-s) y X k
      (reflectedTest phi) hs hc').sub
      (fullTemporalConeResidual_integrable q branch (-s) (-y) X k
        (reflectedTest phi) hs hc')).div_const 2
  unfold futureResidual
  rw [Measure.volume_eq_prod ℝ ℝ] at h ⊢
  have hmp : MeasurePreserving (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ))
      (volume.prod volume) (volume.prod volume) :=
    (Measure.measurePreserving_neg volume).prod (MeasurePreserving.id volume)
  exact (hmp.integrable_comp_emb
    (((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ)).measurableEmbedding)).mpr h

private def retardedTestDensity (q : XiZeroCopy) (branch b : Bool)
    (a : ℂ) (X k : ℝ) (phi : Event → ℂ) (z : Event × Event) : ℂ :=
  phi z.2 * (angularDirichletKernel q branch (z.2.1-z.1.1) z.2.2 z.1.2 X k *
    timeReducedCoefficient (physicalRate q b) a z.1.1 z.1.2)

private theorem kernel_measurable (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    Measurable (fun z : ℝ × ℝ × ℝ =>
      angularDirichletKernel q branch z.1 z.2.1 z.2.2 X k) := by
  classical
  have cone (y : (ℝ × ℝ × ℝ) → ℝ) (hy : Continuous y) :
      Measurable (fun p : ℝ × ℝ × ℝ =>
        if |p.2.1 - y p| ≤ p.1 then
          angularMean q branch (Real.arcosh (invariant p.1 p.2.1 (y p))) X k else 0) := by
    have hi : Continuous (fun p : ℝ × ℝ × ℝ => invariant p.1 p.2.1 (y p)) := by
      unfold invariant
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro p
        exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
    have hr : Continuous (fun p : ℝ × ℝ × ℝ =>
        Real.arcosh (max 1 (invariant p.1 p.2.1 (y p)))) :=
      Real.continuousOn_arcosh.comp_continuous (continuous_const.max hi)
        (fun p => show max 1 (invariant p.1 p.2.1 (y p)) ∈ Ici 1 from
          le_max_left 1 (invariant p.1 p.2.1 (y p)))
    have hm := ((angularMean_smooth q branch X k).continuous.comp hr).measurable
    have hs : MeasurableSet {p : ℝ × ℝ × ℝ | |p.2.1 - y p| ≤ p.1} :=
      (isClosed_le (continuous_snd.fst.sub hy).abs continuous_fst).measurableSet
    have he : Measurable (fun p : ℝ × ℝ × ℝ =>
        if |p.2.1 - y p| ≤ p.1 then
          angularMean q branch (Real.arcosh (max 1 (invariant p.1 p.2.1 (y p)))) X k else 0) :=
      Measurable.ite hs hm measurable_const
    convert he using 1
    funext p
    by_cases hc : |p.2.1 - y p| ≤ p.1
    · simp only [if_pos hc, max_eq_right (invariant_causal ⟨p.1, p.2.1, y p, hc⟩)]
    · rw [if_neg hc, if_neg hc]
  have hd := cone (fun p => p.2.2) (by fun_prop)
  have hi := cone (fun p => -p.2.2) (by fun_prop)
  simpa only [angularDirichletKernel, sub_neg_eq_add, Pi.sub_apply] using
    (hd.sub hi).div_const (2 : ℂ)

private theorem retardedTestDensity_measurable (q : XiZeroCopy)
    (branch b : Bool) (a : ℂ) (X k : ℝ) (phi : Event → ℂ)
    (hphi : Continuous phi) :
    Measurable (retardedTestDensity q branch b a X k phi) := by
  have hk := (kernel_measurable q branch X k).comp
    (show Measurable (fun z : Event × Event =>
      ((z.2.1-z.1.1,z.2.2,z.1.2) : ℝ × ℝ × ℝ)) by fun_prop)
  have hj := (timeReducedCoefficient_joint_continuous (physicalRate q b) a).measurable.comp
    (measurable_fst : Measurable (Prod.fst : Event × Event → Event))
  exact (hphi.measurable.comp measurable_snd).mul (hk.mul hj)

private def sourceWeight (q : XiZeroCopy) (v : ℝ) (p : Event) : ℝ :=
  Real.exp (v*p.1)*Real.exp ((2-decayExponent q)*p.2)

private theorem sourceWeight_integrable (q : XiZeroCopy) (v : ℝ) (hv : v < 0) :
    Integrable (sourceWeight q v) eventMeasure := by
  have ht := integrableOn_exp_mul_Ioi hv 0
  have hx := (integrableOn_exp_mul_Iic (show 0 < 2-decayExponent q from
    sub_pos.mpr (decayExponent_bounds q).2) 0).mono_set Iio_subset_Iic_self
  exact ht.mul_prod hx

private theorem retardedTestDensity_integrable (q : XiZeroCopy) (branch b : Bool)
    (a : ℂ) (X k : ℝ) (phi : Event → ℂ)
    (hphi : Continuous phi) (hc : HasCompactSupport phi) :
    Integrable (retardedTestDensity q branch b a X k phi)
      (eventMeasure.prod volume) := by
  obtain ⟨C,hC,hK⟩ := angularDirichletKernel_strict_growth q branch X k
  obtain ⟨D,hD,hJ⟩ := timeReducedCoefficient_physical_bound q b a _
    (decayExponent_bounds q).2
  let g := strictGrowthExponent q
  let c := decayExponent q
  let w : Event → ℝ := fun r => ‖phi r‖*Real.exp (g*r.1)
  have hw : Integrable w := by
    apply (hphi.norm.mul (by fun_prop)).integrable_of_hasCompactSupport
    exact hc.norm.mul_right
  have hrate : -c-g < 0 := by
    have h1 := (sourceGrowthExponent_bounds q).1
    have h2 := (strictGrowthExponent_bounds q).1
    have h3 := (decayExponent_bounds q).1
    dsimp [c,g]
    linarith
  have hm := ((sourceWeight_integrable q (-c-g) hrate).mul_prod hw).const_mul (C*D)
  apply hm.mono' (retardedTestDensity_measurable q branch b a X k phi hphi).aestronglyMeasurable
  have he : ∀ᵐ p : Event ∂eventMeasure, p.2 < 0 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((isOpen_lt continuous_snd continuous_const).measurableSet :
        MeasurableSet {p : Event | p.2 < 0})).mpr
    exact ae_of_all _ (fun _ => ae_restrict_mem measurableSet_Iio)
  have hz : ∀ᵐ z : Event × Event ∂eventMeasure.prod volume, z.1.2 < 0 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((isOpen_lt continuous_fst.snd continuous_const).measurableSet :
        MeasurableSet {z : Event × Event | z.1.2 < 0})).mpr
    filter_upwards [he] with p hp
    exact ae_of_all _ (fun _ => hp)
  filter_upwards [hz] with z hz
  by_cases ht : 0 ≤ z.2.1-z.1.1
  · have hb := mul_le_mul (hK (z.2.1-z.1.1) z.2.2 z.1.2 ht)
      (hJ z.1.1 z.1.2 hz) (norm_nonneg _)
      (mul_nonneg hC (Real.exp_pos _).le)
    have h := mul_le_mul_of_nonneg_left hb (norm_nonneg (phi z.2))
    rw [retardedTestDensity, norm_mul, norm_mul]
    apply h.trans_eq
    dsimp only [sourceWeight, w, c, g]
    simp only [sub_mul, mul_sub, neg_mul, Real.exp_sub, Real.exp_neg]
    ring
  · have hneg : z.2.1-z.1.1 < 0 := lt_of_not_ge ht
    have hzero : angularDirichletKernel q branch (z.2.1-z.1.1) z.2.2 z.1.2 X k = 0 := by
      have h1 : ¬ |z.2.2-z.1.2| ≤ z.2.1-z.1.1 :=
        not_le.mpr ((abs_nonneg _).trans_lt' hneg)
      have h2 : ¬ |z.2.2+z.1.2| ≤ z.2.1-z.1.1 :=
        not_le.mpr ((abs_nonneg _).trans_lt' hneg)
      simp [angularDirichletKernel,h1,h2]
    rw [retardedTestDensity,hzero,zero_mul,mul_zero,norm_zero]
    dsimp only [sourceWeight,w]
    positivity

private theorem retardedTestDensity_source_integral (q : XiZeroCopy)
    (branch b : Bool) (a : ℂ) (X k : ℝ) (phi : Event → ℂ) (r : Event) :
    (∫ p : Event, retardedTestDensity q branch b a X k phi (p,r) ∂eventMeasure) =
      fullRetardedResponse q branch b a r.1 r.2 X k * phi r := by
  rw [fullRetardedResponse, ← integral_mul_const]
  apply integral_congr_ae
  exact ae_of_all _ (fun p => by
    change phi r * (angularDirichletKernel q branch (r.1-p.1) r.2 p.2 X k *
        timeReducedCoefficient (physicalRate q b) a p.1 p.2) =
      (angularDirichletKernel q branch (r.1-p.1) r.2 p.2 X k *
        timeReducedCoefficient (physicalRate q b) a p.1 p.2) * phi r
    ring)

private theorem retardedTestDensity_target_integral (q : XiZeroCopy)
    (branch b : Bool) (a : ℂ) (X k : ℝ) (phi : Event → ℂ) (p : Event) :
    (∫ r : Event, retardedTestDensity q branch b a X k phi (p,r)) =
      timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
        ∫ r : Event,
          angularDirichletKernel q branch (r.1-p.1) r.2 p.2 X k * phi r := by
  have he (r : Event) : retardedTestDensity q branch b a X k phi (p,r) =
      timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
        (angularDirichletKernel q branch (r.1-p.1) r.2 p.2 X k * phi r) := by
    unfold retardedTestDensity
    ring
  simp_rw [he]
  exact integral_const_mul _ _

theorem fullRetardedResponse_test_fubini (q : XiZeroCopy)
    (branch b : Bool) (a : ℂ) (X k : ℝ) (phi : Event → ℂ)
    (hphi : Continuous phi) (hc : HasCompactSupport phi) :
    (∫ r : Event, fullRetardedResponse q branch b a r.1 r.2 X k * phi r) =
      ∫ p : Event, timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
        (∫ r : Event,
          angularDirichletKernel q branch (r.1-p.1) r.2 p.2 X k * phi r)
        ∂eventMeasure := by
  have hi := retardedTestDensity_integrable q branch b a X k phi hphi hc
  have h := integral_integral_swap
    (f := fun p r => retardedTestDensity q branch b a X k phi (p,r)) hi
  simpa only [retardedTestDensity_source_integral,
    retardedTestDensity_target_integral] using h.symm

private theorem eventWave_continuous_compact {phi : Event → ℂ}
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    Continuous (eventWave phi) ∧ HasCompactSupport (eventWave phi) := by
  have hd (v : Event) : ContDiff ℝ ∞ (eventDir v phi) :=
    (hp.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdd (v w : Event) : ContDiff ℝ ∞ (eventDir v (eventDir w phi)) :=
    ((hd w).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  constructor
  · exact ((hdd (1,0) (1,0)).sub (hdd (0,1) (0,1))).continuous
  · unfold eventWave eventDir
    exact ((hc.fderiv_apply ℝ (1,0)).fderiv_apply ℝ (1,0)).sub
      ((hc.fderiv_apply ℝ (0,1)).fderiv_apply ℝ (0,1))

def retardedCoupledBulkDensity (q : XiZeroCopy) (branch b : Bool) (a : ℂ)
    (X k : ℝ) (phi : Event → ℂ) (p r : Event) : ℂ :=
  timeReducedCoefficient (physicalRate q b) a p.1 p.2 * parameter q branch *
    (angularDirichletKernel q branch (r.1-p.1) r.2 p.2 X k +
      D4BMNativeCircle.nativeDirichletCausalKernel q (r.1-p.1) r.2 p.2 X k) /
      (Real.cosh r.2 : ℂ)^(2 : ℕ) * phi r

def retardedCoupledBulkAt (q : XiZeroCopy) (branch b : Bool) (a : ℂ)
    (X k : ℝ) (phi : Event → ℂ) (p : Event) : ℂ :=
  ∫ r : Event, retardedCoupledBulkDensity q branch b a X k phi p r

/-- The actual infinite-source retarded response has the full angular source
vertex and the undropped full-plus-native bulk action. -/
theorem fullRetardedResponse_weak_with_native (q : XiZeroCopy) (branch b : Bool)
    (a : ℂ) (X k : ℝ) (phi : Event → ℂ)
    (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi) :
    (∫ r : Event, fullRetardedResponse q branch b a r.1 r.2 X k * eventWave phi r) =
      ∫ p : Event, timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
          (fullAngularField q branch ![X, Real.exp k] *
            (phi p - phi (p.1,-p.2))) +
        retardedCoupledBulkAt q branch b a X k phi p ∂eventMeasure := by
  obtain ⟨hwcont,hwcompact⟩ := eventWave_continuous_compact hp hc
  have hi := retardedTestDensity_integrable q branch b a X k
    (eventWave phi) hwcont hwcompact
  rw [fullRetardedResponse_test_fubini q branch b a X k
    (eventWave phi) hwcont hwcompact]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with p hfull
  have hres : Integrable (fun r : Event =>
      timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
        futureResidual q branch p.1 p.2 X k phi r) :=
    (futureResidual_integrable q branch p.1 p.2 X k phi hp hc).const_mul _
  have hpoint (r : Event) :
      retardedTestDensity q branch b a X k (eventWave phi) (p,r) =
        timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
          futureResidual q branch p.1 p.2 X k phi r +
        retardedCoupledBulkDensity q branch b a X k phi p r := by
    rw [futureResidual_kernel q branch p.1 p.2 X k phi hp r]
    dsimp only [retardedTestDensity, retardedCoupledBulkDensity]
    ring
  have hbulk : Integrable (retardedCoupledBulkDensity q branch b a X k phi p) := by
    apply (hfull.sub hres).congr
    filter_upwards with r
    simp only [Pi.sub_apply]
    linear_combination (hpoint r)
  change timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
      (∫ r : Event, angularDirichletKernel q branch (r.1-p.1) r.2 p.2 X k *
        eventWave phi r) = _
  rw [← integral_const_mul]
  calc
    (∫ r : Event, timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
        (angularDirichletKernel q branch (r.1-p.1) r.2 p.2 X k *
          eventWave phi r)) =
      ∫ r : Event, timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
          futureResidual q branch p.1 p.2 X k phi r +
        retardedCoupledBulkDensity q branch b a X k phi p r := by
          apply integral_congr_ae
          filter_upwards with r
          rw [← hpoint r]
          dsimp only [retardedTestDensity]
          ring
    _ = (∫ r : Event, timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
          futureResidual q branch p.1 p.2 X k phi r) +
        retardedCoupledBulkAt q branch b a X k phi p := by
          rw [integral_add hres hbulk]
          rfl
    _ = _ := by
      rw [integral_const_mul,
        futureResidual_integral q branch p.1 p.2 X k phi hp hc]

end
end RHTower.D4BMPWRetardedWeakNative
