import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFutureSeedHorizonCap
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFuturePulseAdmission
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGeneralTemporalTransposition

/-!
Exact future reconstruction of the original source. A measure-theoretic null
coordinate change retains both causal cones, the reflected image and the area
Jacobian. The original outgoing-cut source integral is thereby identified with
the finite Green action. Its two independently admitted limits give
`kappa * A_Q + Seed = A_P + CSeed`, with the previously defined horizon cap.
This scalar identity does not assert metric regularity or noncompact QNM admission.
-/
open Set Filter Topology MeasureTheory
open scoped ENNReal ContDiff
namespace RHTower.D4BMFutureSourceBridge
open D4BMJointSource D4BMModularCore D4BMHorizon D4BMNativeCircle D4BMCausalKernel
open D4BMGlobalAngularResponse D4BMFullAngularCircle D4BMFullAngularReconstruction
open D4BMGeneralTemporalTransposition D4BMFutureSeedGreen D4BMFutureSeedHorizon
noncomputable section
set_option autoImplicit false

private abbrev Event := ℝ × ℝ

private def nullChart (tau : ℝ) : Event ≃ₜ Event where
  toFun z := ((z.1+z.2)/2-tau,(z.1-z.2)/2)
  invFun z := (tau+z.1+z.2,tau+z.1-z.2)
  left_inv z := by ext <;> dsimp <;> ring
  right_inv z := by ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem nullChart_volume (tau : ℝ) :
    Measure.map (nullChart tau) volume = (2:ℝ≥0∞) • (volume : Measure Event) := by
  let N : Event → Event := fun p => (-p.1,p.2)
  have hn : MeasurePreserving N (volume : Measure Event) volume := by
    rw [Measure.volume_eq_prod]
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id volume)
  have he : (nullChart tau : Event → Event)=N ∘ pastVertex tau 0 := by
    funext z
    change ((z.1+z.2)/2-tau,(z.1-z.2)/2)=(-(tau-(z.1+z.2)/2),0+(z.1-z.2)/2)
    ext <;> ring
  rw [he,← Measure.map_map hn.measurable (by unfold pastVertex; fun_prop),pastVertex_volume,
    Measure.map_smul,hn.map_eq]

private theorem integral_nullChart (tau : ℝ) (F : Event → ℂ) :
    (∫ z : Event, F (nullChart tau z))=2*(∫ z : Event,F z) := by
  have h := (nullChart tau).toMeasurableEquiv.measurableEmbedding.integral_map F (μ := volume)
  change (∫ z : Event,F z ∂Measure.map (nullChart tau) volume)=∫ z : Event,F (nullChart tau z) at h
  rw [nullChart_volume,integral_smul_measure] at h
  change (2:ℝ) • (∫ z : Event,F z)=∫ z : Event,F (nullChart tau z) at h
  simpa only [Complex.real_smul,Complex.ofReal_ofNat] using h.symm

private def nullRegion (p r L : ℝ) : Set Event :=
  {z | p ≤ z.1 ∧ r ≤ z.2 ∧ z.1 ≤ z.2 ∧ z.2 ≤ L}

private theorem nullRegion_measurable (p r L : ℝ) : MeasurableSet (nullRegion p r L) := by
  exact (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_const measurable_snd).inter
      ((measurableSet_le measurable_fst measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const)))

private theorem nullRegion_box (p r L : ℝ) :
    nullRegion p r L=(Icc p L ×ˢ Icc r L) ∩ {z : Event | z.1 ≤ z.2} := by
  ext z
  change (p ≤ z.1 ∧ r ≤ z.2 ∧ z.1 ≤ z.2 ∧ z.2 ≤ L) ↔
    ((p ≤ z.1 ∧ z.1 ≤ L) ∧ (r ≤ z.2 ∧ z.2 ≤ L)) ∧ z.1 ≤ z.2
  constructor
  · rintro ⟨hp,hr,hv,hL⟩
    exact ⟨⟨⟨hp,hv.trans hL⟩,hr,hL⟩,hv⟩
  · rintro ⟨⟨⟨hp,_⟩,hr,hL⟩,hv⟩
    exact ⟨hp,hr,hv,hL⟩

private theorem nullRegion_integral (F : Event → ℂ) (hF : Continuous F)
    (p r L : ℝ) (hpr : p ≤ r) (hrL : r ≤ L) :
    (∫ z in nullRegion p r L,F z)=
      (∫ v in p..r,∫ w in r..L,F (v,w))+(∫ v in r..L,∫ w in v..L,F (v,w)) := by
  let G : Event → ℂ := {z : Event | z.1 ≤ z.2}.indicator F
  have hs : MeasurableSet {z : Event | z.1 ≤ z.2} := measurableSet_le measurable_fst measurable_snd
  have hG : IntegrableOn G (Icc p L ×ˢ Icc r L) :=
    (hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).indicator hs
  let J : ℝ → ℂ := fun v => ∫ w in Icc r L,G (v,w)
  have hJ : IntegrableOn J (Icc p L) := by
    rw [IntegrableOn,Measure.volume_eq_prod,← Measure.prod_restrict] at hG
    exact hG.integral_prod_left
  have hprJ : IntervalIntegrable J volume p r :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hpr).mpr
      (hJ.mono_set (Icc_subset_Icc le_rfl hrL))
  have hrLJ : IntervalIntegrable J volume r L :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hrL).mpr
      (hJ.mono_set (Icc_subset_Icc hpr le_rfl))
  have hJval (v : ℝ) : J v=∫ w in Icc (max r v) L,F (v,w) := by
    have he : (fun w => G (v,w))=(Ici v).indicator (fun w => F (v,w)) := by
      funext w
      simp only [G,Set.indicator,mem_setOf_eq,mem_Ici]
      rfl
    have hset : Icc r L ∩ Ici v=Icc (max r v) L := by
      ext w
      simp only [mem_inter_iff,mem_Icc,mem_Ici,max_le_iff]
      tauto
    dsimp only [J]
    rw [he,setIntegral_indicator measurableSet_Ici,hset]
  calc
    _ = ∫ z in Icc p L ×ˢ Icc r L,G z := by
      rw [nullRegion_box,← setIntegral_indicator hs]
    _ = ∫ v in Icc p L,J v := by
      rw [Measure.volume_eq_prod] at hG ⊢
      exact setIntegral_prod _ hG
    _ = ∫ v in p..L,J v := by
      rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le (hpr.trans hrL)]
    _ = (∫ v in p..r,J v)+(∫ v in r..L,J v) :=
      (intervalIntegral.integral_add_adjacent_intervals hprJ hrLJ).symm
    _ = _ := by
      congr 1
      · apply intervalIntegral.integral_congr
        intro v hv
        dsimp only
        have hv' : v ∈ Icc p r := by simpa [uIcc_of_le hpr] using hv
        rw [hJval,max_eq_left hv'.2,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hrL]
      · apply intervalIntegral.integral_congr
        intro v hv
        dsimp only
        have hv' : v ∈ Icc r L := by simpa [uIcc_of_le hrL] using hv
        rw [hJval,max_eq_right hv'.1,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hv'.2]

private def closedFutureRegion (tau L : ℝ) : Set Event :=
  (Ici 0 ×ˢ Iic 0) ∩ {z | tau+z.1-z.2 ≤ L}

private theorem closedFutureRegion_measurable (tau L : ℝ) :
    MeasurableSet (closedFutureRegion tau L) :=
  (measurableSet_Ici.prod measurableSet_Iic).inter
    (measurableSet_le (by fun_prop) measurable_const)

private theorem futureRegion_ae_closed (tau L : ℝ) :
    D4BMFuturePulseAdmission.futureRegion tau L =ᵐ[volume] closedFutureRegion tau L := by
  have h : (Ioi (0:ℝ) ×ˢ Iio (0:ℝ) : Set Event)=ᵐ[volume] (Ici 0 ×ˢ Iic 0) := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioi_ae_eq_Ici Iio_ae_eq_Iic
  exact h.inter (Filter.EventuallyEq.refl _ _)

private theorem null_cone_region (p r L : ℝ) (hpr : p ≤ r) (image : Bool) (z : Event) :
    (nullChart ((p+r)/2) z ∈ closedFutureRegion ((p+r)/2) L ∧
      |(p-r)/2-(if image then -(nullChart ((p+r)/2) z).2 else (nullChart ((p+r)/2) z).2)| ≤
        (nullChart ((p+r)/2) z).1) ↔ z ∈ nullRegion (if image then r else p) r L := by
  change (((0 ≤ (z.1+z.2)/2-(p+r)/2 ∧ (z.1-z.2)/2 ≤ 0) ∧
    (p+r)/2+((z.1+z.2)/2-(p+r)/2)-(z.1-z.2)/2 ≤ L) ∧
    |(p-r)/2-(if image then -((z.1-z.2)/2) else (z.1-z.2)/2)| ≤ (z.1+z.2)/2-(p+r)/2) ↔
      (if image then r else p) ≤ z.1 ∧ r ≤ z.2 ∧ z.1 ≤ z.2 ∧ z.2 ≤ L
  cases image <;> simp only [Bool.false_eq_true,if_false,if_true,abs_le]
  all_goals
    constructor
    · rintro ⟨⟨⟨h0,hy⟩,hL⟩,hlo,hhi⟩
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
    · rintro ⟨hp,hr,hvw,hL⟩
      exact ⟨⟨⟨by linarith,by linarith⟩,by linarith⟩,by linarith,by linarith⟩

private def gated (F : Event → ℂ) (p r : ℝ) (image : Bool) (z : Event) : ℂ :=
  if |(p-r)/2-(if image then -z.2 else z.2)| ≤ z.1 then F z else 0

private theorem gated_chart (F : Event → ℂ) (p r L : ℝ) (hpr : p ≤ r) (image : Bool) :
    (fun z => (closedFutureRegion ((p+r)/2) L).indicator (gated F p r image) (nullChart ((p+r)/2) z))=
      (nullRegion (if image then r else p) r L).indicator (fun z => F (nullChart ((p+r)/2) z)) := by
  classical
  funext z
  by_cases hR : nullChart ((p+r)/2) z ∈ closedFutureRegion ((p+r)/2) L
  · rw [indicator_of_mem hR]
    by_cases hC : |(p-r)/2-(if image then -(nullChart ((p+r)/2) z).2 else
        (nullChart ((p+r)/2) z).2)| ≤ (nullChart ((p+r)/2) z).1
    · rw [gated,if_pos hC,indicator_of_mem ((null_cone_region p r L hpr image z).mp ⟨hR,hC⟩)]
    · rw [gated,if_neg hC,indicator_of_notMem (fun hz =>
        hC ((null_cone_region p r L hpr image z).mpr hz).2)]
  · rw [indicator_of_notMem hR,indicator_of_notMem (fun hz =>
      hR ((null_cone_region p r L hpr image z).mpr hz).1)]

private theorem integrable_nullChart (tau : ℝ) (F : Event → ℂ) :
    Integrable (fun z => F (nullChart tau z)) ↔ Integrable F := by
  have h := (nullChart tau).toMeasurableEquiv.measurableEmbedding.integrable_map_iff
    (g := F) (μ := volume)
  change Integrable F (Measure.map (nullChart tau) volume) ↔ Integrable (fun z => F (nullChart tau z)) at h
  rw [nullChart_volume,integrable_smul_measure (by norm_num) (by norm_num)] at h
  exact h.symm

private theorem cone_integrable (F : Event → ℂ) (hF : Continuous F) (p r L : ℝ)
    (hpr : p ≤ r) (image : Bool) :
    IntegrableOn (gated F p r image) (D4BMFuturePulseAdmission.futureRegion ((p+r)/2) L) := by
  rw [IntegrableOn,Measure.restrict_congr_set (futureRegion_ae_closed ((p+r)/2) L)]
  apply (integrable_indicator_iff (closedFutureRegion_measurable ((p+r)/2) L)).mp
  apply (integrable_nullChart ((p+r)/2) _).mp
  rw [gated_chart F p r L hpr image]
  have hFc : Continuous (fun z => F (nullChart ((p+r)/2) z)) :=
    hF.comp (nullChart ((p+r)/2)).continuous
  have hi : IntegrableOn (fun z => F (nullChart ((p+r)/2) z))
      (Icc (if image then r else p) L ×ˢ Icc r L) := hFc.continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (if image then r else p) L ×ˢ Icc r L))
  have hs : nullRegion (if image then r else p) r L ⊆ Icc (if image then r else p) L ×ˢ Icc r L := by
    rw [nullRegion_box]
    exact inter_subset_left
  exact (hi.mono_set hs).integrable_indicator (nullRegion_measurable _ _ _)

private theorem cone_integral (F : Event → ℂ) (hF : Continuous F) (p r L : ℝ)
    (hpr : p ≤ r) (hrL : r ≤ L) (image : Bool) :
    (∫ z in D4BMFuturePulseAdmission.futureRegion ((p+r)/2) L,gated F p r image z)=
      (∫ v in (if image then r else p)..r,∫ w in r..L,F (nullChart ((p+r)/2) (v,w))/2)+
        (∫ v in r..L,∫ w in v..L,F (nullChart ((p+r)/2) (v,w))/2) := by
  have ht := integral_nullChart ((p+r)/2)
    ((closedFutureRegion ((p+r)/2) L).indicator (gated F p r image))
  rw [gated_chart F p r L hpr image,integral_indicator (nullRegion_measurable _ _ _),
    integral_indicator (closedFutureRegion_measurable _ _)] at ht
  have har : (if image then r else p) ≤ r := by cases image <;> simp [hpr]
  rw [nullRegion_integral (fun z => F (nullChart ((p+r)/2) z))
    (hF.comp (nullChart ((p+r)/2)).continuous) _ _ _ har hrL] at ht
  rw [setIntegral_congr_set (futureRegion_ae_closed ((p+r)/2) L)]
  simp_rw [intervalIntegral.integral_div]
  linear_combination -ht/2


/-- A continuous source restricted to either finite original future cone is absolutely admitted. -/
theorem future_cone_cut_integrable (F : ℝ × ℝ → ℂ) (hF : Continuous F)
    (p r L : ℝ) (hpr : p ≤ r) (image : Bool) :
    IntegrableOn (fun z : ℝ × ℝ =>
      if |(p-r)/2-(if image then -z.2 else z.2)| ≤ z.1 then F z else 0)
      (D4BMFuturePulseAdmission.futureRegion ((p+r)/2) L) :=
  cone_integrable F hF p r L hpr image

/-- Exact finite future cone coordinates for an arbitrary continuous original density. -/
theorem future_cone_cut_coordinates (F : ℝ × ℝ → ℂ) (hF : Continuous F)
    (p r L : ℝ) (hpr : p ≤ r) (hrL : r ≤ L) (image : Bool) :
    (∫ z in D4BMFuturePulseAdmission.futureRegion ((p+r)/2) L,
      if |(p-r)/2-(if image then -z.2 else z.2)| ≤ z.1 then F z else 0)=
    (∫ v in (if image then r else p)..r, ∫ w in r..L,
      F ((v+w)/2-(p+r)/2,(v-w)/2)/2)+
    (∫ v in r..L, ∫ w in v..L,F ((v+w)/2-(p+r)/2,(v-w)/2)/2) :=
  cone_integral F hF p r L hpr hrL image

private def balancedSource (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (t y : ℝ) (z : Point) : ℂ :=
  fullSourceOnsetPulse q branch amp t y z-
    parameter q branch*timeReducedCoefficient (physicalRate q branch) amp t y*fullSquarePotential q z

private theorem balancedSource_eq (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    balancedSource q branch amp=(fun t y z => fullSourceOnsetPulse q branch amp t y z-
      parameter q branch*timeReducedCoefficient (physicalRate q branch) amp t y*fullSquarePotential q z) := rfl

private def balanceCircle (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (t y d X k : ℝ) : ℂ :=
  onsetAngularMean q branch amp t y d X k-
    parameter q branch*timeReducedCoefficient (physicalRate q branch) amp t y*mean q d X k

private theorem circle_continuous (f : Point → ℂ)
    (hf : ∀ z, 0 < z 1 → ContinuousAt f z) (d X k : ℝ) :
    Continuous (fun theta => f (logCircle d theta X k)) := by
  have hc : Continuous (fun theta : ℝ => logCircle d theta X k) := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp [logCircle,circle,offset,height,denominator]
    all_goals fun_prop (disch := intro theta; exact (denominator_pos d theta).ne')
  exact continuous_iff_continuousAt.mpr (fun theta =>
    (hf _ (mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _)))).comp hc.continuousAt)

private theorem average_sub {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    average (fun theta => f theta-g theta)=average f-average g := by
  dsimp [D4BMNativeCircle.average]
  rw [integral_sub (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]
  ring

private theorem average_const_mul (c : ℂ) (f : ℝ → ℂ) :
    average (fun theta => c*f theta)=c*average f := by
  dsimp [D4BMNativeCircle.average]
  rw [integral_const_mul]
  ring

private theorem balanceCircle_average (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (t y d X k : ℝ) :
    average (fun theta => balancedSource q branch amp t y (logCircle d theta X k))=
      balanceCircle q branch amp t y d X k := by
  have hB := circle_continuous (fullAngularField q branch)
    (fun z hz => (fullAngularField_smooth q branch z hz).continuousAt) d X k
  have hQ := circle_continuous (fullSquarePotential q)
    (fun z hz => (fullSquarePotential_smooth q z hz 0).continuousAt) d X k
  have hP : Continuous (fun theta => fullSourceOnsetPulse q branch amp t y (logCircle d theta X k)) := by
    simp_rw [fullSourceOnsetPulse_transition]
    fun_prop
  dsimp only [balancedSource]
  rw [average_sub hP (hQ.const_mul _),average_const_mul]
  rfl

private def closedArm (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau x X k : ℝ)
    (image : Bool) (z : Event) : ℂ :=
  balanceCircle q branch amp (tau+z.1) z.2
    (Real.arcosh (max 1 (invariant z.1 x (if image then -z.2 else z.2)))) X k/2

private theorem closedArm_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (tau x X k : ℝ) (image : Bool) : Continuous (closedArm q branch amp tau x X k image) := by
  have hseed : Continuous (sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch)) :=
    continuous_iff_continuousAt.mpr (fun y => (sourceSeedFieldFirst_hasDerivAt _ _ _ _ _ y).continuousAt)
  have hlift : Continuous (radialLiftFirst (physicalRate q branch) 0 amp 1) :=
    continuous_iff_continuousAt.mpr (fun y => (radialLiftFirst_hasDerivAt _ _ _ _ y).continuousAt)
  have hd : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 2)).differentiable_deriv_two.continuous
  have h0 : Continuous (fun z : Event => onsetResponseCoefficient q branch amp (tau+z.1) z.2) := by
    dsimp only [onsetResponseCoefficient]
    fun_prop
  have h1 : Continuous (fun z : Event => onsetSourceCoefficient q branch amp (tau+z.1) z.2) := by
    dsimp only [onsetSourceCoefficient]
    fun_prop
  have hS : Continuous (fun z : Event => timeReducedCoefficient (physicalRate q branch) amp (tau+z.1) z.2) :=
    (timeReducedCoefficient_joint_continuous _ _).comp
      (show Continuous (fun z : Event => (tau+z.1,z.2)) by fun_prop)
  let Y : Event → ℝ := fun z => if image then -z.2 else z.2
  have hY : Continuous Y := by
    cases image <;> simp only [Y,Bool.false_eq_true,if_false,if_true] <;> fun_prop
  have hI : Continuous (fun z : Event => invariant z.1 x (Y z)) := by
    unfold invariant
    exact (Real.continuous_cosh.comp continuous_fst |>.add
      ((Real.continuous_sinh.comp hY).const_mul (Real.sinh x))).div
      ((Real.continuous_cosh.comp hY).const_mul (Real.cosh x))
      (fun z => mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne')
  have hR : Continuous (fun z : Event => Real.arcosh (max 1 (invariant z.1 x (Y z)))) :=
    Real.continuousOn_arcosh.comp_continuous (continuous_const.max hI)
      (fun z => show 1 ≤ max 1 (invariant z.1 x (Y z)) from le_max_left _ _)
  have hM := (angularMean_smooth q branch X k).continuous.comp hR
  have hN := (mean_radial_smooth q X k).continuous.comp hR
  have he : closedArm q branch amp tau x X k image = fun z : Event =>
      (onsetResponseCoefficient q branch amp (tau+z.1) z.2*
        angularMean q branch (Real.arcosh (max 1 (invariant z.1 x (Y z)))) X k+
       onsetSourceCoefficient q branch amp (tau+z.1) z.2*
        mean q (Real.arcosh (max 1 (invariant z.1 x (Y z)))) X k-
       parameter q branch*timeReducedCoefficient (physicalRate q branch) amp (tau+z.1) z.2*
        mean q (Real.arcosh (max 1 (invariant z.1 x (Y z)))) X k)/2 := by
    funext z
    exact congrArg (fun c : ℂ => (c-_)/2) (onsetAngularMean_eq q branch amp (tau+z.1) z.2 _ X k)
  rw [he]
  exact (((h0.mul hM).add (h1.mul hN)).sub ((hS.const_mul _).mul hN)).div_const 2

private theorem closedArm_on_cone (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (tau x X k : ℝ) (image : Bool) (z : Event)
    (hc : |x-(if image then -z.2 else z.2)| ≤ z.1) :
    closedArm q branch amp tau x X k image z=
      balanceCircle q branch amp (tau+z.1) z.2
        (Real.arcosh (invariant z.1 x (if image then -z.2 else z.2))) X k/2 := by
  rw [closedArm,max_eq_right (invariant_causal ⟨z.1,x,_,hc⟩)]

private theorem gated_closedArm (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r X k : ℝ) (image : Bool) (z : Event) :
    gated (closedArm q branch amp ((p+r)/2) ((p-r)/2) X k image) p r image z=
      ((if |(p-r)/2-(if image then -z.2 else z.2)| ≤ z.1 then
        onsetAngularMean q branch amp ((p+r)/2+z.1) z.2
          (Real.arcosh (invariant z.1 ((p-r)/2) (if image then -z.2 else z.2))) X k else 0)-
       parameter q branch*timeReducedCoefficient (physicalRate q branch) amp ((p+r)/2+z.1) z.2*
        (if |(p-r)/2-(if image then -z.2 else z.2)| ≤ z.1 then
          nativeRiemannKernel q z.1 ((p-r)/2) (if image then -z.2 else z.2) X k else 0))/2 := by
  by_cases hc : |(p-r)/2-(if image then -z.2 else z.2)| ≤ z.1
  · rw [gated,if_pos hc,closedArm_on_cone q branch amp _ _ X k image z hc]
    simp only [balanceCircle,if_pos hc,nativeRiemannKernel,angularKernel]
  · simp only [gated,if_neg hc,mul_zero,sub_zero,zero_div]

private theorem sourceBalance_gates (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r X k : ℝ) (z : Event) :
    D4BMFuturePulseAdmission.density q branch amp ((p+r)/2) ((p-r)/2) X k z-
      parameter q branch*D4BMFullSourceAdvanced.density q branch amp ((p+r)/2) ((p-r)/2) X k z=
    gated (closedArm q branch amp ((p+r)/2) ((p-r)/2) X k false) p r false z-
      gated (closedArm q branch amp ((p+r)/2) ((p-r)/2) X k true) p r true z := by
  rw [gated_closedArm,gated_closedArm]
  dsimp only [D4BMFuturePulseAdmission.density,D4BMFullSourceAdvanced.density,
    onsetDirichletKernel,nativeDirichletCausalKernel]
  simp only [Bool.false_eq_true,if_false,if_true,sub_neg_eq_add]
  ring

private def nullDensity (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r X k : ℝ) (image : Bool) (v w : ℝ) : ℂ :=
  average (fun theta => balancedSource q branch amp ((v+w)/2) ((v-w)/2)
    (logCircle (Real.arcosh (invariant ((v+w-p-r)/2) ((p-r)/2)
      (if image then -((v-w)/2) else (v-w)/2))) theta X k))/4

private theorem closedArm_chart (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r X k : ℝ) (hpr : p ≤ r) (image : Bool) (v w : ℝ)
    (hz : (v,w) ∈ nullRegion (if image then r else p) r w) :
    closedArm q branch amp ((p+r)/2) ((p-r)/2) X k image (nullChart ((p+r)/2) (v,w))/2=
      nullDensity q branch amp p r X k image v w := by
  have hc := ((null_cone_region p r w hpr image (v,w)).mpr hz).2
  rw [closedArm_on_cone q branch amp _ _ X k image _ hc]
  change balanceCircle q branch amp ((p+r)/2+((v+w)/2-(p+r)/2)) ((v-w)/2)
    (Real.arcosh (invariant ((v+w)/2-(p+r)/2) ((p-r)/2)
      (if image then -((v-w)/2) else (v-w)/2))) X k/2/2=_
  rw [show (p+r)/2+((v+w)/2-(p+r)/2)=(v+w)/2 by ring,
    show (v+w)/2-(p+r)/2=(v+w-p-r)/2 by ring,← balanceCircle_average]
  dsimp only [nullDensity]
  ring

private def nullAction (F : ℝ → ℝ → ℂ) (p r L : ℝ) : ℂ :=
  (∫ v in p..r,∫ w in r..L,F v w)+(∫ v in r..L,∫ w in v..L,F v w)

private theorem nullAction_congr {F G : ℝ → ℝ → ℂ} {p r L : ℝ}
    (hpr : p ≤ r) (hrL : r ≤ L)
    (he : ∀ v w, p ≤ v → r ≤ w → v ≤ w → w ≤ L → F v w=G v w) :
    nullAction F p r L=nullAction G p r L := by
  unfold nullAction
  congr 1
  · apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc p r := by simpa [uIcc_of_le hpr] using hv
    apply intervalIntegral.integral_congr
    intro w hw
    have hw' : w ∈ Icc r L := by simpa [uIcc_of_le hrL] using hw
    exact he v w hv'.1 hw'.1 (hv'.2.trans hw'.1) hw'.2
  · apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc r L := by simpa [uIcc_of_le hrL] using hv
    apply intervalIntegral.integral_congr
    intro w hw
    have hw' : w ∈ Icc v L := by simpa [uIcc_of_le hv'.2] using hw
    exact he v w (hpr.trans hv'.1) (hv'.1.trans hw'.1) hw'.1 hw'.2

private theorem sourceBalance_cut_eq_raw (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p r L X k : ℝ) (hpr : p ≤ r) (hrL : r ≤ L) :
    (∫ z in D4BMFuturePulseAdmission.futureRegion ((p+r)/2) L,
      D4BMFuturePulseAdmission.density q branch amp ((p+r)/2) ((p-r)/2) X k z-
        parameter q branch*D4BMFullSourceAdvanced.density q branch amp ((p+r)/2) ((p-r)/2) X k z)=
      finiteFutureAction (balancedSource q branch amp) p r L X k := by
  let F := closedArm q branch amp ((p+r)/2) ((p-r)/2) X k
  have hF (b : Bool) : Continuous (F b) := closedArm_continuous q branch amp _ _ X k b
  calc
    _ = ∫ z in D4BMFuturePulseAdmission.futureRegion ((p+r)/2) L,
        gated (F false) p r false z-gated (F true) p r true z := by
      apply integral_congr_ae
      exact Eventually.of_forall (sourceBalance_gates q branch amp p r X k)
    _ = (∫ z in D4BMFuturePulseAdmission.futureRegion ((p+r)/2) L,gated (F false) p r false z)-
        ∫ z in D4BMFuturePulseAdmission.futureRegion ((p+r)/2) L,gated (F true) p r true z :=
      integral_sub (cone_integrable (F false) (hF false) p r L hpr false)
        (cone_integrable (F true) (hF true) p r L hpr true)
    _ = nullAction (fun v w => F false (nullChart ((p+r)/2) (v,w))/2) p r L-
        nullAction (fun v w => F true (nullChart ((p+r)/2) (v,w))/2) r r L := by
      rw [cone_integral (F false) (hF false) p r L hpr hrL false,
        cone_integral (F true) (hF true) p r L hpr hrL true]
      rfl
    _ = _ := by
      change nullAction _ p r L-nullAction _ r r L=
        nullAction (nullDensity q branch amp p r X k false) p r L-
          nullAction (nullDensity q branch amp p r X k true) r r L
      congr 1
      · apply nullAction_congr hpr hrL
        intro v w hv hw hvw _
        exact closedArm_chart q branch amp p r X k hpr false v w ⟨hv,hw,hvw,le_rfl⟩
      · apply nullAction_congr le_rfl hrL
        intro v w hv hw hvw _
        exact closedArm_chart q branch amp p r X k hpr true v w ⟨hv,hw,hvw,le_rfl⟩


/-- The original outgoing-cut source integral equals the finite null Green action,
with the unchanged direct/image supports and exact Jacobian. -/
theorem finite_source_balance_coordinates (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p : ℝ) (width span : NNReal) (X k : ℝ) :
    (∫ z in D4BMFuturePulseAdmission.futureRegion ((2*p+width)/2) (p+width+span),
      D4BMFuturePulseAdmission.density q branch amp ((2*p+width)/2) (-(width:ℝ)/2) X k z-
        parameter q branch*D4BMFullSourceAdvanced.density q branch amp ((2*p+width)/2) (-(width:ℝ)/2) X k z)=
      finiteFutureAction (fun t y z => fullSourceOnsetPulse q branch amp t y z-
        parameter q branch*timeReducedCoefficient (physicalRate q branch) amp t y*fullSquarePotential q z)
        p (p+width) (p+width+span) X k := by
  have h := sourceBalance_cut_eq_raw q branch amp p (p+width) (p+width+span) X k
    (by linarith [width.coe_nonneg]) (by linarith [span.coe_nonneg])
  have ht : (p+(p+width))/2=(2*p+width)/2 := by ring
  have hx : (p-(p+width))/2= -(width:ℝ)/2 := by ring
  rw [balancedSource_eq,ht,hx] at h
  exact h

private theorem future_source_balance_null (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (p : ℝ) (width : NNReal) (X k : ℝ) :
    parameter q branch*D4BMFullSourceAdvanced.response q branch amp ((2*p+width)/2) (-(width:ℝ)/2) X k+
      timeAngularSeedField q branch amp ((2*p+width)/2) (-(width:ℝ)/2) ![X,Real.exp k]=
    D4BMFuturePulseAdmission.response q branch amp ((2*p+width)/2) (-(width:ℝ)/2) X k+
      seedCapField q branch amp ((2*p+width)/2) (-(width:ℝ)/2) X k := by
  have hA := D4BMFuturePulseAdmission.sourceBalance_limit q branch amp ((2*p+width)/2) (-(width:ℝ)/2) X k
  have hB := finite_source_balance_limit q branch amp p width X k
  have he : (fun L => ∫ z in D4BMFuturePulseAdmission.futureRegion ((2*p+width)/2) L,
      D4BMFuturePulseAdmission.density q branch amp ((2*p+width)/2) (-(width:ℝ)/2) X k z-
        parameter q branch*D4BMFullSourceAdvanced.density q branch amp ((2*p+width)/2) (-(width:ℝ)/2) X k z)
      =ᶠ[atTop] (fun L => finiteFutureAction (fun t y z => fullSourceOnsetPulse q branch amp t y z-
        parameter q branch*timeReducedCoefficient (physicalRate q branch) amp t y*fullSquarePotential q z)
          p (p+width) L X k) := by
    filter_upwards [eventually_ge_atTop (p+width)] with L hL
    have h := sourceBalance_cut_eq_raw q branch amp p (p+width) L X k
      (by linarith [width.coe_nonneg]) hL
    have ht : (p+(p+width))/2=(2*p+width)/2 := by ring
    have hx : (p-(p+width))/2= -(width:ℝ)/2 := by ring
    rw [balancedSource_eq,ht,hx] at h
    exact h
  have hu := tendsto_nhds_unique (Filter.Tendsto.congr' he hA) hB
  linear_combination -hu

/-- Exact reconstruction of the actual future source from the original seed,
unchanged fixed onset pulse and independently defined horizon cap. All integrals
and the limiting boundary term have been admitted from their original sources. -/
theorem future_source_balance (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (tau : ℝ) (depth : NNReal) (X k : ℝ) :
    parameter q branch*D4BMFullSourceAdvanced.response q branch amp tau (-(depth:ℝ)) X k+
      timeAngularSeedField q branch amp tau (-(depth:ℝ)) ![X,Real.exp k]=
    D4BMFuturePulseAdmission.response q branch amp tau (-(depth:ℝ)) X k+
      seedCapField q branch amp tau (-(depth:ℝ)) X k := by
  have h := future_source_balance_null q branch amp (tau-depth) (2*depth) X k
  have ht : (2*(tau-(depth:ℝ))+((2*depth:NNReal):ℝ))/2=tau := by push_cast; ring
  have hx : -((2*depth:NNReal):ℝ)/2= -(depth:ℝ) := by push_cast; ring
  rw [ht,hx] at h
  exact h

end
end RHTower.D4BMFutureSourceBridge
