import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompleteOriginalWeakSource
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalRetardedIdentity
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
The original retarded source-event integral equals the full native null field.
Odd reflection retains the Dirichlet image, while the original onset and causal
support restrict the null coordinates to their source rectangle. The exact area
Jacobian supplies the remaining factor one half.

The admitted causal source pairing consequently uses the original retarded field,
the corrected future field and its explicit cap term. The same retarded inverse
also inherits the original angular-seed and fixed-onset-pulse reconstruction.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace RHTower.D4BMOriginalCausalDifference
open D4BMJointSource D4BMModularCore D4BMHorizon D4BMNativeCircle D4BMCausalKernel
open D4BMNativeResponse D4BMGeneralTemporalTransposition D4BMFullSourceReciprocity
open D4BMFullSourceAdvanced D4BMOriginalCausalPotential D4BMCompleteOriginalWeakSource
open D4BMFutureHorizon D4BMOriginalRetardedIdentity
noncomputable section
set_option autoImplicit false

private def nullChart : Event ≃ₜ Event where
  toFun z := ((z.1+z.2)/2,(z.1-z.2)/2)
  invFun z := (z.1+z.2,z.1-z.2)
  left_inv z := by ext <;> dsimp <;> ring
  right_inv z := by ext <;> dsimp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem nullChart_apply (z : Event) : nullChart z=((z.1+z.2)/2,(z.1-z.2)/2) := rfl

private theorem nullChart_volume :
    Measure.map nullChart volume = (2:ℝ≥0∞) • (volume : Measure Event) := by
  let N : Event → Event := fun p => (-p.1,p.2)
  have hn : MeasurePreserving N (volume : Measure Event) volume := by
    rw [Measure.volume_eq_prod]
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id volume)
  have he : (nullChart : Event → Event)=N ∘ pastVertex 0 0 := by
    funext z
    rw [nullChart_apply]
    ext <;> dsimp only [N,Function.comp_def,pastVertex] <;> ring
  rw [he,← Measure.map_map hn.measurable (by unfold pastVertex; fun_prop),pastVertex_volume,
    Measure.map_smul,hn.map_eq]

private theorem integral_nullChart (F : Event → ℂ) :
    (∫ z : Event, F (nullChart z))=2*(∫ z : Event,F z) := by
  have h := nullChart.toMeasurableEquiv.measurableEmbedding.integral_map F (μ := volume)
  change (∫ z : Event,F z ∂Measure.map nullChart volume)=∫ z : Event,F (nullChart z) at h
  rw [nullChart_volume,integral_smul_measure] at h
  change (2:ℝ) • (∫ z : Event,F z)=∫ z : Event,F (nullChart z) at h
  simpa only [Complex.real_smul,Complex.ofReal_ofNat] using h.symm

private theorem integrable_nullChart (F : Event → ℂ) :
    Integrable (fun z : Event => F (nullChart z)) ↔ Integrable F := by
  have h := nullChart.toMeasurableEquiv.measurableEmbedding.integrable_map_iff
    (g := F) (μ := volume)
  change Integrable F (Measure.map nullChart volume) ↔ Integrable (fun z : Event => F (nullChart z)) at h
  rw [nullChart_volume,integrable_smul_measure (by norm_num) (by norm_num)] at h
  exact h.symm

private theorem odd_negative (s a : ℂ) (t y : ℝ) (hy : y ≤ 0) :
    oddSource s a t y=timeReducedCoefficient s a t y := by
  simp only [oddSource,min_eq_left hy,min_eq_right (neg_nonneg.mpr hy),source_boundary,sub_zero]

private theorem odd_neg (s a : ℂ) (t y : ℝ) :
    oddSource s a t (-y) = -oddSource s a t y := by
  simp only [oddSource,neg_neg,neg_sub]

private theorem odd_null_zero (s a : ℂ) (u v : ℝ) (h : u<0 ∨ v<0) :
    oddSource s a ((u+v)/2) ((u-v)/2)=0 := by
  rcases le_total u v with huv | hvu
  · rw [odd_negative s a _ _ (by linarith)]
    apply timeReducedCoefficient_zero_before_onset
    rcases h with h | h <;> linarith
  · have he : (u-v)/2 = -((v-u)/2) := by ring
    rw [he,odd_neg,odd_negative s a _ _ (by linarith)]
    have hz : timeReducedCoefficient s a ((u+v)/2) ((v-u)/2)=0 := by
      apply timeReducedCoefficient_zero_before_onset
      rcases h with h | h <;> linarith
    rw [hz,neg_zero]

private theorem odd_time_zero (s a : ℂ) (t y : ℝ) (ht : t ≤ 0) :
    oddSource s a t y=0 := by
  by_cases hy : y=0
  · simp only [hy,oddSource,neg_zero,sub_self]
  have h : t+y<0 ∨ t-y<0 := by
    rcases lt_or_gt_of_ne hy with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hz := odd_null_zero s a (t+y) (t-y) h
  rw [show (t+y+(t-y))/2=t by ring,show (t+y-(t-y))/2=y by ring] at hz
  exact hz

private theorem odd_continuous (s a : ℂ) :
    Continuous (fun z : Event => oddSource s a z.1 z.2) := by
  have h1 := (timeReducedCoefficient_joint_continuous s a).comp
    (show Continuous (fun z : Event => (z.1,min z.2 0)) by fun_prop)
  have h2 := (timeReducedCoefficient_joint_continuous s a).comp
    (show Continuous (fun z : Event => (z.1,min (-z.2) 0)) by fun_prop)
  exact h1.sub h2

private def closedKernel (q : XiZeroCopy) (t x X k : ℝ) (z : Event) : ℂ :=
  mean q (Real.arcosh (max 1 (invariant (t-z.1) x z.2))) X k

private theorem closedKernel_continuous (q : XiZeroCopy) (t x X k : ℝ) :
    Continuous (closedKernel q t x X k) := by
  have hi : Continuous (fun z : Event => invariant (t-z.1) x z.2) := by
    unfold invariant
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro z; exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
  have hd := Real.continuousOn_arcosh.comp_continuous (continuous_const.max hi)
    (fun z => show (1:ℝ) ≤ max 1 _ from le_max_left _ _)
  exact (mean_radial_smooth q X k).continuous.comp hd

private def oddCone (q : XiZeroCopy) (s a : ℂ) (t x X k : ℝ) (z : Event) : ℂ :=
  if |x-z.2| ≤ t-z.1 then closedKernel q t x X k z*oddSource s a z.1 z.2/2 else 0

private theorem null_cone (p r : ℝ) (z : Event) :
    |(p-r)/2-(nullChart z).2| ≤ (p+r)/2-(nullChart z).1 ↔ z.1 ≤ p ∧ z.2 ≤ r := by
  rw [nullChart_apply]
  simp only [abs_le]
  constructor
  · rintro ⟨h1,h2⟩
    constructor <;> linarith
  · rintro ⟨h1,h2⟩
    constructor <;> linarith

private def rectangleDensity (q : XiZeroCopy) (s a : ℂ) (p r X k : ℝ) (z : Event) : ℂ :=
  closedKernel q ((p+r)/2) ((p-r)/2) X k (nullChart z)*
    oddSource s a (nullChart z).1 (nullChart z).2/2

private theorem rectangleDensity_continuous (q : XiZeroCopy) (s a : ℂ) (p r X k : ℝ) :
    Continuous (rectangleDensity q s a p r X k) :=
  (((closedKernel_continuous q _ _ X k).comp nullChart.continuous).mul
    ((odd_continuous s a).comp nullChart.continuous)).div_const 2

private theorem oddCone_nullChart (q : XiZeroCopy) (s a : ℂ) (p r X k : ℝ) :
    (fun z : Event => oddCone q s a ((p+r)/2) ((p-r)/2) X k (nullChart z))=
      (Icc 0 p ×ˢ Icc 0 r).indicator (rectangleDensity q s a p r X k) := by
  classical
  funext z
  by_cases hc : z.1 ≤ p ∧ z.2 ≤ r
  · rw [oddCone,if_pos ((null_cone p r z).mpr hc)]
    by_cases hz : z ∈ Icc 0 p ×ˢ Icc 0 r
    · rw [Set.indicator_of_mem hz]
      rfl
    · rw [Set.indicator_of_notMem hz]
      have hn : z.1<0 ∨ z.2<0 := by
        by_contra h
        push Not at h
        exact hz ⟨⟨h.1,hc.1⟩,⟨h.2,hc.2⟩⟩
      have hs := odd_null_zero s a z.1 z.2 hn
      change closedKernel q _ _ X k (nullChart z)*oddSource s a ((z.1+z.2)/2) ((z.1-z.2)/2)/2=0
      rw [hs,mul_zero,zero_div]
  · rw [oddCone,if_neg (fun h => hc ((null_cone p r z).mp h))]
    rw [Set.indicator_of_notMem (fun hz => hc ⟨hz.1.2,hz.2.2⟩)]

private theorem oddCone_integrable (q : XiZeroCopy) (s a : ℂ) (p r X k : ℝ) :
    Integrable (oddCone q s a ((p+r)/2) ((p-r)/2) X k) := by
  apply (integrable_nullChart _).mp
  rw [oddCone_nullChart]
  exact ((rectangleDensity_continuous q s a p r X k).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).integrable_indicator (measurableSet_Icc.prod measurableSet_Icc)

private theorem closedKernel_native (q : XiZeroCopy) (t x X k : ℝ) (z : Event)
    (hc : |x-z.2| ≤ t-z.1) :
    closedKernel q t x X k z=nativeRiemannKernel q (t-z.1) x z.2 X k := by
  unfold closedKernel nativeRiemannKernel angularKernel
  rw [max_eq_right (invariant_causal ⟨_,_,_,hc⟩)]

private theorem oddCone_native (q : XiZeroCopy) (s a : ℂ) (t x X k : ℝ) (z : Event) :
    oddCone q s a t x X k z=
      (if |x-z.2| ≤ t-z.1 then nativeRiemannKernel q (t-z.1) x z.2 X k else 0)*
        oddSource s a z.1 z.2/2 := by
  by_cases hc : |x-z.2| ≤ t-z.1
  · rw [oddCone,if_pos hc,if_pos hc,closedKernel_native q t x X k z hc]
  · simp only [oddCone,if_neg hc,zero_mul,zero_div]

private theorem oddCone_reflection (q : XiZeroCopy) (br : Bool) (a : ℂ)
    (t x X k : ℝ) (z : Event) (hy : z.2 ≤ 0) :
    oddCone q (physicalRate q br) a t x X k z+
      oddCone q (physicalRate q br) a t x X k (z.1,-z.2)=
        directedSourceDensity q br a t x X k false z := by
  rw [oddCone_native,oddCone_native,odd_neg,odd_negative _ _ _ _ hy]
  simp only [directedSourceDensity,Bool.false_eq_true,if_false,
    nativeDirichletCausalKernel,sub_neg_eq_add]
  ring

private theorem integral_fold (F : Event → ℂ) (hi : Integrable F) :
    (∫ z : Event,F z)=∫ t : ℝ,∫ y in Iio (0:ℝ),F (t,y)+F (t,-y) := by
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod F hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with t ht
  have hn : Integrable (fun y : ℝ => F (t,-y)) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_of_integrable ht
  rw [integral_add ht.integrableOn hn.integrableOn]
  simp_rw [← integral_Iic_eq_integral_Iio]
  rw [integral_comp_neg_Iic (0:ℝ) (fun y => F (t,y)),neg_zero]
  exact (intervalIntegral.integral_Iic_add_Ioi ht.integrableOn ht.integrableOn).symm

private theorem radial_reflection_preserving :
    MeasurePreserving (fun z : Event => (z.1,-z.2)) volume volume := by
  rw [Measure.volume_eq_prod]
  exact (MeasurePreserving.id volume).prod (Measure.measurePreserving_neg (volume : Measure ℝ))

private theorem retarded_eq_oddCone (q : XiZeroCopy) (br : Bool) (a : ℂ) (p r X k : ℝ) :
    retardedResponse q br a ((p+r)/2) ((p-r)/2) X k=
      ∫ z : Event,oddCone q (physicalRate q br) a ((p+r)/2) ((p-r)/2) X k z := by
  let G := oddCone q (physicalRate q br) a ((p+r)/2) ((p-r)/2) X k
  have hi : Integrable G := oddCone_integrable q _ a p r X k
  have hn : Integrable (fun z : Event => G (z.1,-z.2)) :=
    radial_reflection_preserving.integrable_comp_of_integrable hi
  have hsum : Integrable (fun z : Event => G z+G (z.1,-z.2)) := hi.add hn
  rw [retardedResponse,eventMeasure,Measure.prod_restrict,← Measure.volume_eq_prod]
  calc
    (∫ z in Ioi (0:ℝ) ×ˢ Iio (0:ℝ), directedSourceDensity q br a ((p+r)/2) ((p-r)/2) X k false z)
        = ∫ z in Ioi (0:ℝ) ×ˢ Iio (0:ℝ), G z+G (z.1,-z.2) := by
      apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Iio)
      intro z hz
      exact (oddCone_reflection q br a _ _ X k z hz.2.le).symm
    _ = ∫ t in Ioi (0:ℝ),∫ y in Iio (0:ℝ),G (t,y)+G (t,-y) := by
      rw [Measure.volume_eq_prod] at hsum ⊢
      exact setIntegral_prod _ hsum.integrableOn
    _ = ∫ t : ℝ,∫ y in Iio (0:ℝ),G (t,y)+G (t,-y) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      have ht0 : t ≤ 0 := le_of_not_gt ht
      have hz (y : ℝ) : G (t,y)=0 := by
        dsimp only [G,oddCone]
        rw [odd_time_zero _ _ t y ht0]
        split_ifs <;> simp only [mul_zero,zero_div]
      simp only [hz,add_zero,integral_zero]
    _ = ∫ z : Event,G z := (integral_fold G hi).symm

private theorem oddCone_eq_native_response (q : XiZeroCopy) (s a : ℂ)
    (p r X k : ℝ) (hp : 0 ≤ p) (hr : 0 ≤ r) :
    (∫ z : Event,oddCone q s a ((p+r)/2) ((p-r)/2) X k z)=fullNullResponse q s a p r X k := by
  have ht := integral_nullChart (oddCone q s a ((p+r)/2) ((p-r)/2) X k)
  rw [oddCone_nullChart,integral_indicator (measurableSet_Icc.prod measurableSet_Icc)] at ht
  have hi : IntegrableOn (rectangleDensity q s a p r X k) (Icc 0 p ×ˢ Icc 0 r) :=
    (rectangleDensity_continuous q s a p r X k).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)
  have hbox : (∫ z in Icc (0:ℝ) p ×ˢ Icc (0:ℝ) r,rectangleDensity q s a p r X k z)=
      ∫ u in (0:ℝ)..p,∫ v in (0:ℝ)..r,rectangleDensity q s a p r X k (u,v) := by
    rw [Measure.volume_eq_prod] at hi ⊢
    rw [setIntegral_prod _ hi]
    simp_rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hr]
    rw [← intervalIntegral.integral_of_le hp]
  rw [hbox] at ht
  have he : (∫ u in (0:ℝ)..p,∫ v in (0:ℝ)..r,rectangleDensity q s a p r X k (u,v))=
      (∫ u in (0:ℝ)..p,∫ v in (0:ℝ)..r,
        nativeRiemannKernel q ((p+r-u-v)/2) ((p-r)/2) ((u-v)/2) X k*
          oddSource s a ((u+v)/2) ((u-v)/2))/2 := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ≤ p := (show u ∈ Icc 0 p by simpa only [uIcc_of_le hp] using hu).2
    dsimp only
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ≤ r := (show v ∈ Icc 0 r by simpa only [uIcc_of_le hr] using hv).2
    dsimp only
    rw [rectangleDensity,closedKernel_native q _ _ X k (nullChart (u,v))
      ((null_cone p r (u,v)).mpr ⟨hu',hv'⟩),nullChart_apply]
    dsimp only
    rw [show (p+r)/2-(u+v)/2=(p+r-u-v)/2 by ring]
  rw [he] at ht
  rw [fullNullResponse_native q s a hp hr X k]
  linear_combination -(1/2:ℂ)*ht

/-- The admitted original source-event inverse is exactly the original full native
retarded field. The source onset, Dirichlet image and null Jacobian are retained. -/
theorem retardedResponse_eq_fullNullResponse (q : XiZeroCopy) (br : Bool) (a : ℂ)
    (p r X k : ℝ) :
    retardedResponse q br a ((p+r)/2) ((p-r)/2) X k=
      fullNullResponse q (physicalRate q br) a p r X k := by
  rw [retarded_eq_oddCone]
  by_cases hp : 0 ≤ p
  · by_cases hr : 0 ≤ r
    · exact oddCone_eq_native_response q _ a p r X k hp hr
    · rw [fullNullResponse_nonpositive q _ a (Or.inr (le_of_not_ge hr)) X k]
      have ht := integral_nullChart (oddCone q (physicalRate q br) a ((p+r)/2) ((p-r)/2) X k)
      rw [oddCone_nullChart,Icc_eq_empty hr,prod_empty,Set.indicator_empty,integral_zero] at ht
      linear_combination -(1/2:ℂ)*ht
  · rw [fullNullResponse_nonpositive q _ a (Or.inl (le_of_not_ge hp)) X k]
    have ht := integral_nullChart (oddCone q (physicalRate q br) a ((p+r)/2) ((p-r)/2) X k)
    rw [oddCone_nullChart,Icc_eq_empty hp,empty_prod,Set.indicator_empty,integral_zero] at ht
    linear_combination -(1/2:ℂ)*ht

/-- The causal difference uses the same original retarded field as the actual
metric/current construction and retains the entire original cap correction. -/
theorem original_causal_difference (q : XiZeroCopy) (br : Bool) (a : ℂ)
    (p r X k : ℝ) :
    originalPotential q br a p r X k-
      correctedFutureField q br a (((p+r)/2,(p-r)/2),X+Complex.I*k)=
        retardedResponse q br a ((p+r)/2) ((p-r)/2) X k-
          response q br a ((p+r)/2) ((p-r)/2) X k+
            capBoundaryField q br a ((p+r)/2) ((p-r)/2) X k := by
  rw [retardedResponse_eq_fullNullResponse q br a p r X k]
  simp only [originalPotential,correctedFutureField,timeLiftField,timeRadialLift,nullLift,
    sourceProfile,Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,
    sub_zero,add_zero,zero_add]
  rw [show (p+r)/2+(p-r)/2=p by ring]
  ring

private theorem actual_difference_eq (q : XiZeroCopy) (br : Bool) (a : ℂ) (t x X k : ℝ) :
    originalPotential q br a (t+x) (t-x) X k-
      correctedFutureField q br a ((t,x),X+Complex.I*k)-capBoundaryField q br a t x X k=
        retardedResponse q br a t x X k-response q br a t x X k := by
  have h := original_causal_difference q br a (t+x) (t-x) X k
  rw [show (t+x+(t-x))/2=t by ring,show (t+x-(t-x))/2=x by ring] at h
  linear_combination h

/-- Absolute admission of the causal pairing expressed using the original retarded
field and corrected future field, including the cap term required by source reciprocity. -/
theorem original_field_pair_integrable (q : XiZeroCopy) (b c : Bool) (a d : ℂ) (X k : ℝ) :
    Integrable (fun p : Event => timeReducedCoefficient (physicalRate q b) a p.1 p.2*
      (originalPotential q c d (p.1+p.2) (p.1-p.2) X k-
        correctedFutureField q c d (p,X+Complex.I*k)-capBoundaryField q c d p.1 p.2 X k)) eventMeasure := by
  have hr : Integrable (fun p : Event => timeReducedCoefficient (physicalRate q b) a p.1 p.2*
      retardedResponse q c d p.1 p.2 X k) eventMeasure := by
    simpa only [mul_comm] using (source_response_pairings_integrable q c b d a X k).2
  have hf := (source_response_pairings_integrable q b c a d X k).1
  apply (hr.sub hf).congr
  exact ae_of_all _ (fun p => by
    dsimp only [Pi.sub_apply]
    rw [actual_difference_eq]
    ring)

/-- The admitted original causal source pairing is exactly the action of the
original retarded field minus corrected future field minus its cap contribution. -/
theorem causalSourcePair_original_fields (q : XiZeroCopy) (b c : Bool) (a d : ℂ) (X k : ℝ) :
    causalSourcePair q b c a d X k=
      ∫ p : Event, timeReducedCoefficient (physicalRate q b) a p.1 p.2*
        (originalPotential q c d (p.1+p.2) (p.1-p.2) X k-
          correctedFutureField q c d (p,X+Complex.I*k)-capBoundaryField q c d p.1 p.2 X k) ∂eventMeasure := by
  unfold causalSourcePair
  apply integral_congr_ae
  exact ae_of_all _ (fun p => by
    dsimp only
    rw [actual_difference_eq])

/-- The admitted retarded source-event inverse reduces to the explicit angular
seed and the original pulse supported in the fixed ingoing transition interval. -/
theorem retardedResponse_onset_pulse (q : XiZeroCopy) (br : Bool) (a : ℂ)
    (p width : NNReal) (X k : ℝ) :
    retardedResponse q br a ((2*p+width)/2) (-(width:ℝ)/2) X k=
      -timeAngularSeedField q br a ((2*p+width)/2) (-(width:ℝ)/2) ![X,Real.exp k]/
        D4BMGlobalAngularResponse.parameter q br+
      D4BMOnsetGreenReconstruction.retardedNullAction (fullSourceOnsetPulse q br a) p width X k/
        D4BMGlobalAngularResponse.parameter q br := by
  have h := originalPotential_onset_reconstruction q br a p width X k
  have hR := retardedResponse_eq_fullNullResponse q br a p (p+width) X k
  rw [show ((p:ℝ)+(p+width))/2=(2*p+width)/2 by ring,
    show ((p:ℝ)-(p+width))/2=-(width:ℝ)/2 by ring] at hR
  rw [hR]
  have hl : timeLiftField q br a ((2*p+width)/2) (-(width:ℝ)/2) ![X,Real.exp k]=
      nullLift (physicalRate q br) a p (p+width)*sourceProfile q X k := by
    dsimp only [timeLiftField,timeRadialLift,nullLift,sourceProfile]
    rw [show (2*(p:ℝ)+width)/2+ -(width:ℝ)/2=p by ring,
      show ((p:ℝ)-((p:ℝ)+width))/2=-(width:ℝ)/2 by ring]
  rw [hl,originalPotential] at h
  linear_combination h

end
end RHTower.D4BMOriginalCausalDifference
