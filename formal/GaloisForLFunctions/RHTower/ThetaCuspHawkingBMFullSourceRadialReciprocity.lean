import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceAdvancedAdmission
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceReflectionTransport

/-!
Absolute time/radial reciprocity for the original full-theta reduced source.
Both source events, the fixed onset, both causal supports and the Dirichlet image
are retained. The resulting full square-source bulk pairing is skew and exchanges
its physical branches under functional-equation reflection without a reciprocity
premise. This does not identify the retarded integral with the existing null-field
representative, prove the advanced wave equation, or attach the lift, cap and full
metric/QNM action. No extinction statement or RH proof is asserted.
-/

open Set MeasureTheory Filter Topology
namespace RHTower.D4BMFullSourceReciprocity
open D4BMNativeCircle D4BMCausalKernel D4BMJointSource D4BMModularCore
open D4BMFullSourceAdvanced
noncomputable section
set_option autoImplicit false

abbrev Event := ℝ × ℝ

abbrev eventMeasure : Measure Event :=
  (volume.restrict (Ioi 0)).prod (volume.restrict (Iio 0))

private theorem kernel_negative (q : XiZeroCopy) (h x y X k : ℝ) (hh : h < 0) :
    nativeDirichletCausalKernel q h x y X k = 0 := by
  have h1 : ¬ |x-y| ≤ h := not_le.mpr ((abs_nonneg _).trans_lt' hh)
  have h2 : ¬ |x+y| ≤ h := not_le.mpr ((abs_nonneg _).trans_lt' hh)
  simp only [nativeDirichletCausalKernel,if_neg h1,if_neg h2,sub_self,zero_div]

/-- Radial reciprocity of the literal full-theta direct-minus-image kernel. -/
theorem kernel_radial_reciprocity (q : XiZeroCopy) (h x y X k : ℝ) :
    nativeDirichletCausalKernel q h x y X k =
      nativeDirichletCausalKernel q h y x X k := by
  have hd : invariant h x y = invariant h y x := by unfold invariant; ring
  have hi : invariant h x (-y) = invariant h y (-x) := by
    simp only [invariant,Real.sinh_neg,Real.cosh_neg]; ring
  simp only [nativeDirichletCausalKernel,nativeRiemannKernel,hd,hi,abs_sub_comm x y,add_comm x y]

private theorem kernel_measurable (q : XiZeroCopy) (X k : ℝ) :
    Measurable (fun z : ℝ × ℝ × ℝ => nativeDirichletCausalKernel q z.1 z.2.1 z.2.2 X k) := by
  classical
  have cone (y : (ℝ × ℝ × ℝ) → ℝ) (hy : Continuous y) : Measurable (fun p : ℝ × ℝ × ℝ =>
      if |p.2.1-y p| ≤ p.1 then nativeRiemannKernel q p.1 p.2.1 (y p) X k else 0) := by
    have hi : Continuous (fun p : ℝ × ℝ × ℝ => invariant p.1 p.2.1 (y p)) := by
      unfold invariant
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro p; exact mul_ne_zero (Real.cosh_pos _).ne' (Real.cosh_pos _).ne'
    have hr := Real.continuousOn_arcosh.comp_continuous (continuous_const.max hi)
      (fun p => show 1 ≤ max 1 (invariant p.1 p.2.1 (y p)) from le_max_left _ _)
    have hm := ((mean_radial_smooth q X k).continuous.comp hr).measurable
    have hs : MeasurableSet {p : ℝ × ℝ × ℝ | |p.2.1-y p| ≤ p.1} :=
      (isClosed_le (continuous_snd.fst.sub hy).abs continuous_fst).measurableSet
    have he : Measurable (fun p : ℝ × ℝ × ℝ =>
        if |p.2.1-y p| ≤ p.1 then mean q (Real.arcosh (max 1 (invariant p.1 p.2.1 (y p)))) X k else 0) :=
      Measurable.ite hs hm measurable_const
    convert he using 1
    funext p
    by_cases hc : |p.2.1-y p| ≤ p.1
    · simp only [if_pos hc,nativeRiemannKernel,angularKernel,
        max_eq_right (invariant_causal ⟨p.1,p.2.1,y p,hc⟩)]
    · simp only [if_neg hc]
  have hd := cone (fun p => p.2.2) (by fun_prop)
  have hi := cone (fun p => -p.2.2) (by fun_prop)
  simpa only [sub_neg_eq_add,nativeDirichletCausalKernel,Pi.sub_apply] using (hd.sub hi).div_const (2:ℂ)

/-- The two original quadratic reduced sources contracted through the full causal kernel.
The first event is the earlier event; the second is the later event. -/
def sourcePairDensity (q : XiZeroCopy) (b c : Bool) (a d : ℂ) (X k : ℝ)
    (z : Event × Event) : ℂ :=
  timeReducedCoefficient (physicalRate q b) a z.1.1 z.1.2 *
    nativeDirichletCausalKernel q (z.2.1-z.1.1) z.1.2 z.2.2 X k *
      timeReducedCoefficient (physicalRate q c) d z.2.1 z.2.2

private theorem pair_measurable (q : XiZeroCopy) (b c : Bool) (a d : ℂ) (X k : ℝ) :
    Measurable (sourcePairDensity q b c a d X k) := by
  have h1 := (timeReducedCoefficient_joint_continuous (physicalRate q b) a).measurable.comp (measurable_fst : Measurable (Prod.fst : Event × Event → Event))
  have h2 := (timeReducedCoefficient_joint_continuous (physicalRate q c) d).measurable.comp (measurable_snd : Measurable (Prod.snd : Event × Event → Event))
  have hk := (kernel_measurable q X k).comp
    (show Measurable (fun z : Event × Event => (z.2.1-z.1.1,z.1.2,z.2.2)) by fun_prop)
  exact (h1.mul hk).mul h2

private def eventWeight (q : XiZeroCopy) (v : ℝ) (p : Event) : ℝ :=
  Real.exp (v*p.1)*Real.exp ((2-decayExponent q)*p.2)

private theorem eventWeight_integrable (q : XiZeroCopy) (v : ℝ) (hv : v < 0) :
    Integrable (eventWeight q v) eventMeasure := by
  have ht := integrableOn_exp_mul_Ioi hv 0
  have hx := (integrableOn_exp_mul_Iic (show 0 < 2-decayExponent q from
    sub_pos.mpr (decayExponent_bounds q).2) 0).mono_set Iio_subset_Iic_self
  exact ht.mul_prod hx

private theorem pair_bound (q : XiZeroCopy) (b c : Bool) (a d : ℂ) (X k : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p r : Event, p.2 < 0 → r.2 < 0 →
      ‖sourcePairDensity q b c a d X k (p,r)‖ ≤ D *
        (eventWeight q (-decayExponent q-sourceGrowthExponent q) p *
          eventWeight q (sourceGrowthExponent q-decayExponent q) r) := by
  obtain ⟨C,hC,hK⟩ := kernel_growth q
  obtain ⟨A,hA,hf⟩ := timeReducedCoefficient_physical_bound q b a _ (decayExponent_bounds q).2
  obtain ⟨B,hB,hg⟩ := timeReducedCoefficient_physical_bound q c d _ (decayExponent_bounds q).2
  refine ⟨A*C*B*Real.exp (sourceGrowthExponent q*|k|),by positivity,fun p r hp hr => ?_⟩
  by_cases ht : 0 ≤ r.1-p.1
  · have h := mul_le_mul (mul_le_mul (hf p.1 p.2 hp) (hK (r.1-p.1) p.2 r.2 X k ht)
        (norm_nonneg _) (by positivity)) (hg r.1 r.2 hr) (norm_nonneg _) (by positivity)
    rw [sourcePairDensity,norm_mul,norm_mul]
    apply h.trans_eq
    simp only [eventWeight]
    simp only [sub_mul,mul_add,mul_sub,neg_mul,Real.exp_add,Real.exp_sub,Real.exp_neg]
    ring
  · rw [sourcePairDensity,kernel_negative q _ _ _ X k (lt_of_not_ge ht),mul_zero,zero_mul,norm_zero]
    dsimp only [eventWeight]
    positivity

/-- Absolute admission of both original source times and both full radial variables. -/
theorem sourcePairDensity_integrable (q : XiZeroCopy) (b c : Bool) (a d : ℂ) (X k : ℝ) :
    Integrable (sourcePairDensity q b c a d X k) (eventMeasure.prod eventMeasure) := by
  have hb := decayExponent_bounds q
  have hg := (sourceGrowthExponent_bounds q).1
  obtain ⟨D,hD,h⟩ := pair_bound q b c a d X k
  have hm := ((eventWeight_integrable q (-decayExponent q-sourceGrowthExponent q) (by linarith)).mul_prod
    (eventWeight_integrable q (sourceGrowthExponent q-decayExponent q) (by linarith))).const_mul D
  apply hm.mono' (pair_measurable q b c a d X k).aestronglyMeasurable
  have he : ∀ᵐ p : Event ∂eventMeasure, p.2 < 0 := by
    apply (Measure.ae_prod_iff_ae_ae ((isOpen_lt continuous_snd continuous_const).measurableSet : MeasurableSet {p : Event | p.2 < 0})).mpr
    exact ae_of_all _ (fun _ => ae_restrict_mem measurableSet_Iio)
  have hz : ∀ᵐ z : Event × Event ∂eventMeasure.prod eventMeasure, z.1.2 < 0 ∧ z.2.2 < 0 := by
    apply (Measure.ae_prod_iff_ae_ae (((isOpen_lt continuous_fst.snd continuous_const).inter
      (isOpen_lt continuous_snd.snd continuous_const)).measurableSet : MeasurableSet {z : Event × Event | z.1.2 < 0 ∧ z.2.2 < 0})).mpr
    filter_upwards [he] with p hp
    filter_upwards [he] with r hr
    exact ⟨hp,hr⟩
  filter_upwards [hz] with z hz
  exact h z.1 z.2 hz.1 hz.2

def directedSourceDensity (q : XiZeroCopy) (b : Bool) (a : ℂ)
    (τ x X k : ℝ) (future : Bool) (p : Event) : ℂ :=
  nativeDirichletCausalKernel q (if future then p.1-τ else τ-p.1) x p.2 X k *
    timeReducedCoefficient (physicalRate q b) a p.1 p.2

private theorem directed_integrable (q : XiZeroCopy) (b : Bool) (a : ℂ)
    (τ x X k : ℝ) (future : Bool) :
    Integrable (directedSourceDensity q b a τ x X k future) eventMeasure := by
  have hb := decayExponent_bounds q
  have hg := (sourceGrowthExponent_bounds q).1
  obtain ⟨C,hC,hK⟩ := kernel_growth q
  obtain ⟨A,hA,hf⟩ := timeReducedCoefficient_physical_bound q b a _ hb.2
  have hm : Measurable (directedSourceDensity q b a τ x X k future) := by
    have hk := (kernel_measurable q X k).comp
      (show Measurable (fun p : Event => ((if future then p.1-τ else τ-p.1),x,p.2)) by
        cases future <;> simp only [Bool.false_eq_true,if_false,if_true] <;> fun_prop)
    exact hk.mul (timeReducedCoefficient_joint_continuous (physicalRate q b) a).measurable
  let v := if future then sourceGrowthExponent q else -sourceGrowthExponent q
  have hv : v-decayExponent q < 0 := by cases future <;> simp only [v,Bool.false_eq_true,if_false,if_true] <;> linarith
  have hi := (eventWeight_integrable q (v-decayExponent q) hv).const_mul
    (C*A*Real.exp (-v*τ+sourceGrowthExponent q*|k|))
  apply hi.mono' hm.aestronglyMeasurable
  have he : ∀ᵐ p : Event ∂eventMeasure, p.2 < 0 := by
    apply (Measure.ae_prod_iff_ae_ae ((isOpen_lt continuous_snd continuous_const).measurableSet : MeasurableSet {p : Event | p.2 < 0})).mpr
    exact ae_of_all _ (fun _ => ae_restrict_mem measurableSet_Iio)
  filter_upwards [he] with p hp
  by_cases ht : 0 ≤ (if future then p.1-τ else τ-p.1)
  · have hh := mul_le_mul (hK _ x p.2 X k ht) (hf p.1 p.2 hp) (norm_nonneg _) (by positivity)
    rw [directedSourceDensity,norm_mul]
    apply hh.trans_eq
    cases future <;> simp only [v,eventWeight,Bool.false_eq_true,if_false,if_true]
    all_goals
      simp only [sub_mul,mul_add,mul_sub,neg_mul,Real.exp_add,Real.exp_sub,Real.exp_neg,inv_inv]
      ring
  · rw [directedSourceDensity,kernel_negative q _ x p.2 X k (lt_of_not_ge ht),zero_mul,norm_zero]
    dsimp only [eventWeight]
    positivity

private theorem future_time_shift (q : XiZeroCopy) (b : Bool) (a : ℂ)
    (τ x X k y : ℝ) (hy : y < 0) :
    (∫ h in Ioi (0:ℝ), nativeDirichletCausalKernel q h x y X k *
      timeReducedCoefficient (physicalRate q b) a (τ+h) y) =
    ∫ t in Ioi (0:ℝ), directedSourceDensity q b a τ x X k true (t,y) := by
  let F := fun h : ℝ => nativeDirichletCausalKernel q h x y X k *
    timeReducedCoefficient (physicalRate q b) a (τ+h) y
  let N := fun t : ℝ => directedSourceDensity q b a τ x X k true (t,y)
  have hF : (∫ h in Ioi (0:ℝ), F h)=∫ h : ℝ, F h := by
    rw [← integral_Ici_eq_integral_Ioi]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro h hh
    simp only [mem_Ici,not_le] at hh
    simp only [F,kernel_negative q h x y X k hh,zero_mul]
  have hN : (∫ t in Ioi (0:ℝ), N t)=∫ t : ℝ, N t := by
    rw [← integral_Ici_eq_integral_Ioi]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    simp only [mem_Ici,not_le] at ht
    have hz := timeReducedCoefficient_zero_before_onset (physicalRate q b) a t y (by linarith)
    simp only [N,directedSourceDensity,hz,mul_zero]
  have he : (fun h : ℝ => N (h+τ))=F := by
    funext h
    simp only [N,F,directedSourceDensity,if_true]
    rw [add_sub_cancel_right,add_comm h τ]
  change (∫ h in Ioi (0:ℝ), F h)=∫ t in Ioi (0:ℝ),N t
  rw [hF,hN]
  simpa only [he] using integral_add_right_eq_self N τ

/-- The admitted future response in the original source-event coordinates. -/
theorem futureResponse_event_integral (q : XiZeroCopy) (b : Bool) (a : ℂ) (τ x X k : ℝ) :
    response q b a τ x X k =
      ∫ p, directedSourceDensity q b a τ x X k true p ∂eventMeasure := by
  have hi : Integrable (density q b a τ x X k) eventMeasure := by
    have hi := density_integrable q b a τ x X k
    simpa only [IntegrableOn,Measure.volume_eq_prod,← Measure.prod_restrict,eventMeasure] using hi
  have h1 := integral_prod_symm _ hi
  have h2 := integral_prod_symm _ (directed_integrable q b a τ x X k true)
  have he : response q b a τ x X k = ∫ p, density q b a τ x X k p ∂eventMeasure := by
    rw [response,eventMeasure,Measure.prod_restrict,← Measure.volume_eq_prod]
  rw [he,h1,h2]
  apply setIntegral_congr_fun measurableSet_Iio
  intro y hy
  exact future_time_shift q b a τ x X k y hy

/-- Original past-directed full kernel applied to the unchanged quadratic source. -/
def retardedResponse (q : XiZeroCopy) (b : Bool) (a : ℂ) (τ x X k : ℝ) : ℂ :=
  ∫ p, directedSourceDensity q b a τ x X k false p ∂eventMeasure

private theorem pair_future_inner (q : XiZeroCopy) (b c : Bool) (a d : ℂ)
    (X k : ℝ) (p : Event) :
    (∫ r, sourcePairDensity q b c a d X k (p,r) ∂eventMeasure) =
      timeReducedCoefficient (physicalRate q b) a p.1 p.2 * response q c d p.1 p.2 X k := by
  rw [futureResponse_event_integral,← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun r => by simp only [sourcePairDensity,directedSourceDensity,if_true]; ring)

private theorem pair_retarded_inner (q : XiZeroCopy) (b c : Bool) (a d : ℂ)
    (X k : ℝ) (r : Event) :
    (∫ p, sourcePairDensity q b c a d X k (p,r) ∂eventMeasure) =
      retardedResponse q b a r.1 r.2 X k * timeReducedCoefficient (physicalRate q c) d r.1 r.2 := by
  rw [retardedResponse,← integral_mul_const]
  apply integral_congr_ae
  exact ae_of_all _ (fun p => by
    simp only [sourcePairDensity,directedSourceDensity,Bool.false_eq_true,if_false]
    rw [kernel_radial_reciprocity q (r.1-p.1) p.2 r.2 X k]
    ring)

/-- Both complete source-response pairings are absolutely integrable. -/
theorem source_response_pairings_integrable (q : XiZeroCopy) (b c : Bool) (a d : ℂ) (X k : ℝ) :
    Integrable (fun p : Event => timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
      response q c d p.1 p.2 X k) eventMeasure ∧
    Integrable (fun p : Event => retardedResponse q b a p.1 p.2 X k *
      timeReducedCoefficient (physicalRate q c) d p.1 p.2) eventMeasure := by
  have hi := sourcePairDensity_integrable q b c a d X k
  constructor
  · simpa only [pair_future_inner] using hi.integral_prod_left
  · simpa only [pair_retarded_inner] using hi.integral_prod_right

/-- Exact time/radial reciprocity for the original source and its full theta kernel.
No reciprocity premise, late-onset substitution, or omitted image contribution is used. -/
theorem original_source_retarded_advanced_reciprocity (q : XiZeroCopy) (b c : Bool)
    (a d : ℂ) (X k : ℝ) :
    (∫ p, timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
      response q c d p.1 p.2 X k ∂eventMeasure) =
    ∫ p, retardedResponse q b a p.1 p.2 X k *
      timeReducedCoefficient (physicalRate q c) d p.1 p.2 ∂eventMeasure := by
  have hi := sourcePairDensity_integrable q b c a d X k
  have hf := integral_prod _ hi
  have hr := integral_prod_symm _ hi
  simpa only [pair_future_inner,pair_retarded_inner] using hf.symm.trans hr

/-- Source-selected causal difference, retaining the two original quadratic source factors. -/
def causalSourcePair (q : XiZeroCopy) (b c : Bool) (a d : ℂ) (X k : ℝ) : ℂ :=
  ∫ p, timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
    (retardedResponse q c d p.1 p.2 X k-response q c d p.1 p.2 X k) ∂eventMeasure

/-- The surviving causal source action is exactly the antisymmetric two-source integral. -/
theorem causalSourcePair_decomposition (q : XiZeroCopy) (b c : Bool) (a d : ℂ) (X k : ℝ) :
    causalSourcePair q b c a d X k =
      (∫ z, sourcePairDensity q c b d a X k z ∂eventMeasure.prod eventMeasure) -
        ∫ z, sourcePairDensity q b c a d X k z ∂eventMeasure.prod eventMeasure := by
  have hbc := source_response_pairings_integrable q b c a d X k
  have hcb := source_response_pairings_integrable q c b d a X k
  have hr : Integrable (fun p : Event => timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
      retardedResponse q c d p.1 p.2 X k) eventMeasure := by simpa only [mul_comm] using hcb.2
  have hf := integral_prod _ (sourcePairDensity_integrable q b c a d X k)
  have hg := integral_prod_symm _ (sourcePairDensity_integrable q c b d a X k)
  simp only [pair_future_inner] at hf
  simp only [pair_retarded_inner] at hg
  rw [causalSourcePair]
  simp_rw [mul_sub]
  rw [integral_sub hr hbc.1,← hf]
  congr 1
  simpa only [mul_comm] using hg.symm

/-- Antisymmetry is proved for these actual source integrals rather than assumed of an abstract inverse. -/
theorem causalSourcePair_skew (q : XiZeroCopy) (b c : Bool) (a d : ℂ) (X k : ℝ) :
    causalSourcePair q b c a d X k = -causalSourcePair q c b d a X k := by
  rw [causalSourcePair_decomposition,causalSourcePair_decomposition]
  ring

theorem causalSourcePair_self (q : XiZeroCopy) (b : Bool) (a : ℂ) (X k : ℝ) :
    causalSourcePair q b b a a X k = 0 := by
  rw [causalSourcePair_decomposition,sub_self]

/-- The actual full theta-square testing source, on the entire time/radial domain. -/
def causalSquareSourcePair (q : XiZeroCopy) (b c : Bool) (a d : ℂ) (X k : ℝ) : ℂ :=
  ∫ p, (timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
    fullSquarePotential q ![X,Real.exp k]) *
      (retardedResponse q c d p.1 p.2 X k-response q c d p.1 p.2 X k) ∂eventMeasure

/-- Absolute admission also retains the full angular testing-source factor. -/
theorem causalSquareSourcePair_integrable (q : XiZeroCopy) (b c : Bool)
    (a d : ℂ) (X k : ℝ) :
    Integrable (fun p : Event => (timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
      fullSquarePotential q ![X,Real.exp k]) *
        (retardedResponse q c d p.1 p.2 X k-response q c d p.1 p.2 X k)) eventMeasure := by
  have hf := (source_response_pairings_integrable q b c a d X k).1
  have hr : Integrable (fun p : Event => timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
      retardedResponse q c d p.1 p.2 X k) eventMeasure := by
    simpa only [mul_comm] using (source_response_pairings_integrable q c b d a X k).2
  have h := (hr.sub hf).const_mul (fullSquarePotential q ![X,Real.exp k])
  convert h using 1
  funext p
  simp only [Pi.sub_apply]
  ring

theorem causalSquareSourcePair_eq (q : XiZeroCopy) (b c : Bool) (a d : ℂ) (X k : ℝ) :
    causalSquareSourcePair q b c a d X k =
      fullSquarePotential q ![X,Real.exp k] * causalSourcePair q b c a d X k := by
  rw [causalSquareSourcePair,causalSourcePair,← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun _ => by ring)

/-- The square-source bulk pairing is skew before taking any angular cutoff or finite part. -/
theorem causalSquareSourcePair_skew (q : XiZeroCopy) (b c : Bool) (a d : ℂ) (X k : ℝ) :
    causalSquareSourcePair q b c a d X k = -causalSquareSourcePair q c b d a X k := by
  rw [causalSquareSourcePair_eq,causalSquareSourcePair_eq,causalSourcePair_skew,mul_neg]

private theorem kernel_reflect (q : XiZeroCopy) (h x y X k : ℝ) :
    nativeDirichletCausalKernel (xiZeroCopyReflectEquiv q) h x y X k =
      nativeDirichletCausalKernel q h x y X k := by
  simp only [nativeDirichletCausalKernel,nativeRiemannKernel,angularKernel,mean,
    D4BMNativeCircle.source,D4BMSourceReflectionTransport.square_reflect]

private theorem pair_reflect (q : XiZeroCopy) (b c : Bool) (a d : ℂ) (X k : ℝ) :
    sourcePairDensity (xiZeroCopyReflectEquiv q) b c a d X k =
      sourcePairDensity q (!b) (!c) a d X k := by
  funext z
  simp only [sourcePairDensity,D4BMSourceReflectionTransport.physicalRate_reflect,kernel_reflect]

/-- Functional-equation reflection transports the actual admitted causal bulk. -/
theorem causalSourcePair_reflect (q : XiZeroCopy) (b c : Bool) (a d : ℂ) (X k : ℝ) :
    causalSourcePair (xiZeroCopyReflectEquiv q) b c a d X k =
      causalSourcePair q (!b) (!c) a d X k := by
  simp only [causalSourcePair_decomposition,pair_reflect]

/-- Reflection reverses the two original branch sources and their independent amplitudes. -/
theorem causalSquareSourcePair_reflection_odd (q : XiZeroCopy) (a d : ℂ) (X k : ℝ) :
    causalSquareSourcePair (xiZeroCopyReflectEquiv q) true false a d X k =
      -causalSquareSourcePair q true false d a X k := by
  simp only [causalSquareSourcePair_eq,D4BMSourceReflectionTransport.square_reflect,
    causalSourcePair_reflect,Bool.not_true,Bool.not_false]
  rw [causalSourcePair_skew q false true a d X k,mul_neg]

end
end RHTower.D4BMFullSourceReciprocity
