import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralCyclicPeierls
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFullSourceRadialReciprocity

/-!
# Full-circle causal Peierls pairing

The pairing below uses the literal full theta-circle direct-minus-image kernel,
not its native half-square component.  Its strict kernel exponent is below the
physical clock exponent, so the two source-event integrals are absolutely
admitted.  Radial reciprocity then makes the retarded-minus-advanced pairing
skew without a formal inverse or a symmetry premise.

Proof-chain role:
`literal cyclic core + strict full-kernel admission -> full source-event
retarded-minus-advanced pairing -> cap/contact equality -> HB causal cut`.
This proves the source-event Peierls stage only; it does not assert the
noncompact cap/contact equality.
-/

open Set MeasureTheory Filter Topology

namespace RHTower.D4BMFullAngularCausalPeierls

open D4BMNativeCircle D4BMCausalKernel D4BMJointSource D4BMModularCore
open D4BMFullAngularCircle D4BMFullAngularReconstruction
open D4BMFullAngularGrowth D4BMFullSourceAdvanced
open D4BMLiteralCyclicPeierls

noncomputable section
set_option autoImplicit false

abbrev Event := ℝ × ℝ

abbrev eventMeasure : Measure Event :=
  (volume.restrict (Ioi 0)).prod (volume.restrict (Iio 0))

private theorem full_kernel_negative (q : XiZeroCopy) (branch : Bool)
    (h x y X k : ℝ) (hh : h < 0) :
    angularDirichletKernel q branch h x y X k = 0 := by
  have h1 : ¬ |x - y| ≤ h := not_le.mpr ((abs_nonneg _).trans_lt' hh)
  have h2 : ¬ |x + y| ≤ h := not_le.mpr ((abs_nonneg _).trans_lt' hh)
  simp [angularDirichletKernel, h1, h2]

private theorem full_kernel_measurable (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
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
  simpa only [angularDirichletKernel, sub_neg_eq_add, Pi.sub_apply] using (hd.sub hi).div_const (2 : ℂ)

/-- Two original source events coupled through the literal full theta-circle
direct-minus-image kernel. -/
def fullSourcePairDensity (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ) (X k : ℝ)
    (z : Event × Event) : ℂ :=
  timeReducedCoefficient (physicalRate q b) a z.1.1 z.1.2 *
    angularDirichletKernel q branch (z.2.1 - z.1.1) z.1.2 z.2.2 X k *
      timeReducedCoefficient (physicalRate q c) d z.2.1 z.2.2

private theorem full_pair_measurable (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) :
    Measurable (fullSourcePairDensity q branch b c a d X k) := by
  have h1 := (timeReducedCoefficient_joint_continuous (physicalRate q b) a).measurable.comp
    (measurable_fst : Measurable (Prod.fst : Event × Event → Event))
  have h2 := (timeReducedCoefficient_joint_continuous (physicalRate q c) d).measurable.comp
    (measurable_snd : Measurable (Prod.snd : Event × Event → Event))
  have hk := (full_kernel_measurable q branch X k).comp
    (show Measurable (fun z : Event × Event => (z.2.1 - z.1.1, z.1.2, z.2.2)) by fun_prop)
  exact (h1.mul hk).mul h2

private def eventWeight (q : XiZeroCopy) (v : ℝ) (p : Event) : ℝ :=
  Real.exp (v * p.1) * Real.exp ((2 - decayExponent q) * p.2)

private theorem eventWeight_integrable (q : XiZeroCopy) (v : ℝ) (hv : v < 0) :
    Integrable (eventWeight q v) eventMeasure := by
  have ht := integrableOn_exp_mul_Ioi hv 0
  have hx := (integrableOn_exp_mul_Iic (show 0 < 2 - decayExponent q from
    sub_pos.mpr (decayExponent_bounds q).2) 0).mono_set Iio_subset_Iic_self
  exact ht.mul_prod hx

private theorem full_pair_bound (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p r : Event, p.2 < 0 → r.2 < 0 →
      ‖fullSourcePairDensity q branch b c a d X k (p, r)‖ ≤ D *
        (eventWeight q (-decayExponent q - strictGrowthExponent q) p *
          eventWeight q (strictGrowthExponent q - decayExponent q) r) := by
  obtain ⟨C, hC, hK⟩ := angularDirichletKernel_strict_growth q branch X k
  obtain ⟨A, hA, hf⟩ := timeReducedCoefficient_physical_bound q b a _
    (decayExponent_bounds q).2
  obtain ⟨B, hB, hg⟩ := timeReducedCoefficient_physical_bound q c d _
    (decayExponent_bounds q).2
  refine ⟨A * C * B, by positivity, fun p r hp hr => ?_⟩
  by_cases ht : 0 ≤ r.1 - p.1
  · have h := mul_le_mul
      (mul_le_mul (hf p.1 p.2 hp) (hK (r.1 - p.1) p.2 r.2 ht)
        (norm_nonneg _) (by positivity))
      (hg r.1 r.2 hr) (norm_nonneg _) (by positivity)
    rw [fullSourcePairDensity, norm_mul, norm_mul]
    apply h.trans_eq
    simp only [eventWeight]
    simp only [sub_mul, mul_sub, neg_mul, Real.exp_sub, Real.exp_neg]
    ring
  · rw [fullSourcePairDensity,
      full_kernel_negative q branch _ p.2 r.2 X k (lt_of_not_ge ht), mul_zero, zero_mul, norm_zero]
    dsimp only [eventWeight]
    positivity

/-- Absolute admission of both original source times through the literal full
circle kernel. -/
theorem fullSourcePairDensity_integrable (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) :
    Integrable (fullSourcePairDensity q branch b c a d X k) (eventMeasure.prod eventMeasure) := by
  obtain ⟨D, hD, h⟩ := full_pair_bound q branch b c a d X k
  have hp : -decayExponent q - strictGrowthExponent q < 0 := by
    have hs := (sourceGrowthExponent_bounds q).1
    have hd := (decayExponent_bounds q).1
    have hg := (strictGrowthExponent_bounds q).1
    linarith
  have hr : strictGrowthExponent q - decayExponent q < 0 := by
    linarith [(strictGrowthExponent_bounds q).2]
  have hm := ((eventWeight_integrable q (-decayExponent q - strictGrowthExponent q) hp).mul_prod
    (eventWeight_integrable q (strictGrowthExponent q - decayExponent q) hr)).const_mul D
  apply hm.mono' (full_pair_measurable q branch b c a d X k).aestronglyMeasurable
  have he : ∀ᵐ p : Event ∂eventMeasure, p.2 < 0 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((isOpen_lt continuous_snd continuous_const).measurableSet : MeasurableSet {p : Event | p.2 < 0})).mpr
    exact ae_of_all _ (fun _ => ae_restrict_mem measurableSet_Iio)
  have hz : ∀ᵐ z : Event × Event ∂eventMeasure.prod eventMeasure, z.1.2 < 0 ∧ z.2.2 < 0 := by
    apply (Measure.ae_prod_iff_ae_ae
      (((isOpen_lt continuous_fst.snd continuous_const).inter
        (isOpen_lt continuous_snd.snd continuous_const)).measurableSet :
          MeasurableSet {z : Event × Event | z.1.2 < 0 ∧ z.2.2 < 0})).mpr
    filter_upwards [he] with p hp
    filter_upwards [he] with r hr
    exact ⟨hp, hr⟩
  filter_upwards [hz] with z hz
  exact h z.1 z.2 hz.1 hz.2

private def directedFullDensity (q : XiZeroCopy) (branch b : Bool) (a : ℂ)
    (τ x X k : ℝ) (future : Bool) (p : Event) : ℂ :=
  angularDirichletKernel q branch (if future then p.1 - τ else τ - p.1) x p.2 X k *
    timeReducedCoefficient (physicalRate q b) a p.1 p.2

private theorem directed_integrable (q : XiZeroCopy) (branch b : Bool) (a : ℂ)
    (τ x X k : ℝ) (future : Bool) :
    Integrable (directedFullDensity q branch b a τ x X k future) eventMeasure := by
  obtain ⟨C, hC, hK⟩ := angularDirichletKernel_strict_growth q branch X k
  obtain ⟨A, hA, hf⟩ := timeReducedCoefficient_physical_bound q b a _
    (decayExponent_bounds q).2
  have hm : Measurable (directedFullDensity q branch b a τ x X k future) := by
    have hk := (full_kernel_measurable q branch X k).comp
      (show Measurable (fun p : Event => ((if future then p.1 - τ else τ - p.1), x, p.2)) by
        cases future <;> simp only [Bool.false_eq_true, if_false, if_true] <;> fun_prop)
    exact hk.mul (timeReducedCoefficient_joint_continuous (physicalRate q b) a).measurable
  let v := if future then strictGrowthExponent q else -strictGrowthExponent q
  have hv : v - decayExponent q < 0 := by
    have hs := (sourceGrowthExponent_bounds q).1
    have hd := (decayExponent_bounds q).1
    have hg := (strictGrowthExponent_bounds q).1
    have hgd := (strictGrowthExponent_bounds q).2
    cases future <;> simp only [v, Bool.false_eq_true, if_false, if_true] <;> linarith
  have hi := (eventWeight_integrable q (v - decayExponent q) hv).const_mul
    (C * A * Real.exp (-v * τ))
  apply hi.mono' hm.aestronglyMeasurable
  have he : ∀ᵐ p : Event ∂eventMeasure, p.2 < 0 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((isOpen_lt continuous_snd continuous_const).measurableSet : MeasurableSet {p : Event | p.2 < 0})).mpr
    exact ae_of_all _ (fun _ => ae_restrict_mem measurableSet_Iio)
  filter_upwards [he] with p hp
  by_cases ht : 0 ≤ (if future then p.1 - τ else τ - p.1)
  · have hh := mul_le_mul (hK _ x p.2 ht) (hf p.1 p.2 hp)
      (norm_nonneg _) (mul_nonneg hC (Real.exp_pos _).le)
    rw [directedFullDensity, norm_mul]
    apply hh.trans_eq
    cases future <;> simp only [v, eventWeight, Bool.false_eq_true, if_false, if_true]
    all_goals
      simp only [sub_mul, mul_sub, neg_mul, Real.exp_sub, Real.exp_neg, inv_inv]
      ring
  · rw [directedFullDensity,
      full_kernel_negative q branch _ x p.2 X k (lt_of_not_ge ht), zero_mul, norm_zero]
    dsimp only [eventWeight]
    positivity

/-- Future full-circle response of one original source leg. -/
def fullFutureResponse (q : XiZeroCopy) (branch b : Bool) (a : ℂ)
    (τ x X k : ℝ) : ℂ :=
  ∫ p, directedFullDensity q branch b a τ x X k true p ∂eventMeasure

/-- Retarded full-circle response of one original source leg. -/
def fullRetardedResponse (q : XiZeroCopy) (branch b : Bool) (a : ℂ)
    (τ x X k : ℝ) : ℂ :=
  ∫ p, directedFullDensity q branch b a τ x X k false p ∂eventMeasure

private theorem pair_future_inner (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ)
    (X k : ℝ) (p : Event) :
    (∫ r, fullSourcePairDensity q branch b c a d X k (p, r) ∂eventMeasure) =
      timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
        fullFutureResponse q branch c d p.1 p.2 X k := by
  rw [fullFutureResponse, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun r => by
    simp only [fullSourcePairDensity, directedFullDensity, if_true]
    ring)

private theorem pair_retarded_inner (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ)
    (X k : ℝ) (r : Event) :
    (∫ p, fullSourcePairDensity q branch b c a d X k (p, r) ∂eventMeasure) =
      fullRetardedResponse q branch b a r.1 r.2 X k *
        timeReducedCoefficient (physicalRate q c) d r.1 r.2 := by
  rw [fullRetardedResponse, ← integral_mul_const]
  apply integral_congr_ae
  exact ae_of_all _ (fun p => by
    simp only [fullSourcePairDensity, directedFullDensity, Bool.false_eq_true, if_false]
    rw [angularDirichletKernel_cyclic q branch (r.1 - p.1) p.2 r.2 X k]
    ring)

/-- Both literal full-kernel source-response pairings are absolutely admitted. -/
theorem full_source_response_pairings_integrable (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) :
    Integrable (fun p : Event => timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
      fullFutureResponse q branch c d p.1 p.2 X k) eventMeasure ∧
    Integrable (fun p : Event => fullRetardedResponse q branch b a p.1 p.2 X k *
      timeReducedCoefficient (physicalRate q c) d p.1 p.2) eventMeasure := by
  have hi := fullSourcePairDensity_integrable q branch b c a d X k
  constructor
  · simpa only [pair_future_inner] using hi.integral_prod_left
  · simpa only [pair_retarded_inner] using hi.integral_prod_right

/-- Literal full-circle retarded-minus-advanced Peierls pairing of two source legs. -/
def fullCausalSourcePair (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ) (X k : ℝ) : ℂ :=
  ∫ p, timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
    (fullRetardedResponse q branch c d p.1 p.2 X k -
      fullFutureResponse q branch c d p.1 p.2 X k) ∂eventMeasure

/-- The full-circle causal pairing is the antisymmetrization of the admitted
two-event literal source integral. -/
theorem fullCausalSourcePair_decomposition (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) :
    fullCausalSourcePair q branch b c a d X k =
      (∫ z, fullSourcePairDensity q branch c b d a X k z ∂eventMeasure.prod eventMeasure) -
        ∫ z, fullSourcePairDensity q branch b c a d X k z ∂eventMeasure.prod eventMeasure := by
  have hbc := full_source_response_pairings_integrable q branch b c a d X k
  have hcb := full_source_response_pairings_integrable q branch c b d a X k
  have hr : Integrable (fun p : Event => timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
      fullRetardedResponse q branch c d p.1 p.2 X k) eventMeasure := by
    simpa only [mul_comm] using hcb.2
  have hf := integral_prod _ (fullSourcePairDensity_integrable q branch b c a d X k)
  have hg := integral_prod_symm _ (fullSourcePairDensity_integrable q branch c b d a X k)
  simp only [pair_future_inner] at hf
  simp only [pair_retarded_inner] at hg
  rw [fullCausalSourcePair]
  simp_rw [mul_sub]
  rw [integral_sub hr hbc.1, ← hf]
  congr 1
  simpa only [mul_comm] using hg.symm

/-- Cyclicity is now a theorem of the actual full theta-circle source-event
integrals, not an axiom about an abstract propagator. -/
theorem fullCausalSourcePair_skew (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) :
    fullCausalSourcePair q branch b c a d X k =
      -fullCausalSourcePair q branch c b d a X k := by
  rw [fullCausalSourcePair_decomposition, fullCausalSourcePair_decomposition]
  ring

theorem fullCausalSourcePair_self (q : XiZeroCopy) (branch b : Bool)
    (a : ℂ) (X k : ℝ) :
    fullCausalSourcePair q branch b b a a X k = 0 := by
  rw [fullCausalSourcePair_decomposition, sub_self]

/-- Reciprocity turns the literal CTP pairing into the skew source pairing of
two future responses under one fixed full-kernel branch. Thus its Green-current
realization needs only the sourced future weak equation, not a separate
retarded-response PDE. -/
theorem fullCausalSourcePair_eq_future_skew (q : XiZeroCopy)
    (branch b c : Bool) (a d : ℂ) (X k : ℝ) :
    fullCausalSourcePair q branch b c a d X k =
      (∫ p : Event, timeReducedCoefficient (physicalRate q c) d p.1 p.2 *
          fullFutureResponse q branch b a p.1 p.2 X k ∂eventMeasure) -
        ∫ p : Event, timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
          fullFutureResponse q branch c d p.1 p.2 X k ∂eventMeasure := by
  rw [fullCausalSourcePair_decomposition]
  rw [integral_prod _ (fullSourcePairDensity_integrable q branch c b d a X k),
    integral_prod _ (fullSourcePairDensity_integrable q branch b c a d X k)]
  simp only [pair_future_inner]

private def futureTestDensity (q : XiZeroCopy) (branch b : Bool) (a : ℂ)
    (X k : ℝ) (phi : Event → ℂ) (z : Event × Event) : ℂ :=
  phi z.2 *
    (angularDirichletKernel q branch (z.1.1-z.2.1) z.2.2 z.1.2 X k *
      timeReducedCoefficient (physicalRate q b) a z.1.1 z.1.2)

private theorem futureTestDensity_measurable (q : XiZeroCopy)
    (branch b : Bool) (a : ℂ) (X k : ℝ) (phi : Event → ℂ)
    (hphi : Continuous phi) :
    Measurable (futureTestDensity q branch b a X k phi) := by
  have hk := (full_kernel_measurable q branch X k).comp
    (show Measurable (fun z : Event × Event =>
      ((z.1.1-z.2.1,z.2.2,z.1.2) : ℝ × ℝ × ℝ)) by fun_prop)
  have hj := (timeReducedCoefficient_joint_continuous (physicalRate q b) a).measurable.comp
    (measurable_fst : Measurable (Prod.fst : Event × Event → Event))
  exact (hphi.measurable.comp measurable_snd).mul (hk.mul hj)

/-- Absolute joint source/target admission of the literal future full-circle
response against every continuous compact physical time/radial test. The
strict full-kernel exponent remains below the actual source decay exponent. -/
theorem futureTestDensity_integrable (q : XiZeroCopy) (branch b : Bool)
    (a : ℂ) (X k : ℝ) (phi : Event → ℂ)
    (hphi : Continuous phi) (hc : HasCompactSupport phi) :
    Integrable (futureTestDensity q branch b a X k phi)
      (eventMeasure.prod volume) := by
  obtain ⟨C,hC,hK⟩ := angularDirichletKernel_strict_growth q branch X k
  obtain ⟨D,hD,hJ⟩ := timeReducedCoefficient_physical_bound q b a _
    (decayExponent_bounds q).2
  let w : Event → ℝ := fun r => ‖phi r‖ * Real.exp (-strictGrowthExponent q*r.1)
  have hw : Integrable w := by
    apply (hphi.norm.mul (by fun_prop)).integrable_of_hasCompactSupport
    exact hc.norm.mul_right
  have hrate : strictGrowthExponent q-decayExponent q < 0 := by
    linarith [(strictGrowthExponent_bounds q).2]
  have hm := ((eventWeight_integrable q
    (strictGrowthExponent q-decayExponent q) hrate).mul_prod hw).const_mul (C*D)
  apply hm.mono' (futureTestDensity_measurable q branch b a X k phi hphi).aestronglyMeasurable
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
  by_cases ht : 0 ≤ z.1.1-z.2.1
  · have hb := mul_le_mul (hK (z.1.1-z.2.1) z.2.2 z.1.2 ht)
      (hJ z.1.1 z.1.2 hz) (norm_nonneg _)
      (mul_nonneg hC (Real.exp_pos _).le)
    have h := mul_le_mul_of_nonneg_left hb (norm_nonneg (phi z.2))
    rw [futureTestDensity, norm_mul, norm_mul]
    apply h.trans_eq
    dsimp only [eventWeight, w]
    simp only [sub_mul, mul_sub, neg_mul, Real.exp_sub, Real.exp_neg]
    ring
  · have hneg : z.1.1-z.2.1 < 0 := lt_of_not_ge ht
    rw [futureTestDensity,
      full_kernel_negative q branch _ z.2.2 z.1.2 X k hneg,
      zero_mul, mul_zero, norm_zero]
    dsimp only [eventWeight, w]
    positivity

private theorem futureTestDensity_source_integral (q : XiZeroCopy)
    (branch b : Bool) (a : ℂ) (X k : ℝ) (phi : Event → ℂ) (r : Event) :
    (∫ p : Event, futureTestDensity q branch b a X k phi (p,r) ∂eventMeasure) =
      fullFutureResponse q branch b a r.1 r.2 X k * phi r := by
  rw [fullFutureResponse, ← integral_mul_const]
  apply integral_congr_ae
  exact ae_of_all _ (fun p => by
    simp only [futureTestDensity,directedFullDensity,if_true]
    ring)

private theorem futureTestDensity_target_integral (q : XiZeroCopy)
    (branch b : Bool) (a : ℂ) (X k : ℝ) (phi : Event → ℂ) (p : Event) :
    (∫ r : Event, futureTestDensity q branch b a X k phi (p,r)) =
      timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
        ∫ r : Event,
          angularDirichletKernel q branch (p.1-r.1) r.2 p.2 X k * phi r := by
  have he (r : Event) : futureTestDensity q branch b a X k phi (p,r) =
      timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
        (angularDirichletKernel q branch (p.1-r.1) r.2 p.2 X k * phi r) := by
    unfold futureTestDensity
    ring
  simp_rw [he]
  exact integral_const_mul _ _

/-- The admitted infinite original source can be transposed through every
continuous compact physical target test for the literal full future response.
No angular field or source leg is replaced by the native kernel. -/
theorem fullFutureResponse_test_fubini (q : XiZeroCopy)
    (branch b : Bool) (a : ℂ) (X k : ℝ) (phi : Event → ℂ)
    (hphi : Continuous phi) (hc : HasCompactSupport phi) :
    (∫ r : Event, fullFutureResponse q branch b a r.1 r.2 X k * phi r) =
      ∫ p : Event, timeReducedCoefficient (physicalRate q b) a p.1 p.2 *
        (∫ r : Event,
          angularDirichletKernel q branch (p.1-r.1) r.2 p.2 X k * phi r)
        ∂eventMeasure := by
  have hi := futureTestDensity_integrable q branch b a X k phi hphi hc
  have h := integral_integral_swap
    (f := fun p r => futureTestDensity q branch b a X k phi (p,r)) hi
  simpa only [futureTestDensity_source_integral,
    futureTestDensity_target_integral] using h.symm

end

end RHTower.D4BMFullAngularCausalPeierls
