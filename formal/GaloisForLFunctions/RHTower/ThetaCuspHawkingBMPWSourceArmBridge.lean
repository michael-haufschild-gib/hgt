import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPWTwoChartGoursat

/-!
# PW-B literal CTP to two-chart physical Goursat source

At each physical receiver, direct and reflected-image source arms are separately
integrable. The original event wedge, both causal gates, and both Jacobian
factors give an exact quarter-weighted difference of finite Goursat arms.
Fubini then identifies the actual crossed-ordering and completed CTP scalars
with their two-chart source expressions. No current-incidence, outer-limit,
PW-magnitude, or extinction claim is made here.
-/

open Complex MeasureTheory Set Topology
open scoped ENNReal

namespace RHTower.D4BMPWTwoChartGoursat
open D4BMFullSourceReciprocity D4BMGeneralTemporalTransposition
open D4BMFullAngularSourceReflection D4BMFullAngularReconstruction
open D4BMFullAngularCircle D4BMModularCore D4BMJointSource
open D4BMFullAngularGoursat

noncomputable section
set_option autoImplicit false

private theorem event_integral_null_chart (s y : ℝ) (F : Event → ℂ) :
    (∫ p : Event, F p ∂eventMeasure) =
      (1 / 2 : ℂ) * ∫ z : ℝ × ℝ,
        (Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ)).indicator F (pastVertex s y z) := by
  let S : Set Event := Ioi 0 ×ˢ Iio 0
  have hmap := integral_pastVertex s y (S.indicator F)
  have hevent : (∫ p : Event, F p ∂eventMeasure) =
      ∫ p : Event, S.indicator F p := by
    rw [eventMeasure, Measure.prod_restrict, ← Measure.volume_eq_prod,
      integral_indicator (measurableSet_Ioi.prod measurableSet_Iio)]
  rw [hevent]
  change (∫ p : Event, S.indicator F p) =
    (1 / 2 : ℂ) * ∫ z : ℝ × ℝ, S.indicator F (pastVertex s y z)
  linear_combination -hmap / 2

private theorem gate_local (u v : ℝ) :
    |(u-v)/2| ≤ (u+v)/2 ↔ 0 ≤ u ∧ 0 ≤ v := by
  rw [abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

def eventArm (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ)
    (r : Event) (η X k : ℝ) (p : Event) : ℂ :=
  physicalSource (physicalRate q b) a p *
    (if |p.2 - η| ≤ r.1 - p.1 then
      angularMean q branch
        (Real.arcosh (D4BMCausalKernel.invariant (r.1-p.1) p.2 η)) X k
      else 0) *
    physicalSource (physicalRate q c) d r

private theorem eventArm_chart (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (r : Event) (η X k : ℝ) (z : Event) :
    (Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ)).indicator
      (eventArm q branch b c a d r η X k)
      (pastVertex r.1 η z) =
      (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)).indicator
        (closedPhysicalArm q branch b c a d r η X k) z := by
  let p := pastVertex r.1 η z
  have ht : r.1 - p.1 = (z.1+z.2)/2 := by dsimp [p,pastVertex]; ring
  have hx : p.2 - η = (z.1-z.2)/2 := by dsimp [p,pastVertex]; ring
  by_cases hq : z ∈ Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)
  · rw [Set.indicator_of_mem hq]
    have hg : |p.2-η| ≤ r.1-p.1 := by
      rw [ht,hx,gate_local]
      exact hq
    by_cases hp : p ∈ Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ)
    · rw [Set.indicator_of_mem hp]
      simp only [eventArm, if_pos hg, closedPhysicalArm, nullPhysicalTest]
      rw [show (pastVertex r.1 η z) = p from rfl]
      have hi : 1 ≤ D4BMCausalKernel.invariant (r.1-p.1) p.2 η :=
        D4BMCausalKernel.invariant_causal ⟨r.1-p.1,p.2,η,hg⟩
      have hp2 : p.2 = η+(z.1-z.2)/2 := rfl
      rw [← ht, ← hp2, max_eq_right hi]
      ring
    · rw [Set.indicator_of_notMem hp]
      have hz : physicalSource (physicalRate q b) a p = 0 := by
        rw [physicalSource_eq_event_indicator]
        exact Set.indicator_of_notMem hp _
      simp [closedPhysicalArm, nullPhysicalTest, hz, p]
  · rw [Set.indicator_of_notMem hq]
    have hg : ¬ |p.2-η| ≤ r.1-p.1 := by
      rw [ht,hx,gate_local]
      exact hq
    by_cases hp : p ∈ Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ)
    · rw [Set.indicator_of_mem hp]
      simp [eventArm, hg]
    · rw [Set.indicator_of_notMem hp]

theorem eventArm_quadrant (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (r : Event) (η X k : ℝ) :
    (∫ p : Event, eventArm q branch b c a d r η X k p ∂eventMeasure) =
      (1/2 : ℂ) * ∫ z in Ici (0 : ℝ) ×ˢ Ici (0 : ℝ),
        closedPhysicalArm q branch b c a d r η X k z := by
  rw [event_integral_null_chart]
  congr 1
  rw [← integral_indicator (measurableSet_Ici.prod measurableSet_Ici)]
  apply integral_congr_ae
  exact ae_of_all _ (eventArm_chart q branch b c a d r η X k)

private theorem fullCircle_eq_eventArm_on_wedge (q : XiZeroCopy)
    (branch b c : Bool) (a d : ℂ) (X k : ℝ) (p r : Event)
    (hp : p ∈ Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ))
    (hr : r ∈ Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ)) :
    fullCircleSourcePairDensity q branch b c a d X k (p,r) =
      (eventArm q branch b c a d r r.2 X k p -
        eventArm q branch b c a d r (-r.2) X k p) / 2 := by
  have hpx : p.2 < 0 := hp.2
  have hrx : r.2 < 0 := hr.2
  simp only [fullCircleSourcePairDensity, angularDirichletKernel,
    eventArm, physicalSource, if_pos hpx, if_pos hrx, sub_neg_eq_add]
  ring

private theorem quadrant_arm_integrable (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (r : Event) (η X k : ℝ) (hr : 0 ≤ r.1) :
    Integrable ((Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)).indicator
      (closedPhysicalArm q branch b c a d r η X k)) := by
  let F := closedPhysicalArm q branch b c a d r η X k
  let R := 2 * r.1
  have hR : 0 ≤ R := by dsimp [R]; linarith
  have he : (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)).indicator F =
      (Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) R).indicator F := by
    funext z
    by_cases hq : z ∈ Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)
    · by_cases hb : z ∈ Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) R
      · simp only [Set.indicator_of_mem hq, Set.indicator_of_mem hb]
      · have hs : R ≤ z.1 + z.2 := by
          have hh : R < z.1 ∨ R < z.2 := by
            by_contra! hh
            exact hb ⟨⟨hq.1, hh.1⟩, ⟨hq.2, hh.2⟩⟩
          have hz1 : 0 ≤ z.1 := hq.1
          have hz2 : 0 ≤ z.2 := hq.2
          rcases hh with hh | hh <;> linarith
        rw [Set.indicator_of_mem hq, Set.indicator_of_notMem hb]
        exact closedPhysicalArm_zero_of_sum q branch b c a d r η X k z hs
    · have hb : z ∉ Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) R :=
        fun h => hq ⟨h.1.1, h.2.1⟩
      simp only [Set.indicator_of_notMem hq, Set.indicator_of_notMem hb]
  rw [he]
  apply (integrable_indicator_iff (measurableSet_Icc.prod measurableSet_Icc)).2
  exact (closedPhysicalArm_continuous q branch b c a d r η X k).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)

private def localPastChart (s y : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun := pastVertex s y
  invFun := fun p => (s-p.1+p.2-y,s-p.1-p.2+y)
  left_inv p := by ext <;> simp only [pastVertex] <;> ring
  right_inv p := by ext <;> simp only [pastVertex] <;> ring
  continuous_toFun := by unfold pastVertex; fun_prop
  continuous_invFun := by fun_prop

private theorem eventArm_integrable (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (r : Event) (η X k : ℝ) (hr : 0 ≤ r.1) :
    Integrable (eventArm q branch b c a d r η X k) eventMeasure := by
  let S : Set Event := Ioi 0 ×ˢ Iio 0
  have hi : Integrable (fun z : Event =>
      S.indicator (eventArm q branch b c a d r η X k)
        (pastVertex r.1 η z)) := by
    have he : (fun z : Event => S.indicator (eventArm q branch b c a d r η X k)
        (pastVertex r.1 η z)) =
        (Ici (0 : ℝ) ×ˢ Ici (0 : ℝ)).indicator
          (closedPhysicalArm q branch b c a d r η X k) := by
      funext z
      exact eventArm_chart q branch b c a d r η X k z
    rw [he]
    exact quadrant_arm_integrable q branch b c a d r η X k hr
  have h := ((localPastChart r.1 η).toMeasurableEquiv.measurableEmbedding.integrable_map_iff
    (μ := volume) (g := S.indicator (eventArm q branch b c a d r η X k))).mpr hi
  change Integrable (S.indicator (eventArm q branch b c a d r η X k))
    (Measure.map (pastVertex r.1 η) volume) at h
  rw [pastVertex_volume, integrable_smul_measure (by norm_num : (2:ℝ≥0∞)≠0)
    (by norm_num : (2:ℝ≥0∞)≠⊤)] at h
  rw [integrable_indicator_iff (measurableSet_Ioi.prod measurableSet_Iio)] at h
  change Integrable (eventArm q branch b c a d r η X k) (volume.restrict S) at h
  rw [eventMeasure, Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact h

theorem fullCircle_source_inner_twoChart (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) (r : Event)
    (hr : r ∈ Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ)) :
    (∫ p : Event, fullCircleSourcePairDensity q branch b c a d X k (p,r)
      ∂eventMeasure) =
      (1/4 : ℂ) *
        ((∫ z in Ici (0 : ℝ) ×ˢ Ici (0 : ℝ),
            closedPhysicalArm q branch b c a d r r.2 X k z) -
          ∫ z in Ici (0 : ℝ) ×ˢ Ici (0 : ℝ),
            closedPhysicalArm q branch b c a d r (-r.2) X k z) := by
  have hiD := eventArm_integrable q branch b c a d r r.2 X k (le_of_lt hr.1)
  have hiI := eventArm_integrable q branch b c a d r (-r.2) X k (le_of_lt hr.1)
  have hcongr :
      (∫ p : Event, fullCircleSourcePairDensity q branch b c a d X k (p,r)
        ∂eventMeasure) =
      ∫ p : Event, (eventArm q branch b c a d r r.2 X k p -
        eventArm q branch b c a d r (-r.2) X k p) / 2 ∂eventMeasure := by
    rw [eventMeasure, Measure.prod_restrict, ← Measure.volume_eq_prod]
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Iio)
    intro p hp
    exact fullCircle_eq_eventArm_on_wedge q branch b c a d X k p r hp hr
  calc
    _ = ∫ p : Event, (eventArm q branch b c a d r r.2 X k p -
        eventArm q branch b c a d r (-r.2) X k p) / 2 ∂eventMeasure := hcongr
    _ = ((∫ p : Event, eventArm q branch b c a d r r.2 X k p ∂eventMeasure) -
          (∫ p : Event, eventArm q branch b c a d r (-r.2) X k p ∂eventMeasure)) / 2 := by
      rw [integral_div, integral_sub hiD hiI]
    _ = _ := by
      rw [eventArm_quadrant, eventArm_quadrant]
      ring

theorem fullCircle_source_inner_goursat (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) (r : Event)
    (hr : r ∈ Ioi (0 : ℝ) ×ˢ Iio (0 : ℝ)) :
    (∫ p : Event, fullCircleSourcePairDensity q branch b c a d X k (p,r)
      ∂eventMeasure) =
      (1/4 : ℂ) *
        (physicalArmGoursatRHS q branch b c a d r r.2 X k -
          physicalArmGoursatRHS q branch b c a d r (-r.2) X k) := by
  rw [fullCircle_source_inner_twoChart q branch b c a d X k r hr,
    physicalArm_quadrant_transposition q branch b c a d r r.2 X k (le_of_lt hr.1),
    physicalArm_quadrant_transposition q branch b c a d r (-r.2) X k (le_of_lt hr.1)]

theorem fullCircle_source_double_goursat (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) :
    (∫ z : Event × Event, fullCircleSourcePairDensity q branch b c a d X k z
      ∂eventMeasure.prod eventMeasure) =
      ∫ r : Event, (1/4 : ℂ) *
        (physicalArmGoursatRHS q branch b c a d r r.2 X k -
          physicalArmGoursatRHS q branch b c a d r (-r.2) X k)
        ∂eventMeasure := by
  have hi : Integrable (fullCircleSourcePairDensity q branch b c a d X k)
      (eventMeasure.prod eventMeasure) :=
    D4BMFullAngularCausalPeierls.fullSourcePairDensity_integrable q branch b c a d X k
  calc
    _ = ∫ r : Event, ∫ p : Event,
        fullCircleSourcePairDensity q branch b c a d X k (p,r)
        ∂eventMeasure ∂eventMeasure :=
          integral_prod_symm (μ := eventMeasure) (ν := eventMeasure) _ hi
    _ = _ := by
      rw [eventMeasure, Measure.prod_restrict, ← Measure.volume_eq_prod]
      apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Iio)
      intro r hr
      simpa only [eventMeasure, Measure.prod_restrict, ← Measure.volume_eq_prod] using
        (fullCircle_source_inner_goursat q branch b c a d X k r hr)

/-- The exact literal crossed-ordering CTP scalar after both physical Goursat
transpositions. -/
def goursatBranch (q : XiZeroCopy) (branch : Bool)
    (a : ℂ) (X k : ℝ) : ℂ :=
  (∫ r : Event, (1/4 : ℂ) *
      (physicalArmGoursatRHS q branch false true a a r r.2 X k -
        physicalArmGoursatRHS q branch false true a a r (-r.2) X k)
      ∂eventMeasure) -
    ∫ r : Event, (1/4 : ℂ) *
      (physicalArmGoursatRHS q branch true false a a r r.2 X k -
        physicalArmGoursatRHS q branch true false a a r (-r.2) X k)
      ∂eventMeasure

theorem fullCircleCrossBranchCausalPair_eq_goursatBranch (q : XiZeroCopy)
    (branch : Bool) (a : ℂ) (X k : ℝ) :
    fullCircleCrossBranchCausalPair q branch a X k =
      goursatBranch q branch a X k := by
  unfold fullCircleCrossBranchCausalPair goursatBranch
  rw [fullCircle_source_double_goursat, fullCircle_source_double_goursat]

theorem fullCircleCrossBranchSymmetricCausalPair_eq_goursat (q : XiZeroCopy)
    (a : ℂ) (X k : ℝ) :
    fullCircleCrossBranchSymmetricCausalPair q a X k =
      goursatBranch q true a X k + goursatBranch q false a X k := by
  unfold fullCircleCrossBranchSymmetricCausalPair
  rw [fullCircleCrossBranchCausalPair_eq_goursatBranch,
    fullCircleCrossBranchCausalPair_eq_goursatBranch]


end
end RHTower.D4BMPWTwoChartGoursat
