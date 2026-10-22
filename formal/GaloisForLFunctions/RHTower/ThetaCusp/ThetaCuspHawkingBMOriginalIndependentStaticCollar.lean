import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalRestoredStaticGeometry
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalMetricCorner

/-! Independent original onset, static-time and horizon removal. -/
open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalIndependentStaticCollar
open D4BMOriginalRestoredTemporalContacts D4BMOriginalRestoredStaticGeometry
noncomputable section
set_option autoImplicit false

/-- Onset, horizon depth and terminal time tend independently. -/
abbrev cutoffFilter : Filter ((ℝ×ℝ)×ℝ) := ((𝓝[>] (0:ℝ))×ˢatTop)×ˢatTop

def triangleRegion (a B T : ℝ) : Set (ℝ×ℝ) :=
  {v | a<v.2 ∧ v.1 ≤ B ∧ v.2+v.1/2 ≤ T}

private theorem triangle_measurable (a B T : ℝ) : MeasurableSet (triangleRegion a B T) := by
  have ht : MeasurableSet {v : ℝ×ℝ | v.2+v.1/2 ≤ T} :=
    measurableSet_le (by fun_prop) measurable_const
  exact (measurableSet_lt measurable_const measurable_snd).inter
    ((measurableSet_le measurable_fst measurable_const).inter ht)

private theorem triangle_integral_eq (F : ℝ×ℝ→ℂ) (a A B T : ℝ) (ha : 0 ≤ a)
    (hAB : A ≤ B) (hF : IntegrableOn F (Ioi A ×ˢ Ioi (0:ℝ))) :
    staticTriangle F a A B T=
      (∫ v in Ioi A ×ˢ Ioi (0:ℝ),(triangleRegion a B T).indicator F v)/2 := by
  have hFa : IntegrableOn F (Ioc A B ×ˢ Ioi a) := hF.mono_set
    (Set.prod_mono (fun _ h => h.1) (Ioi_subset_Ioi ha))
  rw [(static_triangle_fubini F a A B T hAB hFa).2]
  congr 1
  rw [setIntegral_indicator (triangle_measurable a B T),
    setIntegral_indicator (measurableSet_le (by fun_prop) measurable_const)]
  have hs : (Ioc A B ×ˢ Ioi a) ∩ {v : ℝ×ℝ | v.2+v.1/2 ≤ T}=
      (Ioi A ×ˢ Ioi (0:ℝ)) ∩ triangleRegion a B T := by
    ext v
    change ((A<v.1 ∧ v.1 ≤ B) ∧ a<v.2) ∧ v.2+v.1/2 ≤ T ↔
      (A<v.1 ∧ 0<v.2) ∧ a<v.2 ∧ v.1 ≤ B ∧ v.2+v.1/2 ≤ T
    constructor
    · intro h
      exact ⟨⟨h.1.1.1,ha.trans_lt h.1.2⟩,h.1.2,h.1.1.2,h.2⟩
    · intro h
      exact ⟨⟨⟨h.1.1,h.2.2.1⟩,h.2.1⟩,h.2.2.2⟩
  rw [hs]

/-- Absolute product admission gives independent exhaustion of the literal
static-time triangle, including the positive-onset boundary. -/
theorem integrable_triangle_limit (F : ℝ×ℝ→ℂ) (A : ℝ)
    (hF : IntegrableOn F (Ioi A ×ˢ Ioi (0:ℝ))) :
    Tendsto (fun z : (ℝ×ℝ)×ℝ => staticTriangle F z.1.1 A z.1.2 z.2) cutoffFilter
      (𝓝 ((∫ v in Ioi A ×ˢ Ioi (0:ℝ),F v)/2)) := by
  have ha : Tendsto (fun z : (ℝ×ℝ)×ℝ => z.1.1) cutoffFilter (𝓝[>] (0:ℝ)) :=
    tendsto_fst.comp tendsto_fst
  have hB : Tendsto (fun z : (ℝ×ℝ)×ℝ => z.1.2) cutoffFilter atTop :=
    tendsto_snd.comp tendsto_fst
  have hT : Tendsto (fun z : (ℝ×ℝ)×ℝ => z.2) cutoffFilter atTop := tendsto_snd
  have ht : Tendsto (fun z : (ℝ×ℝ)×ℝ =>
      ∫ v in Ioi A ×ˢ Ioi (0:ℝ),(triangleRegion z.1.1 z.1.2 z.2).indicator F v)
      cutoffFilter (𝓝 (∫ v in Ioi A ×ˢ Ioi (0:ℝ),F v)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun v => ‖F v‖)
    · exact Eventually.of_forall (fun z => hF.aestronglyMeasurable.indicator (triangle_measurable _ _ _))
    · exact Eventually.of_forall (fun _ => ae_of_all _ (fun v => norm_indicator_le_norm_self F v))
    · exact hF.norm
    · filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with v hv
      apply tendsto_const_nhds.congr'
      filter_upwards [ha.eventually ((eventually_lt_nhds hv.2).filter_mono nhdsWithin_le_nhds),
        hB.eventually (eventually_ge_atTop v.1),hT.eventually (eventually_ge_atTop (v.2+v.1/2))]
        with z hza hzb hzt
      exact (Set.indicator_of_mem (show v∈triangleRegion z.1.1 z.1.2 z.2 from ⟨hza,hzb,hzt⟩) F).symm
  apply (ht.div_const (2:ℂ)).congr'
  filter_upwards [ha.eventually self_mem_nhdsWithin,hB.eventually (eventually_ge_atTop A)] with z hza hzb
  exact (triangle_integral_eq F z.1.1 A z.1.2 z.2 hza.le hzb hF).symm

private theorem tail_mass_onset (U : ℝ→ℂ) (hU : IntegrableOn U (Ioi (0:ℝ))) :
    Tendsto (tailMass U) (𝓝[>] (0:ℝ)) (𝓝 (tailMass U 0)) := by
  have ht : Tendsto (fun a : ℝ => ∫ p in Ioi (0:ℝ),(Ioi a).indicator U p)
      (𝓝[>] (0:ℝ)) (𝓝 (tailMass U 0)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun p => ‖U p‖)
    · exact Eventually.of_forall (fun _ => hU.aestronglyMeasurable.indicator measurableSet_Ioi)
    · exact Eventually.of_forall (fun _ => ae_of_all _ (fun p => norm_indicator_le_norm_self U p))
    · exact hU.norm
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
      apply tendsto_const_nhds.congr'
      filter_upwards [(eventually_lt_nhds hp).filter_mono nhdsWithin_le_nhds] with a ha
      exact (Set.indicator_of_mem ha U).symm
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [setIntegral_indicator measurableSet_Ioi]
  have he : Ioi (0:ℝ) ∩ Ioi a=Ioi a := by
    ext p
    have ha' : (0:ℝ)<a := ha
    exact ⟨fun h => h.2,fun h => ⟨ha'.trans h,h⟩⟩
  rw [he]
  rfl

/-- Corrected original triangle with its finite-onset mass, original static
clock and both actual temporal corners. -/
def contactTriangle (F : ℝ×ℝ→ℂ) (U : ℝ→ℂ) (a A B T : ℝ) : ℂ :=
  staticTriangle F a A B T-((max a T-max a (T-B/2):ℝ):ℂ)*tailMass U a+
    tailCorner U (max a (T-B/2))-tailCorner U a

private theorem static_triangle_add (R : ℝ×ℝ→ℂ) (U : ℝ→ℂ)
    (A : ℝ) (hR : IntegrableOn R (Ioi A ×ˢ Ioi (0:ℝ)))
    (hU : IntegrableOn U (Ioi (0:ℝ)))
    (a B T : ℝ) (ha : 0 ≤ a) (hAB : A ≤ B) :
    staticTriangle (fun v => R v+U v.2) a A B T=
      staticTriangle R a A B T+staticTriangle (fun v => U v.2) a A B T := by
  have hr : IntegrableOn R (Ioc A B ×ˢ Ioi a) := hR.mono_set
    (Set.prod_mono (fun _ h => h.1) (Ioi_subset_Ioi ha))
  have h1 : IntegrableOn (fun _ : ℝ => (1:ℂ)) (Ioc A B) :=
    integrableOn_const (by simp [Real.volume_Ioc])
  have hu : IntegrableOn (fun v : ℝ×ℝ => U v.2) (Ioc A B ×ˢ Ioi a) := by
    simpa only [IntegrableOn,Measure.prod_restrict,Measure.volume_eq_prod,one_mul] using
      h1.mul_prod (hU.mono_set (Ioi_subset_Ioi ha))
  have hsum : IntegrableOn (fun v : ℝ×ℝ => R v+U v.2) (Ioc A B ×ˢ Ioi a) := by
    simpa only [Pi.add_apply] using! hr.add hu
  rw [(static_triangle_fubini (fun v => R v+U v.2) a A B T hAB hsum).2,
    (static_triangle_fubini R a A B T hAB hr).2,
    (static_triangle_fubini (fun v => U v.2) a A B T hAB hu).2,← add_div]
  congr 1
  let E := {v : ℝ×ℝ | v.2+v.1/2 ≤ T}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have he : E.indicator (fun v => R v+U v.2)=
      fun v => E.indicator R v+E.indicator (fun v => U v.2) v := by
    funext v
    by_cases h : v∈E <;> simp [h]
  change (∫ v in Ioc A B ×ˢ Ioi a,E.indicator (fun v => R v+U v.2) v)=_
  rw [he,integral_add (hr.indicator hE) (hu.indicator hE)]

private theorem contact_triangle_split (R : ℝ×ℝ→ℂ) (U : ℝ→ℂ) (A : ℝ)
    (hR : IntegrableOn R (Ioi A ×ˢ Ioi (0:ℝ)))
    (hU : IntegrableOn U (Ioi (0:ℝ)))
    (hM : IntegrableOn (fun p : ℝ => (p:ℂ)*U p) (Ioi (0:ℝ)))
    (a B T : ℝ) (ha : 0 ≤ a) (hAB : A ≤ B) :
    contactTriangle (fun v => R v+U v.2) U a A B T=
      staticTriangle R a A B T+
        ((max a (T-A/2)-max a T:ℝ):ℂ)*tailMass U a+
          tailCorner U (max a (T-A/2))-tailCorner U a := by
  unfold contactTriangle
  rw [static_triangle_add R U A hR hU a B T ha hAB,
    static_triangle_two_corners U hU hM a A B T ha hAB]
  push_cast
  ring

/-- Finite-onset mass and the lower moving corner cancel exactly. The full
corrected physical triangle has a limit under independent cutoffs. -/
theorem contact_triangle_limit (R : ℝ×ℝ→ℂ) (U : ℝ→ℂ) (A : ℝ)
    (hR : IntegrableOn R (Ioi A ×ˢ Ioi (0:ℝ)))
    (hU : IntegrableOn U (Ioi (0:ℝ)))
    (hM : IntegrableOn (fun p : ℝ => (p:ℂ)*U p) (Ioi (0:ℝ))) :
    Tendsto (fun z : (ℝ×ℝ)×ℝ => contactTriangle (fun v => R v+U v.2) U z.1.1 A z.1.2 z.2)
      cutoffFilter (𝓝 ((∫ v in Ioi A ×ˢ Ioi (0:ℝ),R v)/2-
        ((A/2:ℝ):ℂ)*tailMass U 0-tailCorner U 0)) := by
  have ha : Tendsto (fun z : (ℝ×ℝ)×ℝ => z.1.1) cutoffFilter (𝓝[>] (0:ℝ)) :=
    tendsto_fst.comp tendsto_fst
  have hB : Tendsto (fun z : (ℝ×ℝ)×ℝ => z.1.2) cutoffFilter atTop :=
    tendsto_snd.comp tendsto_fst
  have hT : Tendsto (fun z : (ℝ×ℝ)×ℝ => z.2) cutoffFilter atTop := tendsto_snd
  have hS : Tendsto (fun z : (ℝ×ℝ)×ℝ => max z.1.1 (z.2-A/2)) cutoffFilter atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hT.eventually (eventually_ge_atTop (b+A/2))] with z hz
    exact le_trans (by linarith) (le_max_right _ _)
  have hr := integrable_triangle_limit R A hR
  have hm := (tail_mass_onset U hU).comp ha
  have hcs := (tail_corner_terminal U hU hM).comp hS
  have hca := (tail_corner_onset U hU hM).comp ha
  have ht := ((hr.sub (hm.const_mul ((A/2:ℝ):ℂ))).add hcs).sub hca
  simp only [add_zero] at ht
  apply ht.congr'
  have ha1 : ∀ᶠ a : ℝ in 𝓝[>] (0:ℝ),a<1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [ha.eventually self_mem_nhdsWithin,ha.eventually ha1,
    hB.eventually (eventually_ge_atTop A),hT.eventually (eventually_ge_atTop (1+|A/2|))]
    with z hza hza1 hzb hzt
  rw [contact_triangle_split R U A hR hU hM _ _ _ hza.le hzb]
  have he : max z.1.1 (z.2-A/2)-max z.1.1 z.2= -A/2 := by
    rw [max_eq_right (by linarith [le_abs_self (A/2)]),
      max_eq_right (by linarith [abs_nonneg (A/2)])]
    ring
  dsimp only [Function.comp_def]
  rw [he]
  push_cast
  ring

open D4BMModularCore D4BMJointSource D4BMOriginalTemporalCorner D4BMOriginalMetricCorner

/-- The actual complete original metric collar, with its source-derived
mass and two original contacts, admits independent onset/time/horizon removal.
Both original source and forcing remainders are included. -/
theorem original_metric_independent_contacts (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2<w.re) (hwi : w.im≠0) :
    ∃ A : ℝ,0<A ∧
      Tendsto (fun z : (ℝ×ℝ)×ℝ => contactTriangle (collarDensity q br amp w)
        (leadingDensity q br amp w) z.1.1 A z.1.2 z.2) cutoffFilter
        (𝓝 ((∫ v in Ioi A ×ˢ Ioi (0:ℝ),metricRemainder q br amp w v)/2-
          ((A/2:ℝ):ℂ)*tailMass (leadingDensity q br amp w) 0-
            tailCorner (leadingDensity q br amp w) 0)) := by
  have hq := (xi_divisor_support_re_mem_open_unit q.1).1
  have hwr : (D4BMOriginalCirclePeriod.readerExponent q).re<w.re := by
    norm_num [D4BMOriginalCirclePeriod.readerExponent]
    linarith
  obtain ⟨A,hA,hR⟩ := original_metric_remainder_integrable q br amp w hwi hwr
  have hU : IntegrableOn (leadingDensity q br amp w) (Ioi (0:ℝ)) := by
    simpa only [pow_zero,one_mul] using leading_moment_integrable q br amp w 0 hwr
  have hM : IntegrableOn (fun p : ℝ => (p:ℂ)*leadingDensity q br amp w p) (Ioi (0:ℝ)) := by
    simpa only [pow_one] using leading_moment_integrable q br amp w 1 hwr
  refine ⟨A,hA,?_⟩
  have h := contact_triangle_limit (metricRemainder q br amp w) (leadingDensity q br amp w) A hR hU hM
  have he : (fun v => metricRemainder q br amp w v+leadingDensity q br amp w v.2)=
      collarDensity q br amp w := by
    funext v
    exact sub_add_cancel _ _
  rwa [he] at h

/-- The full original angular-restored metric period on the physical static
radial window, in the unchanged tortoise coordinate and measure. -/
def originalMetricTriangle (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a A B T : ℝ) : ℂ :=
  (∫ L in A..B,((D4BMJointWave.tortoiseRadius (-L/2):ℂ)^(2 : ℕ)-1)*
    D4BMOriginalMetricTimePeriod.restoredMetricTime q br true amp w a
      (max a (T-L/2)) (D4BMJointWave.tortoiseRadius (-L/2)))/2

/-- The two representations coincide at every original finite positive
onset, including the empty part of the static window. -/
theorem original_metric_triangle_identity (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (a A B T : ℝ) (ha : 0<a) (hA : 0<A) (hAB : A ≤ B) :
    staticTriangle (collarDensity q br amp w) a A B T=
      originalMetricTriangle q br amp w a A B T := by
  unfold staticTriangle originalMetricTriangle
  congr 1
  apply intervalIntegral.integral_congr
  intro L hL
  have hL' : L∈Icc A B := by simpa only [uIcc_of_le hAB] using hL
  exact original_metric_collar_integral q br amp w L a (max a (T-L/2))
    (hA.trans_le hL'.1) ha (le_max_left _ _)

def originalMetricContacts (q : XiZeroCopy) (br : Bool) (amp w : ℂ) (a A B T : ℝ) : ℂ :=
  originalMetricTriangle q br amp w a A B T-
    ((max a T-max a (T-B/2):ℝ):ℂ)*tailMass (leadingDensity q br amp w) a+
      tailCorner (leadingDensity q br amp w) (max a (T-B/2))-
        tailCorner (leadingDensity q br amp w) a

/-- Independent cutoff removal for the complete original metric period,
with its actual finite-onset mass and the two retained moving contacts. -/
theorem original_metric_period_independent_limit (q : XiZeroCopy) (br : Bool) (amp w : ℂ)
    (hw : 3/2<w.re) (hwi : w.im≠0) :
    ∃ A : ℝ,0<A ∧
      Tendsto (fun z : (ℝ×ℝ)×ℝ => originalMetricContacts q br amp w z.1.1 A z.1.2 z.2)
        cutoffFilter (𝓝 ((∫ v in Ioi A ×ˢ Ioi (0:ℝ),metricRemainder q br amp w v)/2-
          ((A/2:ℝ):ℂ)*tailMass (leadingDensity q br amp w) 0-
            tailCorner (leadingDensity q br amp w) 0)) := by
  obtain ⟨A,hA,h⟩ := original_metric_independent_contacts q br amp w hw hwi
  refine ⟨A,hA,h.congr' ?_⟩
  have ha : Tendsto (fun z : (ℝ×ℝ)×ℝ => z.1.1) cutoffFilter (𝓝[>] (0:ℝ)) :=
    tendsto_fst.comp tendsto_fst
  have hB : Tendsto (fun z : (ℝ×ℝ)×ℝ => z.1.2) cutoffFilter atTop := tendsto_snd.comp tendsto_fst
  filter_upwards [ha.eventually self_mem_nhdsWithin,hB.eventually (eventually_ge_atTop A)] with z hza hzb
  unfold contactTriangle originalMetricContacts
  rw [original_metric_triangle_identity q br amp w _ _ _ _ hza hA hzb]

end
end RHTower.D4BMOriginalIndependentStaticCollar
