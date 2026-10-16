import GaloisForLFunctions.RHTower.CHMDStationaryGroundPotential

/-!
# Complete stationary pullback graph

This graph uses the original mass space and the translation-invariant Levy
edge measure. Its literal edge coordinate is the difference of theta times
the source. Almost-everywhere closedness gives a complete Hilbert space.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump

def stationaryMeasure : Measure (ℝ × ℝ) :=
  archBase.withDensity (fun e => ENNReal.ofReal (archLevyDensity e.1))

theorem nonsingular_stationary_left :
    Measure.QuasiMeasurePreserving left stationaryMeasure massMeasure :=
  (Measure.quasiMeasurePreserving_snd.mono_left
    (withDensity_absolutelyContinuous archBase _)).mono_right volume_absolutelyContinuous_mass

theorem nonsingular_stationary_right :
    Measure.QuasiMeasurePreserving right stationaryMeasure massMeasure := by
  have h := Measure.quasiMeasurePreserving_snd.comp
    (measurePreserving_prod_add (volume.restrict (Ioi (0 : ℝ))) volume).quasiMeasurePreserving
  have h' : Measure.QuasiMeasurePreserving right archBase volume := by
    change Measure.QuasiMeasurePreserving (fun e : ℝ × ℝ => e.2 + e.1)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) volume
    simpa only [right, Function.comp_def, add_comm] using h
  exact (h'.mono_left (withDensity_absolutelyContinuous archBase _)).mono_right
    volume_absolutelyContinuous_mass

theorem memLp_stationary_difference_iff {v : ℝ → ℝ} (hv : Measurable v) :
    MemLp (difference v) 2 stationaryMeasure ↔ Integrable (stationaryJump v) archBase := by
  rw [memLp_two_iff_integrable_sq (measurable_difference hv).aestronglyMeasurable,
    stationaryMeasure, integrable_weighted_iff archBase (w := fun e : ℝ × ℝ => archLevyDensity e.1)
      (measurable_archLevyDensity.comp measurable_fst)]
  · rfl
  · have ht : ∀ᵐ e ∂archBase, 0 < e.1 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
    exact ht.mono fun e he => (archLevyDensity_pos he).le

abbrev StationaryGroundCarrier := Carrier massMeasure stationaryMeasure

def stationaryGroundGraph : Submodule ℝ StationaryGroundCarrier where
  carrier := {p | p.snd =ᵐ[stationaryMeasure] difference (thetaProduct p.fst)}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℝ 2 stationaryMeasure,
      nonsingular_stationary_left.ae (Lp.coeFn_zero ℝ 2 massMeasure),
      nonsingular_stationary_right.ae (Lp.coeFn_zero ℝ 2 massMeasure)] with e he hl hr
    change (0 : Lp ℝ 2 stationaryMeasure) e =
      riemannKernelReal (left e) * (0 : Lp ℝ 2 massMeasure) (left e) -
        riemannKernelReal (right e) * (0 : Lp ℝ 2 massMeasure) (right e)
    simp only [he, hl, hr, Pi.zero_apply, mul_zero, sub_self]
  add_mem' := by
    intro p q hp hq
    filter_upwards [hp, hq, Lp.coeFn_add p.snd q.snd,
      nonsingular_stationary_left.ae (Lp.coeFn_add p.fst q.fst),
      nonsingular_stationary_right.ae (Lp.coeFn_add p.fst q.fst)] with e he hf ha hb hc
    change (p.snd + q.snd) e =
      riemannKernelReal (left e) * (p.fst + q.fst) (left e) -
        riemannKernelReal (right e) * (p.fst + q.fst) (right e)
    simp only [ha, hb, hc, Pi.add_apply, he, hf, difference, thetaProduct]
    ring
  smul_mem' := by
    intro c p hp
    filter_upwards [hp, Lp.coeFn_smul c p.snd,
      nonsingular_stationary_left.ae (Lp.coeFn_smul c p.fst),
      nonsingular_stationary_right.ae (Lp.coeFn_smul c p.fst)] with e he ha hb hc
    change (c • p.snd) e =
      riemannKernelReal (left e) * (c • p.fst) (left e) -
        riemannKernelReal (right e) * (c • p.fst) (right e)
    simp only [ha, hb, hc, Pi.smul_apply, smul_eq_mul, he, difference, thetaProduct]
    ring

theorem isClosed_stationaryGroundGraph :
    IsClosed (stationaryGroundGraph : Set StationaryGroundCarrier) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u p hu hp
  have hsource := ((WithLp.continuous_fst 2 _ _).tendsto p).comp hp
  have hedge := ((WithLp.continuous_snd 2 _ _).tendsto p).comp hp
  obtain ⟨ns, hns, hs⟩ := (tendstoInMeasure_of_tendsto_Lp hsource).exists_seq_tendsto_ae
  obtain ⟨ms, hms, he⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hedge.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hg : ∀ᵐ e ∂stationaryMeasure, ∀ n : ℕ,
      (u (ns (ms n))).snd e = difference (thetaProduct (u (ns (ms n))).fst) e :=
    ae_all_iff.mpr fun n => hu (ns (ms n))
  filter_upwards [nonsingular_stationary_left.ae hs, nonsingular_stationary_right.ae hs,
    he, hg] with e hleft hright hedge' hgraph
  apply tendsto_nhds_unique hedge'
  exact (((hleft.comp hms.tendsto_atTop).const_mul (riemannKernelReal (left e))).sub
    ((hright.comp hms.tendsto_atTop).const_mul (riemannKernelReal (right e)))).congr
      fun n => (hgraph n).symm

instance completeSpace_stationaryGroundGraph : CompleteSpace stationaryGroundGraph :=
  isClosed_stationaryGroundGraph.isComplete.completeSpace_coe

def stationaryGroundSourceMap : stationaryGroundGraph →L[ℝ] Lp ℝ 2 massMeasure :=
  (WithLp.fstL 2 ℝ _ _).comp stationaryGroundGraph.subtypeL

theorem stationaryGroundSourceMap_injective : Function.Injective stationaryGroundSourceMap := by
  intro p q hpq
  change p.val.fst = q.val.fst at hpq
  have heq : p.val.snd = q.val.snd := by
    apply Lp.ext
    filter_upwards [p.property, q.property] with e hp hq
    rw [hp, hq, hpq]
  apply Subtype.ext
  apply (WithLp.equiv 2 _).injective
  exact Prod.ext hpq heq

def stationaryGroundOfFunction (v : ℝ → ℝ) (hv : MemLp v 2 massMeasure)
    (hd : MemLp (difference (thetaProduct v)) 2 stationaryMeasure) : stationaryGroundGraph := by
  refine ⟨WithLp.toLp 2 (hv.toLp v, hd.toLp (difference (thetaProduct v))), ?_⟩
  filter_upwards [hd.coeFn_toLp, nonsingular_stationary_left.ae hv.coeFn_toLp,
    nonsingular_stationary_right.ae hv.coeFn_toLp] with e he hl hr
  change hd.toLp _ e = riemannKernelReal (left e) * hv.toLp v (left e) -
    riemannKernelReal (right e) * hv.toLp v (right e)
  rw [he, hl, hr]
  rfl

theorem stationaryGround_difference_memLp (p : stationaryGroundGraph) :
    MemLp (difference (thetaProduct p.val.fst)) 2 stationaryMeasure :=
  (Lp.memLp p.val.snd).ae_eq p.property

end RHTower.CHMDDoobGraph
