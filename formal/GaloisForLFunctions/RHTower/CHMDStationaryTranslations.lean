import GaloisForLFunctions.RHTower.CHMDStationaryVolumeGraph
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
# Translation covariance of the actual stationary generator

Translation preserves the literal source-difference graph, including its
singular Levy edge measure. Riesz uniqueness then makes the resolvent commute
with the strongly continuous translation group on ordinary Lebesgue L2.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump CHMDPolar

def stationaryTimeMeasure : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t => ENNReal.ofReal (archLevyDensity t))

theorem stationaryMeasure_eq_prod : stationaryMeasure = stationaryTimeMeasure.prod volume :=
  (prod_withDensity_left (measurable_archLevyDensity.ennreal_ofReal)).symm

def stationaryEdgeShift (a : ℝ) (e : ℝ × ℝ) : ℝ × ℝ := (e.1, e.2 + a)

theorem stationaryEdgeShift_preserving (a : ℝ) :
    MeasurePreserving (stationaryEdgeShift a) stationaryMeasure stationaryMeasure := by
  rw [stationaryMeasure_eq_prod]
  letI : SFinite stationaryTimeMeasure := by unfold stationaryTimeMeasure; infer_instance
  exact (MeasurePreserving.id stationaryTimeMeasure).prod (measurePreserving_add_right volume a)

def volumeTranslate (a : ℝ) : StationaryVolumeSpace →ₗᵢ[ℝ] StationaryVolumeSpace :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x => x + a) (measurePreserving_add_right volume a)

def stationaryEdgeTranslate (a : ℝ) : Lp ℝ 2 stationaryMeasure →ₗᵢ[ℝ] Lp ℝ 2 stationaryMeasure :=
  Lp.compMeasurePreservingₗᵢ ℝ (stationaryEdgeShift a) (stationaryEdgeShift_preserving a)

theorem volumeTranslate_ae (a : ℝ) (u : StationaryVolumeSpace) :
    volumeTranslate a u =ᵐ[volume] (fun x => u (x + a)) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume a)

theorem stationaryEdgeTranslate_ae (a : ℝ) (u : Lp ℝ 2 stationaryMeasure) :
    stationaryEdgeTranslate a u =ᵐ[stationaryMeasure] (fun e => u (stationaryEdgeShift a e)) :=
  Lp.coeFn_compMeasurePreserving u (stationaryEdgeShift_preserving a)

theorem volumeTranslate_zero (u : StationaryVolumeSpace) : volumeTranslate 0 u = u := by
  apply Lp.ext
  simpa only [add_zero] using volumeTranslate_ae 0 u

theorem volumeTranslate_add (a b : ℝ) (u : StationaryVolumeSpace) :
    volumeTranslate a (volumeTranslate b u) = volumeTranslate (a + b) u := by
  apply Lp.ext
  filter_upwards [volumeTranslate_ae a (volumeTranslate b u), volumeTranslate_ae (a + b) u,
    (measurePreserving_add_right volume a).quasiMeasurePreserving.ae (volumeTranslate_ae b u)]
    with x ha hab hb
  change volumeTranslate b u (x + a) = u (x + a + b) at hb
  rw [ha, hb, hab, add_assoc]

theorem volumeTranslate_neg_cancel (a : ℝ) (u : StationaryVolumeSpace) :
    volumeTranslate a (volumeTranslate (-a) u) = u := by
  rw [volumeTranslate_add, add_neg_cancel, volumeTranslate_zero]

theorem volumeTranslate_inner (a : ℝ) (u v : StationaryVolumeSpace) :
    ⟪volumeTranslate a u, v⟫_ℝ = ⟪u, volumeTranslate (-a) v⟫_ℝ := by
  nth_rw 1 [← volumeTranslate_neg_cancel a v]
  exact (volumeTranslate a).inner_map_map u (volumeTranslate (-a) v)

theorem continuous_volumeTranslate (u : StationaryVolumeSpace) :
    Continuous (fun a => volumeTranslate a u) := by
  let g : ℝ → C(ℝ, ℝ) := fun a => ⟨fun x => x + a, continuous_id.add continuous_const⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_snd.add continuous_fst)
  exact continuous_const.compMeasurePreservingLp hg
    (fun a => measurePreserving_add_right volume a) (by norm_num)

def volumeGraphTranslate (a : ℝ) (p : StationaryVolumeGraph) : StationaryVolumeGraph := by
  refine ⟨WithLp.toLp 2 (volumeTranslate a p.val.fst, stationaryEdgeTranslate a p.val.snd), ?_⟩
  filter_upwards [stationaryEdgeTranslate_ae a p.val.snd,
    (stationaryEdgeShift_preserving a).quasiMeasurePreserving.ae p.property,
    nonsingular_stationary_volume_left.ae (volumeTranslate_ae a p.val.fst),
    nonsingular_stationary_volume_right.ae (volumeTranslate_ae a p.val.fst)] with e he hp hl hr
  change stationaryEdgeTranslate a p.val.snd e =
    volumeTranslate a p.val.fst (left e) - volumeTranslate a p.val.fst (right e)
  rw [he, hl, hr]
  simpa only [stationaryEdgeShift, left, right, add_right_comm] using hp

theorem volumeGraphTranslate_source (a : ℝ) (p : StationaryVolumeGraph) :
    volumeSourceMap (volumeGraphTranslate a p) = volumeTranslate a (volumeSourceMap p) := rfl

theorem volumeGraphTranslate_inner (a : ℝ) (p q : StationaryVolumeGraph) :
    ⟪volumeGraphTranslate a p, volumeGraphTranslate a q⟫_ℝ = ⟪p, q⟫_ℝ := by
  rw [volume_graph_inner, volume_graph_inner, volumeGraphTranslate_source,
    volumeGraphTranslate_source, (volumeTranslate a).inner_map_map]
  congr 1
  exact (stationaryEdgeTranslate a).inner_map_map p.val.snd q.val.snd

theorem volumeGraphTranslate_neg_cancel (a : ℝ) (p : StationaryVolumeGraph) :
    volumeGraphTranslate a (volumeGraphTranslate (-a) p) = p := by
  apply volumeSourceMap_injective
  rw [volumeGraphTranslate_source, volumeGraphTranslate_source, volumeTranslate_neg_cancel]

theorem volumeRieszLift_translate (a : ℝ) (w : StationaryVolumeSpace) :
    volumeRieszLift (volumeTranslate a w) = volumeGraphTranslate a (volumeRieszLift w) := by
  apply volumeRieszLift_unique
  intro q
  nth_rw 1 [← volumeGraphTranslate_neg_cancel a q]
  rw [volumeGraphTranslate_inner, inner_volumeRieszLift,
    volumeGraphTranslate_source, volumeTranslate_inner]

theorem volumeResolvent_translate (a : ℝ) (w : StationaryVolumeSpace) :
    volumeResolvent (volumeTranslate a w) = volumeTranslate a (volumeResolvent w) := by
  change volumeSourceMap (volumeRieszLift (volumeTranslate a w)) = _
  rw [volumeRieszLift_translate, volumeGraphTranslate_source]
  rfl

end RHTower.CHMDDoobGraph
