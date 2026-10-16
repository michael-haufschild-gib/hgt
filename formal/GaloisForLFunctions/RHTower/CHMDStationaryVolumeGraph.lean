import GaloisForLFunctions.RHTower.CHMDCompactSupportOperatorCore

/-!
# The actual stationary Levy generator on ordinary Lebesgue L2

The graph is the literal translation difference for CHMD's `archLevyDensity`.
Its dense source projection gives an injective resolvent and a self-adjoint
nonnegative generator. No identification with the Gamma-clock kernel is used.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump CHMDPolar

abbrev StationaryVolumeSpace := Lp ℝ 2 (volume : Measure ℝ)

theorem nonsingular_stationary_volume_left :
    Measure.QuasiMeasurePreserving left stationaryMeasure (volume : Measure ℝ) :=
  nonsingular_stationary_left.mono_right (withDensity_absolutelyContinuous volume _)

theorem nonsingular_stationary_volume_right :
    Measure.QuasiMeasurePreserving right stationaryMeasure (volume : Measure ℝ) :=
  nonsingular_stationary_right.mono_right (withDensity_absolutelyContinuous volume _)

abbrev StationaryVolumeGraph := graph (volume : Measure ℝ) stationaryMeasure left right
  nonsingular_stationary_volume_left nonsingular_stationary_volume_right

def volumeSourceMap : StationaryVolumeGraph →L[ℝ] StationaryVolumeSpace :=
  (WithLp.fstL 2 ℝ _ _).comp StationaryVolumeGraph.subtypeL

theorem volumeSourceMap_injective : Function.Injective volumeSourceMap :=
  source_injective volume stationaryMeasure left right
    nonsingular_stationary_volume_left nonsingular_stationary_volume_right

theorem compact_memLp_volume {v : ℝ → ℝ} (hv : Continuous v) (hc : HasCompactSupport v) :
    MemLp v 2 (volume : Measure ℝ) := by
  rw [memLp_two_iff_integrable_sq hv.aestronglyMeasurable]
  have hs : HasCompactSupport (fun x => v x ^ 2) :=
    hc.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
  exact (hv.pow 2).integrable_of_hasCompactSupport hs

theorem compact_memLp_stationary {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hc : HasCompactSupport v) :
    MemLp (difference v) 2 stationaryMeasure :=
  (memLp_stationary_difference_iff hv.continuous.measurable).mpr
    (integrable_stationaryJump hv.continuous.measurable hc (compact_memLp_volume hv.continuous hc)
      (compact_memLp_difference hv hc))

def volumeCompactLift (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hc : HasCompactSupport v) :
    StationaryVolumeGraph :=
  ofFunction volume stationaryMeasure left right
    nonsingular_stationary_volume_left nonsingular_stationary_volume_right v
    (compact_memLp_volume hv.continuous hc) (compact_memLp_stationary hv hc)

theorem dense_volumeSourceMap_range : Dense (volumeSourceMap.range : Set StationaryVolumeSpace) := by
  apply (Lp.dense_hasCompactSupport_contDiff (F := ℝ) (μ := (volume : Measure ℝ)) (p := 2)
    (by norm_num)).mono
  rintro u ⟨v, huv, hc, hs⟩
  refine ⟨volumeCompactLift v (hs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hc, ?_⟩
  apply Lp.ext
  exact (compact_memLp_volume hs.continuous hc).coeFn_toLp.trans huv.symm

def volumeRieszLift : StationaryVolumeSpace →L[ℝ] StationaryVolumeGraph := volumeSourceMap.adjoint

theorem inner_volumeRieszLift (w : StationaryVolumeSpace) (q : StationaryVolumeGraph) :
    ⟪volumeRieszLift w, q⟫_ℝ = ⟪w, volumeSourceMap q⟫_ℝ :=
  volumeSourceMap.adjoint_inner_left q w

theorem volumeRieszLift_unique {w : StationaryVolumeSpace} {p : StationaryVolumeGraph}
    (h : ∀ q : StationaryVolumeGraph, ⟪p, q⟫_ℝ = ⟪w, volumeSourceMap q⟫_ℝ) :
    volumeRieszLift w = p := by
  apply ext_inner_right ℝ
  intro q
  rw [inner_volumeRieszLift, h]

def volumeResolvent : StationaryVolumeSpace →L[ℝ] StationaryVolumeSpace :=
  volumeSourceMap.comp volumeRieszLift

theorem volumeResolvent_isPositive : volumeResolvent.IsPositive :=
  ContinuousLinearMap.isPositive_self_comp_adjoint volumeSourceMap

theorem volumeResolvent_isSelfAdjoint : IsSelfAdjoint volumeResolvent :=
  volumeResolvent_isPositive.isSelfAdjoint

theorem volumeResolvent_injective : Function.Injective volumeResolvent := by
  intro u v h
  have hr : volumeRieszLift u = volumeRieszLift v := volumeSourceMap_injective h
  apply dense_volumeSourceMap_range.eq_of_inner_left ℝ
  rintro _ ⟨q, rfl⟩
  exact (inner_volumeRieszLift u q).symm.trans
    ((congrArg (fun p => ⟪p, q⟫_ℝ) hr).trans (inner_volumeRieszLift v q))

def volumeGenerator : StationaryVolumeSpace →ₗ.[ℝ] StationaryVolumeSpace :=
  generatorOfResolvent volumeResolvent volumeResolvent_injective

theorem volumeGenerator_isSelfAdjoint : IsSelfAdjoint volumeGenerator :=
  generatorOfResolvent_isSelfAdjoint _ _ volumeResolvent_isSelfAdjoint

theorem volumeGenerator_isClosed : volumeGenerator.IsClosed := volumeGenerator_isSelfAdjoint.isClosed

theorem volumeGenerator_resolvent (w : StationaryVolumeSpace) :
    volumeGenerator ⟨volumeResolvent w, ⟨w, rfl⟩⟩ = w - volumeResolvent w :=
  generatorOfResolvent_apply _ _ w

theorem volume_graph_inner (p q : StationaryVolumeGraph) :
    ⟪p, q⟫_ℝ = ⟪volumeSourceMap p, volumeSourceMap q⟫_ℝ + ⟪p.val.snd, q.val.snd⟫_ℝ := by
  rw [Submodule.coe_inner, WithLp.prod_inner_apply]
  rfl

theorem volumeGenerator_form (w : StationaryVolumeSpace) (q : StationaryVolumeGraph) :
    ⟪volumeGenerator ⟨volumeResolvent w, ⟨w, rfl⟩⟩, volumeSourceMap q⟫_ℝ =
      ⟪(volumeRieszLift w).val.snd, q.val.snd⟫_ℝ := by
  have h := inner_volumeRieszLift w q
  rw [volume_graph_inner] at h
  rw [volumeGenerator_resolvent, inner_sub_left]
  change ⟪w, volumeSourceMap q⟫_ℝ - ⟪volumeSourceMap (volumeRieszLift w), volumeSourceMap q⟫_ℝ = _
  linarith

theorem volumeGenerator_nonneg (u : volumeGenerator.domain) :
    0 ≤ ⟪volumeGenerator u, (u : StationaryVolumeSpace)⟫_ℝ := by
  rcases u with ⟨u, hu⟩
  obtain ⟨w, rfl⟩ := hu
  have h := volumeGenerator_form w (volumeRieszLift w)
  change ⟪volumeGenerator ⟨volumeResolvent w, _⟩, volumeResolvent w⟫_ℝ = _ at h
  erw [h, real_inner_self_eq_norm_sq]
  positivity

def groundToVolume (p : stationaryGroundGraph) : StationaryVolumeGraph := by
  let hf := memLp_thetaProduct (Lp.stronglyMeasurable p.val.fst).measurable (Lp.memLp p.val.fst)
  refine ⟨WithLp.toLp 2 (hf.toLp (thetaProduct p.val.fst), p.val.snd), ?_⟩
  filter_upwards [p.property, nonsingular_stationary_volume_left.ae hf.coeFn_toLp,
    nonsingular_stationary_volume_right.ae hf.coeFn_toLp] with e he hl hr
  change p.val.snd e = hf.toLp _ (left e) - hf.toLp _ (right e)
  rw [hl, hr]
  exact he

theorem groundToVolume_source_ae (p : stationaryGroundGraph) :
    volumeSourceMap (groundToVolume p) =ᵐ[volume] thetaProduct p.val.fst :=
  (memLp_thetaProduct (Lp.stronglyMeasurable p.val.fst).measurable (Lp.memLp p.val.fst)).coeFn_toLp

theorem groundToVolume_edge (p : stationaryGroundGraph) : (groundToVolume p).val.snd = p.val.snd := rfl

end RHTower.CHMDDoobGraph
