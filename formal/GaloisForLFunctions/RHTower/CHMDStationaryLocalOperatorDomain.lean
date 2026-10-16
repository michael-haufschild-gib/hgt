import GaloisForLFunctions.RHTower.CHMDStationaryLocalTransform

/-!
# Local equivalence of the actual operator domains

Every compactly supported ground-generator domain vector has its theta
transform in the ordinary stationary generator domain. The reverse transfer
is valid whenever the theta transform is admitted. Both statements follow
from identities on the complete form domains, not only compact tests.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump CHMDPolar

def volumeDomainLift (u : volumeGenerator.domain) : StationaryVolumeGraph :=
  volumeRieszLift ((u : StationaryVolumeSpace) + volumeGenerator u)

theorem volumeDomainLift_source (u : volumeGenerator.domain) :
    volumeSourceMap (volumeDomainLift u) = u :=
  generatorOfResolvent_identity volumeResolvent volumeResolvent_injective u

theorem volumeDomainLift_form (u : volumeGenerator.domain) (q : StationaryVolumeGraph) :
    ⟪volumeGenerator u, volumeSourceMap q⟫_ℝ = ⟪(volumeDomainLift u).val.snd, q.val.snd⟫_ℝ := by
  have h := volumeGenerator_form ((u : StationaryVolumeSpace) + volumeGenerator u) q
  have hi : volumeResolvent ((u : StationaryVolumeSpace) + volumeGenerator u) = u :=
    generatorOfResolvent_identity volumeResolvent volumeResolvent_injective u
  rw [volumeGenerator_resolvent, hi, add_sub_cancel_left] at h
  exact h

def stationaryDomainLift (u : stationaryGenerator.domain) : stationaryGroundGraph :=
  stationaryRieszLift ((u : MassSpace) + stationaryGenerator u)

theorem stationaryDomainLift_source (u : stationaryGenerator.domain) :
    stationaryGroundSourceMap (stationaryDomainLift u) = u :=
  generatorOfResolvent_identity stationaryResolvent stationaryResolvent_injective u

theorem stationaryDomainLift_form (u : stationaryGenerator.domain) (q : stationaryGroundGraph) :
    ⟪stationaryGenerator u, stationaryGroundSourceMap q⟫_ℝ =
      ⟪(stationaryDomainLift u).val.snd, q.val.snd⟫_ℝ := by
  have h := stationaryGenerator_form ((u : MassSpace) + stationaryGenerator u) q
  have hi : stationaryResolvent ((u : MassSpace) + stationaryGenerator u) = u :=
    generatorOfResolvent_identity stationaryResolvent stationaryResolvent_injective u
  rw [stationaryGenerator_resolvent, hi, add_sub_cancel_left] at h
  exact h

theorem volume_form_resolvent (p : StationaryVolumeGraph) (w : StationaryVolumeSpace)
    (h : ∀ q : StationaryVolumeGraph, ⟪w, volumeSourceMap q⟫_ℝ = ⟪p.val.snd, q.val.snd⟫_ℝ) :
    volumeResolvent (volumeSourceMap p + w) = volumeSourceMap p := by
  have hr : volumeRieszLift (volumeSourceMap p + w) = p := by
    apply volumeRieszLift_unique
    intro q
    rw [volume_graph_inner, inner_add_left, h]
  exact congrArg volumeSourceMap hr

theorem volume_form_mem_domain (p : StationaryVolumeGraph) (w : StationaryVolumeSpace)
    (h : ∀ q : StationaryVolumeGraph, ⟪w, volumeSourceMap q⟫_ℝ = ⟪p.val.snd, q.val.snd⟫_ℝ) :
    volumeSourceMap p ∈ volumeGenerator.domain :=
  ⟨volumeSourceMap p + w, volume_form_resolvent p w h⟩

theorem volume_form_generator (p : StationaryVolumeGraph) (w : StationaryVolumeSpace)
    (h : ∀ q : StationaryVolumeGraph, ⟪w, volumeSourceMap q⟫_ℝ = ⟪p.val.snd, q.val.snd⟫_ℝ)
    (hu : volumeSourceMap p ∈ volumeGenerator.domain) :
    volumeGenerator ⟨volumeSourceMap p, hu⟩ = w := by
  have h1 := generatorOfResolvent_identity volumeResolvent volumeResolvent_injective
    (⟨volumeSourceMap p, hu⟩ : volumeGenerator.domain)
  exact add_left_cancel (volumeResolvent_injective (h1.trans (volume_form_resolvent p w h).symm))

theorem stationary_form_resolvent (p : stationaryGroundGraph) (w : MassSpace)
    (h : ∀ q : stationaryGroundGraph,
      ⟪w, stationaryGroundSourceMap q⟫_ℝ = ⟪p.val.snd, q.val.snd⟫_ℝ) :
    stationaryResolvent (stationaryGroundSourceMap p + w) = stationaryGroundSourceMap p := by
  have hr : stationaryRieszLift (stationaryGroundSourceMap p + w) = p := by
    apply stationaryRieszLift_unique
    intro q
    rw [Submodule.coe_inner, WithLp.prod_inner_apply, inner_add_left, h]
    rfl
  exact congrArg stationaryGroundSourceMap hr

theorem stationary_form_mem_domain (p : stationaryGroundGraph) (w : MassSpace)
    (h : ∀ q : stationaryGroundGraph,
      ⟪w, stationaryGroundSourceMap q⟫_ℝ = ⟪p.val.snd, q.val.snd⟫_ℝ) :
    stationaryGroundSourceMap p ∈ stationaryGenerator.domain :=
  ⟨stationaryGroundSourceMap p + w, stationary_form_resolvent p w h⟩

theorem stationary_form_generator (p : stationaryGroundGraph) (w : MassSpace)
    (h : ∀ q : stationaryGroundGraph,
      ⟪w, stationaryGroundSourceMap q⟫_ℝ = ⟪p.val.snd, q.val.snd⟫_ℝ)
    (hu : stationaryGroundSourceMap p ∈ stationaryGenerator.domain) :
    stationaryGenerator ⟨stationaryGroundSourceMap p, hu⟩ = w := by
  have h1 := generatorOfResolvent_identity stationaryResolvent stationaryResolvent_injective
    (⟨stationaryGroundSourceMap p, hu⟩ : stationaryGenerator.domain)
  exact add_left_cancel (stationaryResolvent_injective (h1.trans (stationary_form_resolvent p w h).symm))

theorem volumeCutoff_form (n : ℕ) (u : volumeGenerator.domain) (q : StationaryVolumeGraph) :
    ⟪volumeCutoff n (volumeGenerator u) + volumeCutoffCommutator n u, volumeSourceMap q⟫_ℝ =
      ⟪(volumeGraphCutoff n (volumeDomainLift u)).val.snd, q.val.snd⟫_ℝ := by
  have h := volumeGraphCutoff_edge_pairing n (volumeDomainLift u) q
  have hf := volumeDomainLift_form u (volumeGraphCutoff n q)
  rw [volumeDomainLift_source] at h
  rw [volumeGraphCutoff_source, ← volumeCutoff_symmetric] at hf
  rw [inner_add_left]
  linarith

theorem volumeCutoff_mem_domain (n : ℕ) (u : volumeGenerator.domain) :
    volumeCutoff n u ∈ volumeGenerator.domain := by
  have h := volume_form_mem_domain (volumeGraphCutoff n (volumeDomainLift u))
    (volumeCutoff n (volumeGenerator u) + volumeCutoffCommutator n u) (volumeCutoff_form n u)
  rwa [volumeGraphCutoff_source, volumeDomainLift_source] at h

def volumeGeneratorCutoff (n : ℕ) (u : volumeGenerator.domain) : volumeGenerator.domain :=
  ⟨volumeCutoff n u, volumeCutoff_mem_domain n u⟩

theorem volumeGeneratorCutoff_apply (n : ℕ) (u : volumeGenerator.domain) :
    volumeGenerator (volumeGeneratorCutoff n u) =
      volumeCutoff n (volumeGenerator u) + volumeCutoffCommutator n u := by
  have h := volume_form_resolvent (volumeGraphCutoff n (volumeDomainLift u))
    (volumeCutoff n (volumeGenerator u) + volumeCutoffCommutator n u) (volumeCutoff_form n u)
  rw [volumeGraphCutoff_source, volumeDomainLift_source] at h
  have h1 := generatorOfResolvent_identity volumeResolvent volumeResolvent_injective
    (volumeGeneratorCutoff n u)
  exact add_left_cancel (volumeResolvent_injective (h1.trans h.symm))

def volumeGroundLift (u : MassSpace) (p : StationaryVolumeGraph)
    (hp : volumeSourceMap p = thetaToVolume u) : stationaryGroundGraph := by
  refine ⟨WithLp.toLp 2 (u, p.val.snd), ?_⟩
  have he := p.property
  change p.val.snd =ᵐ[stationaryMeasure] difference (volumeSourceMap p) at he
  rw [hp] at he
  filter_upwards [he, nonsingular_stationary_volume_left.ae (thetaToVolume_ae u),
    nonsingular_stationary_volume_right.ae (thetaToVolume_ae u)] with e he hl hr
  change p.val.snd e = difference (thetaProduct u) e
  simpa only [difference, hl, hr] using he

theorem stationary_of_volume_form (u : MassSpace) (f : volumeGenerator.domain)
    (hf : (f : StationaryVolumeSpace) = thetaToVolume u) (q : stationaryGroundGraph) :
    ⟪thetaToVolume.adjoint (volumeGenerator f), stationaryGroundSourceMap q⟫_ℝ =
      ⟪(volumeGroundLift u (volumeDomainLift f) ((volumeDomainLift_source f).trans hf)).val.snd,
        q.val.snd⟫_ℝ := by
  rw [thetaToVolume.adjoint_inner_left]
  have h := volumeDomainLift_form f (groundToVolume q)
  rw [groundToVolume_source, groundToVolume_edge] at h
  exact h

theorem stationary_of_volume_mem_domain (u : MassSpace) (f : volumeGenerator.domain)
    (hf : (f : StationaryVolumeSpace) = thetaToVolume u) : u ∈ stationaryGenerator.domain :=
  stationary_form_mem_domain
    (volumeGroundLift u (volumeDomainLift f) ((volumeDomainLift_source f).trans hf))
    (thetaToVolume.adjoint (volumeGenerator f)) (stationary_of_volume_form u f hf)

theorem stationary_of_volume_apply (u : stationaryGenerator.domain) (f : volumeGenerator.domain)
    (hf : (f : StationaryVolumeSpace) = thetaToVolume u) :
    stationaryGenerator u = thetaToVolume.adjoint (volumeGenerator f) :=
  stationary_form_generator
    (volumeGroundLift u (volumeDomainLift f) ((volumeDomainLift_source f).trans hf))
    (thetaToVolume.adjoint (volumeGenerator f)) (stationary_of_volume_form u f hf) u.property

theorem thetaToVolume_cutoff (n : ℕ) (u : MassSpace) :
    thetaToVolume (massCutoff n u) = volumeCutoff n (thetaToVolume u) := by
  rw [← localInverse_thetaToVolume n u, thetaToVolume_localInverse]

theorem localized_volume_form (n : ℕ) (u : stationaryGenerator.domain)
    (hu : massCutoff n u = u) (q : StationaryVolumeGraph) :
    ⟪(localThetaInverse n).adjoint (stationaryGenerator u) +
      volumeCutoffCommutator n (thetaToVolume u), volumeSourceMap q⟫_ℝ =
    ⟪(groundToVolume (stationaryDomainLift u)).val.snd, q.val.snd⟫_ℝ := by
  let p := groundToVolume (stationaryDomainLift u)
  have hs : volumeSourceMap p = thetaToVolume u := by
    rw [groundToVolume_source, stationaryDomainLift_source]
  have hc : volumeGraphCutoff n p = p := by
    apply volumeSourceMap_injective
    rw [volumeGraphCutoff_source, hs, ← thetaToVolume_cutoff, hu]
  have h := volumeGraphCutoff_edge_pairing n p q
  rw [hc, hs] at h
  have hg := stationaryDomainLift_form u (localToGround n q)
  rw [localToGround_source, localToGround_edge] at hg
  change ⟪stationaryGenerator u, localThetaInverse n (volumeSourceMap q)⟫_ℝ =
    ⟪p.val.snd, (volumeGraphCutoff n q).val.snd⟫_ℝ at hg
  rw [inner_add_left, (localThetaInverse n).adjoint_inner_left]
  change _ = ⟪p.val.snd, q.val.snd⟫_ℝ
  linarith

theorem localized_theta_mem_volume_domain (n : ℕ) (u : stationaryGenerator.domain)
    (hu : massCutoff n u = u) : thetaToVolume u ∈ volumeGenerator.domain := by
  have h := volume_form_mem_domain (groundToVolume (stationaryDomainLift u))
    ((localThetaInverse n).adjoint (stationaryGenerator u) + volumeCutoffCommutator n (thetaToVolume u))
    (localized_volume_form n u hu)
  rwa [groundToVolume_source, stationaryDomainLift_source] at h

end RHTower.CHMDDoobGraph
