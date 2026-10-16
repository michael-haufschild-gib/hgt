import GaloisForLFunctions.RHTower.CHMDStationaryGroundGraph
import GaloisForLFunctions.RHTower.CHMDArchimedeanDomain

/-!
# Exact equivalence of the maximal archimedean and stationary pullback forms

The source coordinate is unchanged. The complete graph topologies agree, and
the graph inner products differ by precisely the bounded ground-state potential.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump

def archGroundRestriction (p : ArchGraph) : stationaryGroundGraph :=
  stationaryGroundOfFunction p.val.fst (Lp.memLp p.val.fst)
    ((memLp_stationary_difference_iff
      (measurable_thetaProduct (Lp.stronglyMeasurable p.val.fst).measurable)).mpr
        ((memLp_arch_difference_iff_stationary (Lp.stronglyMeasurable p.val.fst).measurable
          (Lp.memLp p.val.fst)).mp (arch_difference_memLp p)))

theorem archGroundRestriction_source (p : ArchGraph) :
    stationaryGroundSourceMap (archGroundRestriction p) = archSourceMap p :=
  Lp.toLp_coeFn p.val.fst (Lp.memLp p.val.fst)

def stationaryGroundExtension (p : stationaryGroundGraph) : ArchGraph :=
  ofFunction massMeasure archMeasure left right nonsingular_arch_left nonsingular_arch_right
    p.val.fst (Lp.memLp p.val.fst)
    ((memLp_arch_difference_iff_stationary (Lp.stronglyMeasurable p.val.fst).measurable
      (Lp.memLp p.val.fst)).mpr
      ((memLp_stationary_difference_iff
        (measurable_thetaProduct (Lp.stronglyMeasurable p.val.fst).measurable)).mp
          (stationaryGround_difference_memLp p)))

theorem stationaryGroundExtension_source (p : stationaryGroundGraph) :
    archSourceMap (stationaryGroundExtension p) = stationaryGroundSourceMap p :=
  Lp.toLp_coeFn p.val.fst (Lp.memLp p.val.fst)

def archGroundLinearEquiv : ArchGraph ≃ₗ[ℝ] stationaryGroundGraph where
  toFun := archGroundRestriction
  invFun := stationaryGroundExtension
  map_add' p q := by
    apply stationaryGroundSourceMap_injective
    simp only [archGroundRestriction_source, map_add]
  map_smul' c p := by
    apply stationaryGroundSourceMap_injective
    simp only [archGroundRestriction_source, map_smul, RingHom.id_apply]
  left_inv p := by
    apply archSourceMap_injective
    rw [stationaryGroundExtension_source, archGroundRestriction_source]
  right_inv p := by
    apply stationaryGroundSourceMap_injective
    rw [archGroundRestriction_source, stationaryGroundExtension_source]

theorem continuous_archGroundLinearEquiv : Continuous archGroundLinearEquiv := by
  apply archGroundLinearEquiv.toLinearMap.continuous_of_isClosed_graph
  have heq : (archGroundLinearEquiv.toLinearMap.graph : Set (ArchGraph × stationaryGroundGraph)) =
      {p | archSourceMap p.1 = stationaryGroundSourceMap p.2} := by
    ext p
    change p.2 = archGroundRestriction p.1 ↔ archSourceMap p.1 = stationaryGroundSourceMap p.2
    constructor
    · intro h
      rw [h, archGroundRestriction_source]
    · intro h
      apply stationaryGroundSourceMap_injective
      rw [archGroundRestriction_source]
      exact h.symm
  rw [heq]
  exact isClosed_eq (archSourceMap.continuous.comp continuous_fst)
    (stationaryGroundSourceMap.continuous.comp continuous_snd)

def archGroundEquiv : ArchGraph ≃L[ℝ] stationaryGroundGraph :=
  archGroundLinearEquiv.toContinuousLinearEquivOfContinuous continuous_archGroundLinearEquiv

theorem archGroundEquiv_source (p : ArchGraph) :
    (archGroundEquiv p).val.fst = p.val.fst := archGroundRestriction_source p

theorem archGroundEquiv_symm_source (p : stationaryGroundGraph) :
    (archGroundEquiv.symm p).val.fst = p.val.fst := stationaryGroundExtension_source p

theorem full_source_domain_eq_stationary : sourceMap.range = stationaryGroundSourceMap.range := by
  rw [full_source_domain_eq_arch]
  ext w
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨archGroundEquiv p, archGroundEquiv_source p⟩
  · rintro ⟨p, rfl⟩
    exact ⟨archGroundEquiv.symm p, archGroundEquiv_symm_source p⟩

theorem stationaryGround_edge_energy (p : stationaryGroundGraph) :
    ‖p.val.snd‖ ^ 2 = stationaryEnergy (thetaProduct p.val.fst) := by
  have hn := norm_toLp_sq stationaryMeasure (Lp.memLp p.val.snd)
  rw [Lp.toLp_coeFn] at hn
  rw [hn]
  have heq : (∫ e, p.val.snd e ^ 2 ∂stationaryMeasure) =
      ∫ e, difference (thetaProduct p.val.fst) e ^ 2 ∂stationaryMeasure := by
    apply integral_congr_ae
    filter_upwards [p.property] with e he
    rw [he]
  rw [heq]
  change (∫ e, difference (thetaProduct p.val.fst) e ^ 2
    ∂archBase.withDensity (fun e => ENNReal.ofReal (archLevyDensity e.1))) = _
  rw [integral_weighted archBase (w := fun e : ℝ × ℝ => archLevyDensity e.1)
    (measurable_archLevyDensity.comp measurable_fst)]
  · rfl
  · have ht : ∀ᵐ e ∂archBase, 0 < e.1 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
    exact ht.mono fun e he => (archLevyDensity_pos he).le

theorem archGround_edge_energy_decomposition (p : ArchGraph) :
    ‖p.val.snd‖ ^ 2 = ‖(archGroundEquiv p).val.snd‖ ^ 2 +
      ⟪groundPotentialOperator (archSourceMap p), archSourceMap p⟫_ℝ := by
  rw [graph_edge_norm_sq_integral archMeasure nonsingular_arch_left nonsingular_arch_right,
    stationaryGround_edge_energy, archGroundEquiv_source, inner_groundPotentialOperator_self]
  exact arch_energy_eq_stationary_add_potential (Lp.stronglyMeasurable p.val.fst).measurable
    (Lp.memLp p.val.fst) (arch_difference_memLp p)

theorem archGround_norm_decomposition (p : ArchGraph) :
    ‖p‖ ^ 2 = ‖archGroundEquiv p‖ ^ 2 +
      ⟪groundPotentialOperator (archSourceMap p), archSourceMap p⟫_ℝ := by
  change ‖p.val‖ ^ 2 = ‖(archGroundEquiv p).val‖ ^ 2 + _
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2,
    archGroundEquiv_source, archGround_edge_energy_decomposition]
  ring

theorem archGround_inner_decomposition (p q : ArchGraph) :
    ⟪p, q⟫_ℝ = ⟪archGroundEquiv p, archGroundEquiv q⟫_ℝ +
      ⟪groundPotentialOperator (archSourceMap p), archSourceMap q⟫_ℝ := by
  have h := archGround_norm_decomposition (p + q)
  simp only [map_add, norm_add_sq_real, inner_add_left, inner_add_right] at h
  rw [archGround_norm_decomposition p, archGround_norm_decomposition q] at h
  have hs : ⟪groundPotentialOperator (archSourceMap q), archSourceMap p⟫_ℝ =
      ⟪groundPotentialOperator (archSourceMap p), archSourceMap q⟫_ℝ := by
    rw [groundPotentialOperator_symmetric, real_inner_comm]
  linarith

end RHTower.CHMDDoobGraph
