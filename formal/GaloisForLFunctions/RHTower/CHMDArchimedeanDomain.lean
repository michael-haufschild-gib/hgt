import GaloisForLFunctions.RHTower.CHMDBoundedPrimeGenerator
import GaloisForLFunctions.RHTower.CHMDSignedGraphPolarization

/-!
# Exact removal of arithmetic from the closed form domain

The full graph and the archimedean graph have the same source domain and are
continuously linearly isomorphic by the identity on sources. The complete prime
generator accounts exactly for the difference of their energies and graph norms.
This is a form-domain theorem; an operator-core theorem is not assumed.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump

abbrev ArchGraph := graph massMeasure archMeasure left right
  nonsingular_arch_left nonsingular_arch_right

def archSourceMap : ArchGraph →L[ℝ] Lp ℝ 2 massMeasure :=
  (WithLp.fstL 2 ℝ _ _).comp ArchGraph.subtypeL

theorem archSourceMap_injective : Function.Injective archSourceMap :=
  source_injective massMeasure archMeasure left right nonsingular_arch_left nonsingular_arch_right

theorem full_difference_memLp (p : SourceGraph) :
    MemLp (difference p.val.fst) 2 edgeMeasure := (Lp.memLp p.val.snd).ae_eq p.property

theorem arch_difference_memLp (p : ArchGraph) :
    MemLp (difference p.val.fst) 2 archMeasure := (Lp.memLp p.val.snd).ae_eq p.property

def archRestriction (p : SourceGraph) : ArchGraph :=
  ofFunction massMeasure archMeasure left right nonsingular_arch_left nonsingular_arch_right
    p.val.fst (Lp.memLp p.val.fst)
    ((memLp_full_difference_iff_arch (Lp.memLp p.val.fst)).mp (full_difference_memLp p))

theorem archRestriction_source (p : SourceGraph) :
    archSourceMap (archRestriction p) = sourceMap p := Lp.toLp_coeFn p.val.fst (Lp.memLp p.val.fst)

def arithmeticExtension (p : ArchGraph) : SourceGraph :=
  ofFunction massMeasure edgeMeasure left right nonsingular_left nonsingular_right
    p.val.fst (Lp.memLp p.val.fst)
    ((memLp_full_difference_iff_arch (Lp.memLp p.val.fst)).mpr (arch_difference_memLp p))

theorem arithmeticExtension_source (p : ArchGraph) :
    sourceMap (arithmeticExtension p) = archSourceMap p := Lp.toLp_coeFn p.val.fst (Lp.memLp p.val.fst)

def graphArchLinearEquiv : SourceGraph ≃ₗ[ℝ] ArchGraph where
  toFun := archRestriction
  invFun := arithmeticExtension
  map_add' p q := by
    apply archSourceMap_injective
    simp only [archRestriction_source, map_add]
  map_smul' c p := by
    apply archSourceMap_injective
    simp only [archRestriction_source, map_smul, RingHom.id_apply]
  left_inv p := by
    apply source_projection_injective
    change sourceMap (arithmeticExtension (archRestriction p)) = sourceMap p
    rw [arithmeticExtension_source, archRestriction_source]
  right_inv p := by
    apply archSourceMap_injective
    rw [archRestriction_source, arithmeticExtension_source]

theorem continuous_graphArchLinearEquiv : Continuous graphArchLinearEquiv := by
  apply graphArchLinearEquiv.toLinearMap.continuous_of_isClosed_graph
  have heq : (graphArchLinearEquiv.toLinearMap.graph : Set (SourceGraph × ArchGraph)) =
      {p | sourceMap p.1 = archSourceMap p.2} := by
    ext p
    change p.2 = archRestriction p.1 ↔ sourceMap p.1 = archSourceMap p.2
    constructor
    · intro h
      rw [h, archRestriction_source]
    · intro h
      apply archSourceMap_injective
      rw [archRestriction_source]
      exact h.symm
  rw [heq]
  exact isClosed_eq (sourceMap.continuous.comp continuous_fst)
    (archSourceMap.continuous.comp continuous_snd)

/-- Identity on sources, with both complete graph topologies retained. -/
def graphArchEquiv : SourceGraph ≃L[ℝ] ArchGraph :=
  graphArchLinearEquiv.toContinuousLinearEquivOfContinuous continuous_graphArchLinearEquiv

theorem graphArchEquiv_source (p : SourceGraph) :
    (graphArchEquiv p).val.fst = p.val.fst := archRestriction_source p

theorem graphArchEquiv_symm_source (p : ArchGraph) :
    (graphArchEquiv.symm p).val.fst = p.val.fst := arithmeticExtension_source p

theorem full_source_domain_eq_arch : sourceMap.range = archSourceMap.range := by
  ext w
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨graphArchEquiv p, graphArchEquiv_source p⟩
  · rintro ⟨p, rfl⟩
    exact ⟨graphArchEquiv.symm p, graphArchEquiv_symm_source p⟩

theorem graph_edge_norm_sq_integral (κ : Measure (ℝ × ℝ))
    (hl : Measure.QuasiMeasurePreserving left κ massMeasure)
    (hr : Measure.QuasiMeasurePreserving right κ massMeasure)
    (p : graph massMeasure κ left right hl hr) :
    ‖p.val.snd‖ ^ 2 = ∫ e, difference p.val.fst e ^ 2 ∂κ := by
  have hn := CHMDClosedJump.norm_toLp_sq κ (Lp.memLp p.val.snd)
  rw [Lp.toLp_coeFn] at hn
  rw [hn]
  apply integral_congr_ae
  filter_upwards [p.property] with e he
  exact congrArg (fun x : ℝ => x ^ 2) he

theorem full_edge_energy_decomposition (p : SourceGraph) :
    ‖p.val.snd‖ ^ 2 = ‖(graphArchEquiv p).val.snd‖ ^ 2 +
      ⟪primeGenerator (sourceMap p), sourceMap p⟫_ℝ := by
  rw [graph_edge_norm_sq_integral edgeMeasure nonsingular_left nonsingular_right,
    graph_edge_norm_sq_integral archMeasure nonsingular_arch_left nonsingular_arch_right,
    graphArchEquiv_source, inner_primeGenerator_eq_integral]
  change (∫ e, difference p.val.fst e ^ 2 ∂edgeMeasure) =
    (∫ e, difference p.val.fst e ^ 2 ∂archMeasure) +
      ∫ e, difference p.val.fst e * difference p.val.fst e ∂allPrimeMeasure
  simp only [← pow_two]
  exact integral_add_measure (full_difference_memLp p).integrable_sq.left_of_add_measure
    (full_difference_memLp p).integrable_sq.right_of_add_measure

theorem full_signed_energy_decomposition (p : SourceGraph) :
    sourceEnergy p =
      energy massMeasure archMeasure left right nonsingular_arch_left nonsingular_arch_right
        (graphArchEquiv p) + ⟪primeGenerator (sourceMap p), sourceMap p⟫_ℝ := by
  unfold sourceEnergy energy
  rw [graphArchEquiv_source, full_edge_energy_decomposition]
  ring

theorem full_graph_norm_decomposition (p : SourceGraph) :
    ‖p‖ ^ 2 = ‖graphArchEquiv p‖ ^ 2 +
      ⟪primeGenerator (sourceMap p), sourceMap p⟫_ℝ := by
  change ‖p.val‖ ^ 2 = ‖(graphArchEquiv p).val‖ ^ 2 + _
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2,
    graphArchEquiv_source, full_edge_energy_decomposition]
  ring

theorem full_graph_inner_decomposition (p q : SourceGraph) :
    ⟪p, q⟫_ℝ = ⟪graphArchEquiv p, graphArchEquiv q⟫_ℝ +
      ⟪primeGenerator (sourceMap p), sourceMap q⟫_ℝ := by
  have h := full_graph_norm_decomposition (p + q)
  have hp := full_graph_norm_decomposition p
  have hq := full_graph_norm_decomposition q
  have hsym : ⟪primeGenerator (sourceMap q), sourceMap p⟫_ℝ =
      ⟪primeGenerator (sourceMap p), sourceMap q⟫_ℝ := by
    rw [inner_primeGenerator, inner_primeGenerator, real_inner_comm]
  simp only [map_add, norm_add_sq_real, inner_add_left, inner_add_right] at h
  rw [hsym] at h
  linarith

end RHTower.CHMDDoobGraph
