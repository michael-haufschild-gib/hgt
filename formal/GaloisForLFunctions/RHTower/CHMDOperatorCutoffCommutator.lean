import GaloisForLFunctions.RHTower.CHMDOperatorCutoffForm

/-!
# Exact bounded cutoff commutator for the complete arithmetic form

The antisymmetric cutoff defect factors through two bounded endpoint maps in
the first-moment space. Arithmetic contributes its ordinary bounded-operator
commutator. Both defects converge strongly to zero.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump CHMDPolar

theorem cutoff_inner_realLp {η : Measure (ℝ × ℝ)} (u v : Lp ℝ 2 η) :
    ⟪u, v⟫_ℝ = ∫ e, u e * v e ∂η := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with e
  simp [mul_comm]

theorem cutoff_integrable_mul {η : Measure (ℝ × ℝ)} (u v : Lp ℝ 2 η) :
    Integrable (fun e => u e * v e) η := by
  simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using
    (L2.integrable_inner (𝕜 := ℝ) u v)

theorem archCutoffCommutator_inner (n : ℕ) (u v : MassSpace) :
    ⟪archCutoffCommutator n u, v⟫_ℝ =
      ∫ e, cutoffSlope n e * (u (right e) * v (left e) - u (left e) * v (right e))
        ∂archMomentMeasure := by
  change ⟪archMomentLeft.adjoint (cutoffSlopeOperator n (archMomentRight u)) -
    archMomentRight.adjoint (cutoffSlopeOperator n (archMomentLeft u)), v⟫_ℝ = _
  rw [inner_sub_left, archMomentLeft.adjoint_inner_left,
    archMomentRight.adjoint_inner_left, cutoff_inner_realLp, cutoff_inner_realLp,
    ← integral_sub (cutoff_integrable_mul _ _) (cutoff_integrable_mul _ _)]
  apply integral_congr_ae
  filter_upwards [cutoffSlopeOperator_ae n (archMomentRight u),
    cutoffSlopeOperator_ae n (archMomentLeft u), archMomentRight_ae u,
    archMomentLeft_ae u, archMomentLeft_ae v, archMomentRight_ae v] with e h1 h2 h3 h4 h5 h6
  simp only [Function.comp_apply] at *
  rw [h1, h2, h3, h4, h5, h6]
  ring

theorem archCutoff_edge_ae (n : ℕ) (p : ArchGraph) :
    (archCutoff n p).val.snd =ᵐ[archMeasure]
      difference (fun x => cutoff n x * p.val.fst x) :=
  (memLp_cutoff_arch n p).coeFn_toLp

theorem archCutoff_edge_pairing (n : ℕ) (p q : ArchGraph) :
    ⟪(archCutoff n p).val.snd, q.val.snd⟫_ℝ -
      ⟪p.val.snd, (archCutoff n q).val.snd⟫_ℝ =
        ⟪archCutoffCommutator n (archSourceMap p), archSourceMap q⟫_ℝ := by
  rw [cutoff_inner_realLp, cutoff_inner_realLp,
    ← integral_sub (cutoff_integrable_mul _ _) (cutoff_integrable_mul _ _),
    archCutoffCommutator_inner, integral_archMoment]
  have ht : ∀ᵐ e ∂archMeasure, 0 < e.1 :=
    (withDensity_absolutelyContinuous archBase _).ae_le archBase_fst_pos
  apply integral_congr_ae
  filter_upwards [archCutoff_edge_ae n p, archCutoff_edge_ae n q,
    p.property, q.property, ht] with e hp hq hpe hqe he
  change (archCutoff n p).val.snd e * q.val.snd e -
    p.val.snd e * (archCutoff n q).val.snd e =
      e.1 * (cutoffSlope n e *
        (p.val.fst (right e) * q.val.fst (left e) - p.val.fst (left e) * q.val.fst (right e)))
  rw [hp, hq, hpe, hqe]
  dsimp only [difference, cutoffSlope]
  field_simp [he.ne']
  ring

theorem arch_graph_inner (p q : ArchGraph) :
    ⟪p, q⟫_ℝ = ⟪archSourceMap p, archSourceMap q⟫_ℝ + ⟪p.val.snd, q.val.snd⟫_ℝ := by
  rw [Submodule.coe_inner, WithLp.prod_inner_apply]
  rfl

theorem archCutoff_pairing (n : ℕ) (p q : ArchGraph) :
    ⟪archCutoff n p, q⟫_ℝ - ⟪p, archCutoff n q⟫_ℝ =
      ⟪archCutoffCommutator n (archSourceMap p), archSourceMap q⟫_ℝ := by
  rw [arch_graph_inner, arch_graph_inner, archCutoff_source, archCutoff_source,
    massCutoff_symmetric]
  linarith [archCutoff_edge_pairing n p q]

def fullCutoff (n : ℕ) (p : SourceGraph) : SourceGraph :=
  graphArchEquiv.symm (archCutoff n (graphArchEquiv p))

theorem fullCutoff_arch (n : ℕ) (p : SourceGraph) :
    graphArchEquiv (fullCutoff n p) = archCutoff n (graphArchEquiv p) :=
  graphArchEquiv.apply_symm_apply _

theorem fullCutoff_source (n : ℕ) (p : SourceGraph) :
    sourceMap (fullCutoff n p) = massCutoff n (sourceMap p) := by
  change (graphArchEquiv.symm (archCutoff n (graphArchEquiv p))).val.fst = _
  rw [graphArchEquiv_symm_source]
  change archSourceMap (archCutoff n (graphArchEquiv p)) = _
  rw [archCutoff_source]
  congr 1
  exact graphArchEquiv_source p

def fullCutoffCommutator (n : ℕ) : MassSpace →L[ℝ] MassSpace :=
  archCutoffCommutator n + primeGenerator.comp (massCutoff n) -
    (massCutoff n).comp primeGenerator

theorem fullCutoffCommutator_inner (n : ℕ) (u v : MassSpace) :
    ⟪fullCutoffCommutator n u, v⟫_ℝ = ⟪archCutoffCommutator n u, v⟫_ℝ +
      ⟪primeGenerator (massCutoff n u), v⟫_ℝ - ⟪primeGenerator u, massCutoff n v⟫_ℝ := by
  change ⟪archCutoffCommutator n u + primeGenerator (massCutoff n u) -
    massCutoff n (primeGenerator u), v⟫_ℝ = _
  rw [inner_sub_left, inner_add_left, massCutoff_symmetric]

theorem fullCutoff_pairing (n : ℕ) (p q : SourceGraph) :
    ⟪fullCutoff n p, q⟫_ℝ - ⟪p, fullCutoff n q⟫_ℝ =
      ⟪fullCutoffCommutator n (sourceMap p), sourceMap q⟫_ℝ := by
  rw [full_graph_inner_decomposition, full_graph_inner_decomposition,
    fullCutoff_arch, fullCutoff_arch, fullCutoff_source, fullCutoff_source,
    fullCutoffCommutator_inner]
  have h := archCutoff_pairing n (graphArchEquiv p) (graphArchEquiv q)
  have hp : archSourceMap (graphArchEquiv p) = sourceMap p := graphArchEquiv_source p
  have hq : archSourceMap (graphArchEquiv q) = sourceMap q := graphArchEquiv_source q
  rw [hp, hq] at h
  linarith

theorem fullCutoffCommutator_tendsto (u : MassSpace) :
    Tendsto (fun n => fullCutoffCommutator n u) atTop (𝓝 0) := by
  have hp := (primeGenerator.continuous.tendsto u).comp (massCutoff_tendsto u)
  have hq := massCutoff_tendsto (primeGenerator u)
  change Tendsto (fun n => archCutoffCommutator n u + primeGenerator (massCutoff n u) -
    massCutoff n (primeGenerator u)) atTop (𝓝 0)
  simpa only [Function.comp_def, zero_add, sub_self] using
    ((archCutoffCommutator_tendsto u).add hp).sub hq

end RHTower.CHMDDoobGraph
