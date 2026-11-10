import GaloisForLFunctions.HyperbolicArakelovTheory.TheWeightedAdelicAdjacencyOnSquareSummableCharges
import Mathlib.Topology.MetricSpace.Contracting

/-!
# The positive square root of the adelic precision

An operator-norm contraction constructs the square root of the hyperbolic
spectral shift. The iteration preserves nonnegative charges, retaining
the order information needed for a positive hyperbolic Green kernel.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators Topology InnerProductSpace NNReal

namespace GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
open FullAdelic

abbrev ChargeOperator := ChargeSpace →L[ℝ] ChargeSpace

def rootScale : ℝ := Real.sqrt (edge + 1 / 4)
def rootRadius : ℝ := rootScale - 1 / 2

theorem rootScale_sq : rootScale ^ 2 = edge + 1 / 4 :=
  Real.sq_sqrt (by linarith only [edge_pos])

theorem rootScale_gt_half : (1 / 2 : ℝ) < rootScale := by
  have hn : 0 ≤ rootScale := Real.sqrt_nonneg _
  nlinarith only [rootScale_sq, edge_pos, hn]

theorem rootScale_pos : 0 < rootScale := lt_trans (by norm_num) rootScale_gt_half

theorem rootRadius_pos : 0 < rootRadius := sub_pos.mpr rootScale_gt_half

theorem rootRadius_identity : edge + rootRadius ^ 2 = 2 * rootScale * rootRadius := by
  unfold rootRadius
  nlinarith only [rootScale_sq]

/-- Iteration for the positive remainder `aI−√(a²I−A)`. -/
def rootStep (T : ChargeOperator) : ChargeOperator :=
  (2 * rootScale)⁻¹ • (adjacencyOperator + T * T)

theorem rootStep_norm_le (T : ChargeOperator) (hT : ‖T‖ ≤ rootRadius) :
    ‖rootStep T‖ ≤ rootRadius := by
  have ha : 0 < 2 * rootScale := mul_pos (by norm_num) rootScale_pos
  calc
    ‖rootStep T‖ = (2 * rootScale)⁻¹ * ‖adjacencyOperator + T * T‖ := by
      rw [rootStep, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
    _ ≤ (2 * rootScale)⁻¹ * (edge + rootRadius ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ha.le)
      exact (norm_add_le _ _).trans (add_le_add adjacencyOperator_norm_le
        ((norm_mul_le _ _).trans (by nlinarith only [hT, norm_nonneg T, rootRadius_pos])))
    _ = rootRadius := by rw [rootRadius_identity]; field_simp [rootScale_pos.ne']

theorem rootStep_dist_le (T U : ChargeOperator)
    (hT : ‖T‖ ≤ rootRadius) (hU : ‖U‖ ≤ rootRadius) :
    dist (rootStep T) (rootStep U) ≤ (rootRadius / rootScale) * dist T U := by
  have ha : 0 < 2 * rootScale := mul_pos (by norm_num) rootScale_pos
  have he : rootStep T - rootStep U =
      (2 * rootScale)⁻¹ • (T * (T - U) + (T - U) * U) := by
    rw [rootStep, rootStep, ← smul_sub]
    congr 1
    noncomm_ring
  rw [dist_eq_norm, dist_eq_norm, he, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr ha)]
  calc
    _ ≤ (2 * rootScale)⁻¹ * (‖T‖ * ‖T - U‖ + ‖T - U‖ * ‖U‖) :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
        (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))) (inv_nonneg.mpr ha.le)
    _ ≤ (2 * rootScale)⁻¹ * (rootRadius * ‖T - U‖ + ‖T - U‖ * rootRadius) := by
      gcongr
    _ = _ := by field_simp [rootScale_pos.ne']; ring

private def rootBall : Set ChargeOperator := Metric.closedBall 0 rootRadius

private theorem rootStep_maps : Set.MapsTo rootStep rootBall rootBall := by
  intro T hT
  rw [rootBall, Metric.mem_closedBall, dist_zero_right] at hT ⊢
  exact rootStep_norm_le T hT

private def rootRatio : ℝ≥0 := ⟨rootRadius / rootScale,
  div_nonneg rootRadius_pos.le rootScale_pos.le⟩

private theorem rootStep_contracting : ContractingWith rootRatio
    (rootStep_maps.restrict rootStep rootBall rootBall) := by
  refine ⟨?_, ?_⟩
  · change rootRadius / rootScale < 1
    apply (div_lt_one rootScale_pos).mpr
    unfold rootRadius
    linarith
  · rw [lipschitzWith_iff_dist_le_mul]
    intro T U
    have hT : ‖T.1‖ ≤ rootRadius := by
      simpa only [rootBall, Metric.mem_closedBall, dist_zero_right] using T.2
    have hU : ‖U.1‖ ≤ rootRadius := by
      simpa only [rootBall, Metric.mem_closedBall, dist_zero_right] using U.2
    exact rootStep_dist_le T.1 U.1 hT hU

private theorem rootRemainder_exists : ∃ R : ChargeOperator,
    ‖R‖ ≤ rootRadius ∧ rootStep R = R ∧
      Tendsto (fun n => rootStep^[n] 0) atTop (𝓝 R) := by
  have hz : (0 : ChargeOperator) ∈ rootBall := by
    simpa only [rootBall, Metric.mem_closedBall, dist_self] using rootRadius_pos.le
  obtain ⟨R, hR, hfix, ht, _⟩ := rootStep_contracting.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete rootStep_maps hz (edist_ne_top _ _)
  exact ⟨R, by simpa only [rootBall, Metric.mem_closedBall, dist_zero_right] using hR,
    hfix, ht⟩

def rootRemainder : ChargeOperator := Classical.choose rootRemainder_exists

theorem rootRemainder_norm_le : ‖rootRemainder‖ ≤ rootRadius :=
  (Classical.choose_spec rootRemainder_exists).1

theorem rootRemainder_fixed : rootStep rootRemainder = rootRemainder :=
  (Classical.choose_spec rootRemainder_exists).2.1

theorem tendsto_rootStep_iterate :
    Tendsto (fun n => rootStep^[n] 0) atTop (𝓝 rootRemainder) :=
  (Classical.choose_spec rootRemainder_exists).2.2

private theorem rootStep_preserves_nonneg (T : ChargeOperator)
    (hT : ∀ f : ChargeSpace, (∀ y, 0 ≤ f y) → ∀ y, 0 ≤ T f y)
    (f : ChargeSpace) (hf : ∀ y, 0 ≤ f y) (y : FiniteVertices) :
    0 ≤ rootStep T f y := by
  change 0 ≤ (2 * rootScale)⁻¹ * (adjacencyOperator f y + T (T f) y)
  exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) rootScale_pos.le))
    (add_nonneg (adjacencyOperator_nonneg f hf y) (hT (T f) (hT f hf) y))

private theorem rootStep_symmetric (T : ChargeOperator)
    (hT : ∀ f g, ⟪T f, g⟫_ℝ = ⟪f, T g⟫_ℝ) (f g : ChargeSpace) :
    ⟪rootStep T f, g⟫_ℝ = ⟪f, rootStep T g⟫_ℝ := by
  change ⟪(2 * rootScale)⁻¹ • (adjacencyOperator f + T (T f)), g⟫_ℝ =
    ⟪f, (2 * rootScale)⁻¹ • (adjacencyOperator g + T (T g))⟫_ℝ
  rw [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
    adjacencyOperator_symmetric, hT (T f) g, hT f (T g)]

private theorem iterate_nonneg (n : ℕ) (f : ChargeSpace) (hf : ∀ y, 0 ≤ f y)
    (y : FiniteVertices) : 0 ≤ (rootStep^[n] 0) f y := by
  induction n generalizing f y with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact rootStep_preserves_nonneg _ (fun f hf y => ih f hf y) f hf y

private theorem iterate_symmetric (n : ℕ) (f g : ChargeSpace) :
    ⟪(rootStep^[n] 0) f, g⟫_ℝ = ⟪f, (rootStep^[n] 0) g⟫_ℝ := by
  induction n generalizing f g with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact rootStep_symmetric _ ih f g

theorem rootRemainder_nonneg (f : ChargeSpace) (hf : ∀ y, 0 ≤ f y)
    (y : FiniteVertices) : 0 ≤ rootRemainder f y := by
  have ht := ((ContinuousLinearMap.apply ℝ ChargeSpace f).continuous.tendsto
    rootRemainder).comp tendsto_rootStep_iterate
  have he := ((lp.lipschitzWith_one_eval 2 y).continuous.tendsto
    (rootRemainder f)).comp ht
  exact ge_of_tendsto he (Filter.Eventually.of_forall fun n => iterate_nonneg n f hf y)

theorem rootRemainder_symmetric (f g : ChargeSpace) :
    ⟪rootRemainder f, g⟫_ℝ = ⟪f, rootRemainder g⟫_ℝ := by
  have hf := ((ContinuousLinearMap.apply ℝ ChargeSpace f).continuous.tendsto
    rootRemainder).comp tendsto_rootStep_iterate
  have hg := ((ContinuousLinearMap.apply ℝ ChargeSpace g).continuous.tendsto
    rootRemainder).comp tendsto_rootStep_iterate
  exact tendsto_nhds_unique (hf.inner tendsto_const_nhds)
    ((tendsto_const_nhds.inner hg).congr (fun n => (iterate_symmetric n f g).symm))

/-- The positive square root of the full weighted hyperbolic precision. -/
def hyperbolicRoot : ChargeOperator := rootScale • 1 - rootRemainder

theorem hyperbolicRoot_symmetric (f g : ChargeSpace) :
    ⟪hyperbolicRoot f, g⟫_ℝ = ⟪f, hyperbolicRoot g⟫_ℝ := by
  change ⟪rootScale • f - rootRemainder f, g⟫_ℝ =
    ⟪f, rootScale • g - rootRemainder g⟫_ℝ
  rw [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    rootRemainder_symmetric]

theorem hyperbolicRoot_coercive (f : ChargeSpace) :
    (1 / 2 : ℝ) * ‖f‖ ^ 2 ≤ ⟪hyperbolicRoot f, f⟫_ℝ := by
  have hn : ‖rootRemainder f‖ ≤ rootRadius * ‖f‖ :=
    (rootRemainder.le_opNorm f).trans
      (mul_le_mul_of_nonneg_right rootRemainder_norm_le (norm_nonneg _))
  have hi : ⟪rootRemainder f, f⟫_ℝ ≤ rootRadius * ‖f‖ ^ 2 := by
    calc
      _ ≤ ‖⟪rootRemainder f, f⟫_ℝ‖ := le_abs_self _
      _ ≤ ‖rootRemainder f‖ * ‖f‖ := norm_inner_le_norm _ _
      _ ≤ (rootRadius * ‖f‖) * ‖f‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = _ := by ring
  change _ ≤ ⟪rootScale • f - rootRemainder f, f⟫_ℝ
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  unfold rootRadius at hi
  linarith only [hi]

theorem hyperbolicRoot_squared :
    hyperbolicRoot * hyperbolicRoot = (edge + 1 / 4) • (1 : ChargeOperator) -
      adjacencyOperator := by
  have hr : adjacencyOperator + rootRemainder * rootRemainder =
      (2 * rootScale) • rootRemainder := by
    have h := congrArg (fun T : ChargeOperator => (2 * rootScale) • T) rootRemainder_fixed
    have ha : (2 : ℝ) * rootScale ≠ 0 := mul_ne_zero (by norm_num) rootScale_pos.ne'
    simpa only [rootStep, smul_smul, mul_inv_cancel₀ ha, one_smul] using h
  ext1 f
  have hf : rootRemainder (rootRemainder f) =
      (2 * rootScale) • rootRemainder f - adjacencyOperator f := by
    have h := congrArg (fun T : ChargeOperator => T f) hr
    exact eq_sub_of_add_eq' h
  change rootScale • (rootScale • f - rootRemainder f) -
      rootRemainder (rootScale • f - rootRemainder f) =
    (edge + 1 / 4) • f - adjacencyOperator f
  rw [map_sub, map_smul, hf]
  have ha : rootScale * rootScale = edge + 1 / 4 := by
    simpa only [pow_two] using rootScale_sq
  rw [smul_sub, smul_smul, ha]
  module

#print axioms rootRemainder_norm_le
#print axioms tendsto_rootStep_iterate
#print axioms rootRemainder_nonneg
#print axioms rootRemainder_symmetric
#print axioms hyperbolicRoot_coercive
#print axioms hyperbolicRoot_squared

end GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
