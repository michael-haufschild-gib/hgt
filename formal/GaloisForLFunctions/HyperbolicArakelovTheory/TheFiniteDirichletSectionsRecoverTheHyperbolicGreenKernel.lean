import GaloisForLFunctions.HyperbolicArakelovTheory.TheHyperbolicGreenKernelOfTheWeightedAdelicCarrier
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Finite Dirichlet sections recover the hyperbolic Green kernel

Compression of the actual adelic adjacency determines finite positive square
roots. A uniform contraction estimate passes these roots to the full carrier
in the strong topology. The resulting Green kernels and Robin operators
converge along all finite vertex sets, independently of an enumeration.
-/

set_option autoImplicit false
noncomputable section
open Filter NormedSpace
open scoped Classical BigOperators Topology InnerProductSpace NNReal
namespace GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
open FullAdelic SurfaceOfSpecZ

/-- Restriction to a finite set of actual adelic vertices. -/
def sectionProjection (F : Finset FiniteVertices) : ChargeOperator :=
  ∑ y ∈ F, (lp.singleContinuousLinearMap ℝ (fun _ : FiniteVertices => ℝ) 2 y).comp
    (lp.evalCLM ℝ (fun _ : FiniteVertices => ℝ) 2 y)

theorem sectionProjection_apply (F : Finset FiniteVertices) (f : ChargeSpace) :
    sectionProjection F f = ∑ y ∈ F, lp.single 2 y (f y) := by
  simp only [sectionProjection, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply]

theorem sectionProjection_coord (F : Finset FiniteVertices) (f : ChargeSpace)
    (y : FiniteVertices) : sectionProjection F f y = if y ∈ F then f y else 0 := by
  rw [sectionProjection_apply]
  simp only [lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply, Finset.sum_pi_single]

theorem sectionProjection_norm_le (F : Finset FiniteVertices) :
    ‖sectionProjection F‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  rw [one_mul]
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro y
  rw [sectionProjection_coord]
  split_ifs
  · exact le_rfl
  · simp only [norm_zero]; exact norm_nonneg _

theorem sectionProjection_idempotent (F : Finset FiniteVertices) :
    sectionProjection F * sectionProjection F = sectionProjection F := by
  ext1 f
  apply lp.ext
  funext y
  change sectionProjection F (sectionProjection F f) y = sectionProjection F f y
  simp only [sectionProjection_coord]
  split_ifs <;> rfl

theorem tendsto_sectionProjection (f : ChargeSpace) :
    Tendsto (fun F : Finset FiniteVertices => sectionProjection F f) atTop (𝓝 f) := by
  simpa only [sectionProjection_apply] using (lp.hasSum_single (by norm_num) f)

private theorem strong_apply {ι : Type*} {l : Filter ι}
    (T : ι → ChargeOperator) (U : ChargeOperator) (C : ℝ)
    (hb : ∀ i, ‖T i‖ ≤ C)
    (ht : ∀ f, Tendsto (fun i => T i f) l (𝓝 (U f)))
    {v : ι → ChargeSpace} {w : ChargeSpace} (hv : Tendsto v l (𝓝 w)) :
    Tendsto (fun i => T i (v i)) l (𝓝 (U w)) := by
  have hzero : Tendsto (fun i => T i (v i - w)) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun i => ((T i).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _)))
    simpa only [sub_self, norm_zero, mul_zero] using
      tendsto_const_nhds.mul (hv.sub tendsto_const_nhds).norm
  simpa only [map_sub, sub_add_cancel, zero_add] using hzero.add (ht w)

/-- The true Dirichlet compression of the all-prime adjacency. -/
def sectionAdjacency (F : Finset FiniteVertices) : ChargeOperator :=
  sectionProjection F * adjacencyOperator * sectionProjection F

theorem sectionAdjacency_norm_le (F : Finset FiniteVertices) :
    ‖sectionAdjacency F‖ ≤ edge := by
  calc
    _ ≤ (‖sectionProjection F‖ * ‖adjacencyOperator‖) * ‖sectionProjection F‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * edge) * 1 := by gcongr; exacts [sectionProjection_norm_le F,
      adjacencyOperator_norm_le, sectionProjection_norm_le F]
    _ = edge := by ring

theorem tendsto_sectionAdjacency (f : ChargeSpace) :
    Tendsto (fun F : Finset FiniteVertices => sectionAdjacency F f) atTop
      (𝓝 (adjacencyOperator f)) := by
  exact strong_apply sectionProjection 1 1 sectionProjection_norm_le tendsto_sectionProjection
    (adjacencyOperator.continuous.tendsto _ |>.comp (tendsto_sectionProjection f))

def sectionRootStep (F : Finset FiniteVertices) (T : ChargeOperator) : ChargeOperator :=
  (2 * rootScale)⁻¹ • (sectionAdjacency F + T * T)

private theorem sectionRootStep_norm_le (F : Finset FiniteVertices)
    (T : ChargeOperator) (hT : ‖T‖ ≤ rootRadius) :
    ‖sectionRootStep F T‖ ≤ rootRadius := by
  have ha : 0 < 2 * rootScale := mul_pos (by norm_num) rootScale_pos
  calc
    _ = (2 * rootScale)⁻¹ * ‖sectionAdjacency F + T * T‖ := by
      rw [sectionRootStep, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
    _ ≤ (2 * rootScale)⁻¹ * (edge + rootRadius ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ha.le)
      exact (norm_add_le _ _).trans (add_le_add (sectionAdjacency_norm_le F)
        ((norm_mul_le _ _).trans (by nlinarith only [hT, norm_nonneg T, rootRadius_pos])))
    _ = rootRadius := by rw [rootRadius_identity]; field_simp [rootScale_pos.ne']

private theorem sectionRootStep_dist_le (F : Finset FiniteVertices)
    (T U : ChargeOperator) (hT : ‖T‖ ≤ rootRadius) (hU : ‖U‖ ≤ rootRadius) :
    dist (sectionRootStep F T) (sectionRootStep F U) ≤
      (rootRadius / rootScale) * dist T U := by
  have he : sectionRootStep F T - sectionRootStep F U = rootStep T - rootStep U := by
    simp only [sectionRootStep, rootStep, ← smul_sub, add_sub_add_left_eq_sub]
  simpa only [dist_eq_norm, he] using rootStep_dist_le T U hT hU

private def sectionRootBall : Set ChargeOperator := Metric.closedBall 0 rootRadius

private theorem sectionRootStep_maps (F : Finset FiniteVertices) :
    Set.MapsTo (sectionRootStep F) sectionRootBall sectionRootBall := by
  intro T hT
  rw [sectionRootBall, Metric.mem_closedBall, dist_zero_right] at hT ⊢
  exact sectionRootStep_norm_le F T hT

private def sectionRootRatio : ℝ≥0 := ⟨rootRadius / rootScale,
  div_nonneg rootRadius_pos.le rootScale_pos.le⟩

private theorem sectionRootStep_contracting (F : Finset FiniteVertices) :
    ContractingWith sectionRootRatio
      ((sectionRootStep_maps F).restrict (sectionRootStep F) sectionRootBall sectionRootBall) := by
  refine ⟨?_, ?_⟩
  · change rootRadius / rootScale < 1
    apply (div_lt_one rootScale_pos).mpr
    unfold rootRadius
    linarith
  · rw [lipschitzWith_iff_dist_le_mul]
    intro T U
    have hT : ‖T.1‖ ≤ rootRadius := by
      simpa only [sectionRootBall, Metric.mem_closedBall, dist_zero_right] using T.2
    have hU : ‖U.1‖ ≤ rootRadius := by
      simpa only [sectionRootBall, Metric.mem_closedBall, dist_zero_right] using U.2
    exact sectionRootStep_dist_le F T.1 U.1 hT hU

private theorem sectionRemainder_exists (F : Finset FiniteVertices) : ∃ R : ChargeOperator,
    ‖R‖ ≤ rootRadius ∧ sectionRootStep F R = R ∧
      Tendsto (fun n => (sectionRootStep F)^[n] 0) atTop (𝓝 R) := by
  have hz : (0 : ChargeOperator) ∈ sectionRootBall := by
    simpa only [sectionRootBall, Metric.mem_closedBall, dist_self] using rootRadius_pos.le
  obtain ⟨R, hR, hfix, ht, _⟩ := (sectionRootStep_contracting F).exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete (sectionRootStep_maps F) hz (edist_ne_top _ _)
  exact ⟨R, by simpa only [sectionRootBall, Metric.mem_closedBall, dist_zero_right] using hR,
    hfix, ht⟩

def sectionRemainder (F : Finset FiniteVertices) : ChargeOperator :=
  Classical.choose (sectionRemainder_exists F)

theorem sectionRemainder_norm_le (F : Finset FiniteVertices) :
    ‖sectionRemainder F‖ ≤ rootRadius := (Classical.choose_spec (sectionRemainder_exists F)).1

theorem sectionRemainder_fixed (F : Finset FiniteVertices) :
    sectionRootStep F (sectionRemainder F) = sectionRemainder F :=
  (Classical.choose_spec (sectionRemainder_exists F)).2.1

theorem tendsto_sectionRootStep_iterate (F : Finset FiniteVertices) :
    Tendsto (fun n => (sectionRootStep F)^[n] 0) atTop (𝓝 (sectionRemainder F)) :=
  (Classical.choose_spec (sectionRemainder_exists F)).2.2

private theorem root_iterate_bound (n : ℕ) : ‖rootStep^[n] 0‖ ≤ rootRadius := by
  induction n with
  | zero => simpa using rootRadius_pos.le
  | succ n ih => rw [Function.iterate_succ_apply']; exact rootStep_norm_le _ ih

private theorem section_iterate_bound (F : Finset FiniteVertices) (n : ℕ) :
    ‖(sectionRootStep F)^[n] 0‖ ≤ rootRadius := by
  induction n with
  | zero => simpa using rootRadius_pos.le
  | succ n ih => rw [Function.iterate_succ_apply']; exact sectionRootStep_norm_le _ _ ih

private theorem root_iterate_error (n : ℕ) :
    dist (rootStep^[n] 0) rootRemainder ≤ (rootRadius / rootScale) ^ n * rootRadius := by
  induction n with
  | zero => simpa only [Function.iterate_zero, id_eq, dist_zero_left, pow_zero, one_mul] using
      rootRemainder_norm_le
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc
        _ = dist (rootStep (rootStep^[n] 0)) (rootStep rootRemainder) := by
          rw [rootRemainder_fixed]
        _ ≤ (rootRadius / rootScale) * dist (rootStep^[n] 0) rootRemainder :=
          rootStep_dist_le _ _ (root_iterate_bound n) rootRemainder_norm_le
        _ ≤ (rootRadius / rootScale) * ((rootRadius / rootScale)^n * rootRadius) :=
          mul_le_mul_of_nonneg_left ih (div_nonneg rootRadius_pos.le rootScale_pos.le)
        _ = _ := by rw [pow_succ']; ring

private theorem section_iterate_error (F : Finset FiniteVertices) (n : ℕ) :
    dist ((sectionRootStep F)^[n] 0) (sectionRemainder F) ≤
      (rootRadius / rootScale) ^ n * rootRadius := by
  induction n with
  | zero => simpa only [Function.iterate_zero, id_eq, dist_zero_left, pow_zero, one_mul] using
      sectionRemainder_norm_le F
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc
        _ = dist (sectionRootStep F ((sectionRootStep F)^[n] 0))
            (sectionRootStep F (sectionRemainder F)) := by rw [sectionRemainder_fixed]
        _ ≤ (rootRadius / rootScale) * dist ((sectionRootStep F)^[n] 0) (sectionRemainder F) :=
          sectionRootStep_dist_le _ _ _ (section_iterate_bound F n) (sectionRemainder_norm_le F)
        _ ≤ (rootRadius / rootScale) * ((rootRadius / rootScale)^n * rootRadius) :=
          mul_le_mul_of_nonneg_left ih (div_nonneg rootRadius_pos.le rootScale_pos.le)
        _ = _ := by rw [pow_succ']; ring

private theorem tendsto_section_iterate (n : ℕ) (f : ChargeSpace) :
    Tendsto (fun F : Finset FiniteVertices => ((sectionRootStep F)^[n] 0) f) atTop
      (𝓝 ((rootStep^[n] 0) f)) := by
  induction n generalizing f with
  | zero => exact tendsto_const_nhds
  | succ n ih =>
      simp only [Function.iterate_succ_apply']
      have hprod := strong_apply (fun F => (sectionRootStep F)^[n] 0)
        (rootStep^[n] 0) rootRadius (fun F => section_iterate_bound F n) ih (ih f)
      exact ((tendsto_sectionAdjacency f).add hprod).const_smul ((2 * rootScale)⁻¹)

/-- Finite Dirichlet square roots converge strongly, with no choice of enumeration of the carrier. -/
theorem tendsto_sectionRemainder (f : ChargeSpace) :
    Tendsto (fun F : Finset FiniteVertices => sectionRemainder F f) atTop
      (𝓝 (rootRemainder f)) := by
  have hq0 : 0 ≤ rootRadius / rootScale := div_nonneg rootRadius_pos.le rootScale_pos.le
  have hq1 : rootRadius / rootScale < 1 := by
    apply (div_lt_one rootScale_pos).mpr
    unfold rootRadius
    linarith
  have hz : Tendsto (fun n : ℕ => (rootRadius / rootScale)^n * rootRadius * ‖f‖)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const rootRadius).mul_const ‖f‖
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨n, hn⟩ := (Metric.tendsto_nhds.mp hz (ε / 3) (by linarith)).exists
  have hn' : (rootRadius / rootScale)^n * rootRadius * ‖f‖ < ε / 3 := by
    exact (le_abs_self _).trans_lt (by simpa only [Real.dist_eq, sub_zero] using hn)
  filter_upwards [Metric.tendsto_nhds.mp (tendsto_section_iterate n f)
    (ε / 3) (by linarith)] with F hF
  have hleft : dist (sectionRemainder F f) (((sectionRootStep F)^[n] 0) f) ≤
      (rootRadius / rootScale)^n * rootRadius * ‖f‖ := by
    rw [dist_comm, dist_eq_norm, ← ContinuousLinearMap.sub_apply]
    exact (((sectionRootStep F)^[n] 0 - sectionRemainder F).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (by simpa only [dist_eq_norm] using
        section_iterate_error F n) (norm_nonneg _))
  have hright : dist ((rootStep^[n] 0) f) (rootRemainder f) ≤
      (rootRadius / rootScale)^n * rootRadius * ‖f‖ := by
    rw [dist_eq_norm, ← ContinuousLinearMap.sub_apply]
    exact ((rootStep^[n] 0 - rootRemainder).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (by simpa only [dist_eq_norm] using root_iterate_error n)
        (norm_nonneg _))
  have htri := dist_triangle4 (sectionRemainder F f) (((sectionRootStep F)^[n] 0) f)
    ((rootStep^[n] 0) f) (rootRemainder f)
  linarith only [hleft, hright, hF, hn', htri]

private theorem sectionAdjacency_supported (F : Finset FiniteVertices) :
    sectionProjection F * sectionAdjacency F = sectionAdjacency F ∧
      sectionAdjacency F * sectionProjection F = sectionAdjacency F := by
  constructor
  · unfold sectionAdjacency
    rw [← mul_assoc, ← mul_assoc, sectionProjection_idempotent]
  · unfold sectionAdjacency
    rw [mul_assoc, sectionProjection_idempotent]

private theorem section_iterate_supported (F : Finset FiniteVertices) (n : ℕ) :
    sectionProjection F * ((sectionRootStep F)^[n] 0) = (sectionRootStep F)^[n] 0 ∧
      ((sectionRootStep F)^[n] 0) * sectionProjection F = (sectionRootStep F)^[n] 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      constructor
      · rw [sectionRootStep, mul_smul_comm, mul_add, (sectionAdjacency_supported F).1,
          ← mul_assoc, ih.1]
      · rw [sectionRootStep, smul_mul_assoc, add_mul, (sectionAdjacency_supported F).2,
          mul_assoc, ih.2]

theorem sectionRemainder_supported (F : Finset FiniteVertices) :
    sectionProjection F * sectionRemainder F = sectionRemainder F ∧
      sectionRemainder F * sectionProjection F = sectionRemainder F := by
  have ht := tendsto_sectionRootStep_iterate F
  constructor
  · exact tendsto_nhds_unique ((tendsto_const_nhds (x := sectionProjection F)).mul ht)
      (ht.congr fun n => (section_iterate_supported F n).1.symm)
  · exact tendsto_nhds_unique (ht.mul (tendsto_const_nhds (x := sectionProjection F)))
      (ht.congr fun n => (section_iterate_supported F n).2.symm)

/-- On the finite range this is the square root of the Dirichlet precision. -/
def sectionHyperbolicRoot (F : Finset FiniteVertices) : ChargeOperator :=
  rootScale • 1 - sectionRemainder F

private theorem sectionProjection_symmetric (F : Finset FiniteVertices) (f g : ChargeSpace) :
    ⟪sectionProjection F f, g⟫_ℝ = ⟪f, sectionProjection F g⟫_ℝ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro y
  simp only [sectionProjection_coord]
  split_ifs
  · rfl
  · simp only [inner_zero_left, inner_zero_right]

private theorem sectionAdjacency_symmetric (F : Finset FiniteVertices) (f g : ChargeSpace) :
    ⟪sectionAdjacency F f, g⟫_ℝ = ⟪f, sectionAdjacency F g⟫_ℝ := by
  change ⟪sectionProjection F (adjacencyOperator (sectionProjection F f)), g⟫_ℝ =
    ⟪f, sectionProjection F (adjacencyOperator (sectionProjection F g))⟫_ℝ
  rw [sectionProjection_symmetric, adjacencyOperator_symmetric, sectionProjection_symmetric]

private theorem section_iterate_symmetric (F : Finset FiniteVertices) (n : ℕ)
    (f g : ChargeSpace) :
    ⟪((sectionRootStep F)^[n] 0) f, g⟫_ℝ = ⟪f, ((sectionRootStep F)^[n] 0) g⟫_ℝ := by
  induction n generalizing f g with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change ⟪(2 * rootScale)⁻¹ • (sectionAdjacency F f +
        ((sectionRootStep F)^[n] 0) (((sectionRootStep F)^[n] 0) f)), g⟫_ℝ =
          ⟪f, (2 * rootScale)⁻¹ • (sectionAdjacency F g +
        ((sectionRootStep F)^[n] 0) (((sectionRootStep F)^[n] 0) g))⟫_ℝ
      rw [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
        sectionAdjacency_symmetric, ih _ g, ih f _]

theorem sectionRemainder_symmetric (F : Finset FiniteVertices) (f g : ChargeSpace) :
    ⟪sectionRemainder F f, g⟫_ℝ = ⟪f, sectionRemainder F g⟫_ℝ := by
  have hf := ((ContinuousLinearMap.apply ℝ ChargeSpace f).continuous.tendsto
    (sectionRemainder F)).comp (tendsto_sectionRootStep_iterate F)
  have hg := ((ContinuousLinearMap.apply ℝ ChargeSpace g).continuous.tendsto
    (sectionRemainder F)).comp (tendsto_sectionRootStep_iterate F)
  exact tendsto_nhds_unique (hf.inner tendsto_const_nhds)
    ((tendsto_const_nhds.inner hg).congr (fun n => (section_iterate_symmetric F n f g).symm))

theorem sectionHyperbolicRoot_symmetric (F : Finset FiniteVertices) (f g : ChargeSpace) :
    ⟪sectionHyperbolicRoot F f, g⟫_ℝ = ⟪f, sectionHyperbolicRoot F g⟫_ℝ := by
  change ⟪rootScale • f - sectionRemainder F f, g⟫_ℝ =
    ⟪f, rootScale • g - sectionRemainder F g⟫_ℝ
  rw [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    sectionRemainder_symmetric]

theorem sectionHyperbolicRoot_squared (F : Finset FiniteVertices) :
    sectionHyperbolicRoot F * sectionHyperbolicRoot F =
      (edge + 1 / 4) • (1 : ChargeOperator) - sectionAdjacency F := by
  have hr : sectionAdjacency F + sectionRemainder F * sectionRemainder F =
      (2 * rootScale) • sectionRemainder F := by
    have h := congrArg (fun T : ChargeOperator => (2 * rootScale) • T) (sectionRemainder_fixed F)
    have ha : (2 : ℝ) * rootScale ≠ 0 := mul_ne_zero (by norm_num) rootScale_pos.ne'
    simpa only [sectionRootStep, smul_smul, mul_inv_cancel₀ ha, one_smul] using h
  ext1 f
  have hf : sectionRemainder F (sectionRemainder F f) =
      (2 * rootScale) • sectionRemainder F f - sectionAdjacency F f := by
    have h := congrArg (fun T : ChargeOperator => T f) hr
    exact eq_sub_of_add_eq' h
  change rootScale • (rootScale • f - sectionRemainder F f) -
      sectionRemainder F (rootScale • f - sectionRemainder F f) =
    (edge + 1 / 4) • f - sectionAdjacency F f
  rw [map_sub, map_smul, hf]
  have ha : rootScale * rootScale = edge + 1 / 4 := by
    simpa only [pow_two] using rootScale_sq
  rw [smul_sub, smul_smul, ha]
  module

theorem sectionHyperbolicRoot_coercive (F : Finset FiniteVertices) (f : ChargeSpace) :
    (1 / 2 : ℝ) * ‖f‖ ^ 2 ≤ ⟪sectionHyperbolicRoot F f, f⟫_ℝ := by
  have hn : ‖sectionRemainder F f‖ ≤ rootRadius * ‖f‖ :=
    ((sectionRemainder F).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (sectionRemainder_norm_le F) (norm_nonneg _))
  have hi : ⟪sectionRemainder F f, f⟫_ℝ ≤ rootRadius * ‖f‖ ^ 2 := by
    calc
      _ ≤ ‖⟪sectionRemainder F f, f⟫_ℝ‖ := le_abs_self _
      _ ≤ ‖sectionRemainder F f‖ * ‖f‖ := norm_inner_le_norm _ _
      _ ≤ (rootRadius * ‖f‖) * ‖f‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = _ := by ring
  change _ ≤ ⟪rootScale • f - sectionRemainder F f, f⟫_ℝ
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  unfold rootRadius at hi
  linarith only [hi]

theorem tendsto_sectionHyperbolicRoot (f : ChargeSpace) :
    Tendsto (fun F : Finset FiniteVertices => sectionHyperbolicRoot F f) atTop
      (𝓝 (hyperbolicRoot f)) :=
  tendsto_const_nhds.sub (tendsto_sectionRemainder f)

private theorem operator_exp_apply (T : ChargeOperator) (f : ChargeSpace) :
    exp T f = ∑' n : ℕ, (n.factorial : ℝ)⁻¹ • (T ^ n) f := by
  let ev := ContinuousLinearMap.apply ℝ ChargeSpace f
  rw [exp_eq_tsum ℝ]
  change ev (∑' n : ℕ, (n.factorial : ℝ)⁻¹ • T ^ n) = _
  rw [ev.map_tsum (expSeries_summable' (𝕂 := ℝ) T)]
  rfl

private theorem strong_exp {ι : Type*} {l : Filter ι}
    (T : ι → ChargeOperator) (U : ChargeOperator) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ i, ‖T i‖ ≤ C)
    (ht : ∀ f, Tendsto (fun i => T i f) l (𝓝 (U f))) (f : ChargeSpace) :
    Tendsto (fun i => exp (T i) f) l (𝓝 (exp U f)) := by
  have hp (n : ℕ) (v : ChargeSpace) :
      Tendsto (fun i => ((T i)^n) v) l (𝓝 ((U^n) v)) := by
    induction n generalizing v with
    | zero => exact tendsto_const_nhds
    | succ n ih =>
        simp only [pow_succ', mul_apply_eq_comp]
        exact strong_apply T U C hb ht (ih v)
  have hpow (i : ι) (n : ℕ) : ‖((T i)^n) f‖ ≤ C^n * ‖f‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', mul_apply_eq_comp]
        calc
          _ ≤ C * ‖((T i)^n) f‖ := ((T i).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _))
          _ ≤ C * (C^n * ‖f‖) := mul_le_mul_of_nonneg_left ih hC
          _ = C^(n+1) * ‖f‖ := by rw [pow_succ']; ring
  have hsum : Summable (fun n : ℕ => (n.factorial : ℝ)⁻¹ * C^n * ‖f‖) := by
    simpa only [smul_eq_mul] using (expSeries_summable' (𝕂 := ℝ) C).mul_right ‖f‖
  have hdom : ∀ᶠ i in l, ∀ n : ℕ,
      ‖(n.factorial : ℝ)⁻¹ • ((T i)^n) f‖ ≤ (n.factorial : ℝ)⁻¹ * C^n * ‖f‖ := by
    apply Filter.Eventually.of_forall
    intro i n
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)),
      mul_assoc]
    exact mul_le_mul_of_nonneg_left (hpow i n) (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hlim := tendsto_tsum_of_dominated_convergence hsum
    (fun n => (hp n f).const_smul ((n.factorial : ℝ)⁻¹)) hdom
  simpa only [operator_exp_apply] using hlim

private theorem sectionHyperbolicRoot_norm_le (F : Finset FiniteVertices) :
    ‖sectionHyperbolicRoot F‖ ≤ rootScale + rootRadius := by
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg rootScale_pos.le rootRadius_pos.le)
  intro f
  change ‖rootScale • f - sectionRemainder F f‖ ≤ _
  calc
    _ ≤ ‖rootScale • f‖ + ‖sectionRemainder F f‖ := norm_sub_le _ _
    _ ≤ rootScale * ‖f‖ + rootRadius * ‖f‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos rootScale_pos]
      exact add_le_add_left (((sectionRemainder F).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right (sectionRemainder_norm_le F) (norm_nonneg _))) _
    _ = _ := by ring

def sectionEvolution (F : Finset FiniteVertices) (r : ℝ) : ChargeOperator :=
  exp (r • (-sectionHyperbolicRoot F))

private theorem sectionEvolution_norm_le (F : Finset FiniteVertices) (r : ℝ) :
    ‖sectionEvolution F r‖ ≤ Real.exp (|r| * (rootScale + rootRadius)) := by
  apply (HTGeometry.norm_exp_le_exp_norm _).trans
  apply Real.exp_le_exp.mpr
  rw [norm_smul, norm_neg, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (sectionHyperbolicRoot_norm_le F) (abs_nonneg _)

theorem tendsto_sectionEvolution (r : ℝ) (f : ChargeSpace) :
    Tendsto (fun F : Finset FiniteVertices => sectionEvolution F r f) atTop
      (𝓝 (exp (r • (-hyperbolicRoot)) f)) := by
  apply strong_exp (fun F => r • (-sectionHyperbolicRoot F))
    (r • (-hyperbolicRoot)) (|r| * (rootScale + rootRadius))
    (mul_nonneg (abs_nonneg _) (add_nonneg rootScale_pos.le rootRadius_pos.le))
  · intro F
    rw [norm_smul, norm_neg, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (sectionHyperbolicRoot_norm_le F) (abs_nonneg _)
  · intro g
    exact (tendsto_sectionHyperbolicRoot g).neg.const_smul r

/-- Zero extension of the finite evolution; the exterior identity is removed. -/
def dirichletEvolution (F : Finset FiniteVertices) (r : ℝ) : ChargeOperator :=
  sectionProjection F * sectionEvolution F r * sectionProjection F

theorem tendsto_dirichletEvolution (r : ℝ) (f : ChargeSpace) :
    Tendsto (fun F : Finset FiniteVertices => dirichletEvolution F r f) atTop
      (𝓝 (exp (r • (-hyperbolicRoot)) f)) := by
  have h := strong_apply (fun F => sectionEvolution F r) (exp (r • (-hyperbolicRoot)))
    (Real.exp (|r| * (rootScale + rootRadius))) (fun F => sectionEvolution_norm_le F r)
    (tendsto_sectionEvolution r) (tendsto_sectionProjection f)
  exact strong_apply sectionProjection 1 1 sectionProjection_norm_le tendsto_sectionProjection h

#print axioms tendsto_sectionRemainder
#print axioms sectionRemainder_supported
#print axioms sectionHyperbolicRoot_squared
#print axioms sectionHyperbolicRoot_coercive
#print axioms tendsto_dirichletEvolution
end GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
