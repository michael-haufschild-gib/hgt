import GaloisForLFunctions.RHTower.CHMDPolarTransfer

/-!
# The arithmetic resolvent and the bounded Weil operator

The complete arithmetic graph is a Hilbert space for the graph norm `‖v‖²_μ + ‖edge v‖²` on the
theta–cosh mass space `L²(μ)`, `μ = Θ cosh(x/2) dx`. Riesz representation of the source functional
`q ↦ ⟨w, q⟩_μ` produces the arithmetic resolvent `R`, a bounded positive selfadjoint contraction of
`L²(μ)`: it is `(1 + L)⁻¹` for the generator `L` of the arithmetic jump form. It fixes the ground
vector `1` and halves every exact critical mode. In resolvent coordinates the signed Doob energy is
`⟨w, Rw⟩ − 2‖Rw‖²` and the complete Weil form is the quadratic form of the bounded selfadjoint
operator

`T = R − 2R² + 2|1⟩⟨1| − 2|R tanh(·/2)⟩⟨R tanh(·/2)|`.

The range of the Riesz lift is dense in the graph, so Weil positivity on the whole completed graph
is exactly the operator inequality `T ≥ 0`. The operator annihilates `1` and every critical mode,
and it is positive under the Riemann hypothesis.
-/

open MeasureTheory Set Filter Topology Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph

abbrev MassSpace := Lp ℝ 2 massMeasure

/-! ## Graph inner product -/

theorem graph_inner (p q : SourceGraph) :
    ⟪p, q⟫_ℝ = ⟪p.val.fst, q.val.fst⟫_ℝ + ⟪p.val.snd, q.val.snd⟫_ℝ := by
  rw [Submodule.coe_inner, WithLp.prod_inner_apply]
  rfl

theorem graph_norm_sq (p : SourceGraph) : ‖p‖ ^ 2 = ‖p.val.fst‖ ^ 2 + ‖p.val.snd‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, graph_inner, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]

theorem norm_source_le_graph (p : SourceGraph) : ‖p.val.fst‖ ≤ ‖p‖ := by
  have h : ‖p.val.fst‖ ^ 2 ≤ ‖p‖ ^ 2 := by
    rw [graph_norm_sq]
    nlinarith [sq_nonneg ‖p.val.snd‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-! ## The Riesz lift -/

/-- The source functional `q ↦ ⟨w, q⟩_μ` of a mass vector on the complete graph. -/
def sourceFunctional (w : MassSpace) : SourceGraph →L[ℝ] ℝ := (innerSL ℝ w).comp sourceMap

theorem sourceFunctional_apply (w : MassSpace) (q : SourceGraph) :
    sourceFunctional w q = ⟪w, q.val.fst⟫_ℝ := rfl

/-- The Riesz lift of a mass vector: the graph vector representing its source functional. -/
def rieszLift (w : MassSpace) : SourceGraph :=
  (InnerProductSpace.toDual ℝ SourceGraph).symm (sourceFunctional w)

theorem inner_rieszLift (w : MassSpace) (q : SourceGraph) :
    ⟪rieszLift w, q⟫_ℝ = ⟪w, q.val.fst⟫_ℝ := by
  unfold rieszLift
  rw [InnerProductSpace.toDual_symm_apply, sourceFunctional_apply]

theorem rieszLift_unique {w : MassSpace} {p : SourceGraph}
    (h : ∀ q : SourceGraph, ⟪p, q⟫_ℝ = ⟪w, q.val.fst⟫_ℝ) : rieszLift w = p := by
  apply ext_inner_right ℝ
  intro q
  rw [inner_rieszLift, h]

theorem rieszLift_add (w w' : MassSpace) : rieszLift (w + w') = rieszLift w + rieszLift w' :=
  rieszLift_unique fun q => by
    rw [inner_add_left, inner_rieszLift, inner_rieszLift, ← inner_add_left]

theorem rieszLift_smul (c : ℝ) (w : MassSpace) : rieszLift (c • w) = c • rieszLift w :=
  rieszLift_unique fun q => by
    rw [graph_inner]
    change ⟪c • (rieszLift w).val.fst, q.val.fst⟫_ℝ + ⟪c • (rieszLift w).val.snd, q.val.snd⟫_ℝ = _
    rw [real_inner_smul_left, real_inner_smul_left, ← mul_add, ← graph_inner, inner_rieszLift,
      real_inner_smul_left]

/-! ## The arithmetic resolvent -/

/-- The source coordinate of the Riesz lift. -/
def resolventFun (w : MassSpace) : MassSpace := (rieszLift w).val.fst

theorem inner_resolventFun (w w' : MassSpace) :
    ⟪resolventFun w, w'⟫_ℝ = ⟪rieszLift w, rieszLift w'⟫_ℝ := by
  have h := inner_rieszLift w' (rieszLift w)
  change ⟪rieszLift w', rieszLift w⟫_ℝ = ⟪w', resolventFun w⟫_ℝ at h
  rw [← real_inner_comm (resolventFun w) w', ← h]
  exact real_inner_comm _ _

theorem resolventFun_self (w : MassSpace) : ⟪resolventFun w, w⟫_ℝ = ‖rieszLift w‖ ^ 2 := by
  rw [inner_resolventFun, real_inner_self_eq_norm_sq]

theorem norm_resolventFun_le (w : MassSpace) : ‖resolventFun w‖ ≤ ‖w‖ := by
  have h3 : ‖resolventFun w‖ ≤ ‖rieszLift w‖ := norm_source_le_graph _
  by_cases h : rieszLift w = 0
  · have h0 : resolventFun w = 0 := by
      unfold resolventFun
      rw [h]
      rfl
    rw [h0, norm_zero]
    exact norm_nonneg _
  · have hpos : 0 < ‖rieszLift w‖ := norm_pos_iff.mpr h
    have h1 : ‖rieszLift w‖ ^ 2 = ⟪resolventFun w, w⟫_ℝ := (resolventFun_self w).symm
    have h2 : ⟪resolventFun w, w⟫_ℝ ≤ ‖resolventFun w‖ * ‖w‖ := real_inner_le_norm _ _
    have h4 : ‖rieszLift w‖ ^ 2 ≤ ‖rieszLift w‖ * ‖w‖ := by nlinarith [norm_nonneg w]
    have h5 : ‖rieszLift w‖ ≤ ‖w‖ := by nlinarith
    exact h3.trans h5

/-- The resolvent as a linear map. -/
def resolventLinear : MassSpace →ₗ[ℝ] MassSpace where
  toFun := resolventFun
  map_add' w w' := by
    unfold resolventFun
    rw [rieszLift_add]
    rfl
  map_smul' c w := by
    unfold resolventFun
    rw [rieszLift_smul]
    rfl

/-- **The arithmetic resolvent** `R = (1 + L)⁻¹` on the theta–cosh mass space. -/
def resolvent : MassSpace →L[ℝ] MassSpace :=
  resolventLinear.mkContinuous 1 fun w => by
    rw [one_mul]
    exact norm_resolventFun_le w

theorem resolvent_apply (w : MassSpace) : resolvent w = (rieszLift w).val.fst := rfl

theorem norm_resolvent_le : ‖resolvent‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem resolvent_symm (w w' : MassSpace) :
    ⟪resolvent w, w'⟫_ℝ = ⟪w, resolvent w'⟫_ℝ := by
  change ⟪resolventFun w, w'⟫_ℝ = ⟪w, resolventFun w'⟫_ℝ
  rw [inner_resolventFun, real_inner_comm (resolventFun w') w, inner_resolventFun]
  exact real_inner_comm _ _

theorem inner_resolvent_self (w : MassSpace) : ⟪resolvent w, w⟫_ℝ = ‖rieszLift w‖ ^ 2 :=
  resolventFun_self w

/-- The resolvent is a positive selfadjoint operator. -/
theorem resolvent_isPositive : resolvent.IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  refine ⟨fun w w' => resolvent_symm w w', fun w => ?_⟩
  rw [inner_resolvent_self]
  positivity

theorem isSelfAdjoint_resolvent : IsSelfAdjoint resolvent :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun w w' => resolvent_symm w w'

/-- The ground vector is fixed: the constant lift has no edge. -/
theorem rieszLift_oneL : rieszLift oneL = constantLift 1 :=
  rieszLift_unique fun q => by
    rw [graph_inner, constantLift_edge, inner_zero_left, add_zero]
    rfl

theorem resolvent_oneL : resolvent oneL = oneL := by
  rw [resolvent_apply, rieszLift_oneL]
  rfl

/-- Exact critical modes are halved: the resolvent has eigenvalue `1/2` on the critical band. -/
theorem rieszLift_critical (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    rieszLift (CHMDThetaTranslate.critical a ha).val.fst =
      (1 / 2 : ℝ) • CHMDThetaTranslate.critical a ha :=
  rieszLift_unique fun q => by
    rw [graph_inner]
    change ⟪(1 / 2 : ℝ) • (CHMDThetaTranslate.critical a ha).val.fst, q.val.fst⟫_ℝ +
      ⟪(1 / 2 : ℝ) • (CHMDThetaTranslate.critical a ha).val.snd, q.val.snd⟫_ℝ = _
    rw [real_inner_smul_left, real_inner_smul_left, CHMDThetaTranslate.critical_jump_identity]
    ring

theorem resolvent_critical (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    resolvent (CHMDThetaTranslate.critical a ha).val.fst =
      (1 / 2 : ℝ) • (CHMDThetaTranslate.critical a ha).val.fst := by
  rw [resolvent_apply, rieszLift_critical]
  rfl

/-! ## Energy in resolvent coordinates -/

theorem graph_norm_sq_rieszLift (w : MassSpace) : ‖rieszLift w‖ ^ 2 = ⟪w, resolvent w⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq, inner_rieszLift]
  rfl

theorem edge_norm_sq_rieszLift (w : MassSpace) :
    ‖(rieszLift w).val.snd‖ ^ 2 = ⟪w, resolvent w⟫_ℝ - ‖resolvent w‖ ^ 2 := by
  have h := graph_norm_sq (rieszLift w)
  rw [graph_norm_sq_rieszLift, ← resolvent_apply] at h
  linarith

/-- The signed Doob energy in resolvent coordinates. -/
theorem sourceEnergy_rieszLift (w : MassSpace) :
    sourceEnergy (rieszLift w) = ⟪w, resolvent w⟫_ℝ - 2 * ‖resolvent w‖ ^ 2 := by
  change ‖(rieszLift w).val.snd‖ ^ 2 - ‖(rieszLift w).val.fst‖ ^ 2 = _
  rw [edge_norm_sq_rieszLift, ← resolvent_apply]
  ring

/-! ## The bounded Weil operator -/

/-- The rank-one operator `x ↦ ⟨u, x⟩ u`. -/
def rankOne (u : MassSpace) : MassSpace →L[ℝ] MassSpace := (innerSL ℝ u).smulRight u

theorem rankOne_apply (u x : MassSpace) : rankOne u x = ⟪u, x⟫_ℝ • u := rfl

/-- **The bounded Weil operator** `T = R − 2R² + 2|1⟩⟨1| − 2|R tanh(·/2)⟩⟨R tanh(·/2)|`. -/
def weilOperator : MassSpace →L[ℝ] MassSpace :=
  resolvent - (2 : ℝ) • (resolvent ∘L resolvent) + (2 : ℝ) • rankOne oneL -
    (2 : ℝ) • rankOne (resolvent tanhL)

theorem weilOperator_apply (w : MassSpace) :
    weilOperator w = resolvent w - (2 : ℝ) • resolvent (resolvent w) +
      (2 : ℝ) • (⟪oneL, w⟫_ℝ • oneL) - (2 : ℝ) • (⟪resolvent tanhL, w⟫_ℝ • resolvent tanhL) := by
  simp only [weilOperator, sub_apply, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    rankOne_apply]

theorem inner_resolvent_oneL (w : MassSpace) : ⟪resolvent w, oneL⟫_ℝ = ⟪oneL, w⟫_ℝ := by
  rw [resolvent_symm, resolvent_oneL, real_inner_comm]

theorem inner_resolvent_tanhL (w : MassSpace) :
    ⟪resolvent w, tanhL⟫_ℝ = ⟪resolvent tanhL, w⟫_ℝ := by
  rw [resolvent_symm, real_inner_comm]

/-- **The complete Weil form is the quadratic form of the bounded Weil operator** in resolvent
coordinates. -/
theorem inner_weilOperator (w : MassSpace) :
    ⟪weilOperator w, w⟫_ℝ = weilForm (rieszLift w) := by
  rw [weilOperator_apply]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
  unfold weilForm
  rw [sourceEnergy_rieszLift, ← resolvent_apply, inner_resolvent_oneL, inner_resolvent_tanhL,
    resolvent_symm (resolvent w) w, real_inner_self_eq_norm_sq, real_inner_comm w (resolvent w)]
  ring

theorem weilOperator_symm (w w' : MassSpace) :
    ⟪weilOperator w, w'⟫_ℝ = ⟪w, weilOperator w'⟫_ℝ := by
  rw [weilOperator_apply, weilOperator_apply]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left, inner_sub_right,
    inner_add_right, real_inner_smul_right]
  rw [resolvent_symm w w', resolvent_symm (resolvent w) w', resolvent_symm w (resolvent w'),
    real_inner_comm oneL w, real_inner_comm (resolvent tanhL) w]
  ring

theorem isSelfAdjoint_weilOperator : IsSelfAdjoint weilOperator :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun w w' => weilOperator_symm w w'

theorem norm_oneL_sq : ‖oneL‖ ^ 2 = 1 / 2 := by
  rw [oneL_eq_constantLift, constantLift_mass]
  ring

theorem inner_tanhL_oneL : ⟪tanhL, oneL⟫_ℝ = 0 := by
  rw [inner_oneL]
  have hae : (∫ x, tanhL x ∂massMeasure) = ∫ x, tanhHalf x ∂massMeasure :=
    integral_congr_ae memLp_tanhHalf.coeFn_toLp
  rw [hae, integral_mass]
  apply integral_eq_zero_of_odd
  intro x
  rw [massDensity_neg, tanhHalf_neg]
  ring

/-- The Weil operator annihilates the ground vector. -/
theorem weilOperator_oneL : weilOperator oneL = 0 := by
  rw [weilOperator_apply, resolvent_oneL, resolvent_oneL, real_inner_self_eq_norm_sq, norm_oneL_sq,
    resolvent_symm, resolvent_oneL, inner_tanhL_oneL]
  module

/-- The Weil operator annihilates every exact critical mode. -/
theorem weilOperator_critical (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    weilOperator (CHMDThetaTranslate.critical a ha).val.fst = 0 := by
  have h1 : ⟪oneL, (CHMDThetaTranslate.critical a ha).val.fst⟫_ℝ = 0 := by
    rw [real_inner_comm, oneL_eq_constantLift]
    exact CHMDThetaTranslate.critical_primitive a ha
  have h2 : ⟪resolvent tanhL, (CHMDThetaTranslate.critical a ha).val.fst⟫_ℝ = 0 := by
    rw [resolvent_symm, resolvent_critical, real_inner_smul_right, real_inner_comm,
      critical_inner_tanhL, mul_zero]
  rw [weilOperator_apply, resolvent_critical, map_smul, resolvent_critical, h1, h2]
  module

/-! ## Operator positivity is graph positivity -/

/-- The Riesz lift as a linear map into the graph. -/
def rieszLinear : MassSpace →ₗ[ℝ] SourceGraph where
  toFun := rieszLift
  map_add' := rieszLift_add
  map_smul' := rieszLift_smul

/-- The range of the Riesz lift is dense in the complete graph. -/
theorem dense_range_rieszLift : Dense (Set.range rieszLift) := by
  have hK : (LinearMap.range rieszLinear).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro p hp
    have hall : ∀ w : MassSpace, ⟪w, p.val.fst⟫_ℝ = 0 := by
      intro w
      rw [← inner_rieszLift]
      exact Submodule.inner_right_of_mem_orthogonal (LinearMap.mem_range_self rieszLinear w) hp
    have hfst : p.val.fst = 0 := by
      have h := hall p.val.fst
      rw [real_inner_self_eq_norm_sq] at h
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)
    exact source_projection_injective hfst
  have hdense : Dense ((LinearMap.range rieszLinear : Submodule ℝ SourceGraph) : Set SourceGraph) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr hK
  have heq : ((LinearMap.range rieszLinear : Submodule ℝ SourceGraph) : Set SourceGraph) =
      Set.range rieszLift := by
    ext q
    simp only [SetLike.mem_coe, LinearMap.mem_range, Set.mem_range]
    rfl
  rw [heq] at hdense
  exact hdense

/-- Positivity of the bounded Weil operator gives nonnegativity of the complete Weil form on the
entire completed graph. -/
theorem weilForm_nonneg_of_weilOperator_isPositive (hT : weilOperator.IsPositive)
    (p : SourceGraph) : 0 ≤ weilForm p := by
  have hclosed : IsClosed {q : SourceGraph | 0 ≤ weilForm q} :=
    isClosed_le continuous_const continuous_weilForm
  have hsub : Set.range rieszLift ⊆ {q : SourceGraph | 0 ≤ weilForm q} := by
    rintro q ⟨w, rfl⟩
    change 0 ≤ weilForm (rieszLift w)
    rw [← inner_weilOperator]
    exact hT.inner_nonneg_left w
  have hall : (univ : Set SourceGraph) ⊆ {q : SourceGraph | 0 ≤ weilForm q} := by
    rw [← dense_range_rieszLift.closure_eq]
    exact closure_minimal hsub hclosed
  exact hall (mem_univ p)

/-- **Operator positivity is graph positivity.** -/
theorem weilOperator_isPositive_iff :
    weilOperator.IsPositive ↔ ∀ p : SourceGraph, 0 ≤ weilForm p := by
  refine ⟨fun hT p => weilForm_nonneg_of_weilOperator_isPositive hT p, fun h => ?_⟩
  rw [ContinuousLinearMap.isPositive_iff]
  refine ⟨fun w w' => weilOperator_symm w w', fun w => ?_⟩
  rw [inner_weilOperator]
  exact h _

/-- Positivity of the bounded Weil operator gives the literal Weil positivity of every real
compact `C²` test `Θv`. -/
theorem W_re_nonneg_of_weilOperator_isPositive (hT : weilOperator.IsPositive)
    (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    0 ≤ (zetaZeroConfig.W (fun x => (phiDoobTest v x : ℂ)) (fun x => (phiDoobTest v x : ℂ))).re := by
  rw [← weilForm_compactLift v hv hvc]
  exact weilForm_nonneg_of_weilOperator_isPositive hT _

/-- Under the Riemann hypothesis the bounded Weil operator is positive. -/
theorem weilOperator_isPositive_of_riemannHypothesis (hRH : RiemannHypothesis) :
    weilOperator.IsPositive :=
  weilOperator_isPositive_iff.mpr fun p => weilForm_nonneg_of_riemannHypothesis hRH p

end RHTower.CHMDPolar
