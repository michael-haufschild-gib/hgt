import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Source-gauge observability spectrum

A linear source boundary `Q` remembers a primitive only modulo `ker Q`.  A transverse reporter
`R` must therefore be tested on that residual gauge, not on the ambient primitive space.  This
module proves the exact topological refinement of the common-kernel conservativity criterion.

There are three exhaustive phases: an exact invisible gauge, normalized approximate invisible
gauges, or stable anti-Lipschitz separation.  On a Hilbert completion the positive Gram operator
of the restricted reporter has exactly the same algebraic conservativity gate.  Moreover, a
compact reporter on an infinite-dimensional residual gauge can never be stably conservative:
even if it is injective, it has unit gauge directions whose signals converge to zero.
-/

open Filter Topology Set Function

namespace GaloisForLFunctions

noncomputable section

/-- A reporter has normalized approximate invisible directions when it sends a sequence of unit
vectors to zero.  This is the topological obstruction left after its exact kernel has vanished. -/
def HasApproximateUnitKernel
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →L[ℂ] F) : Prop :=
  ∃ u : ℕ → E, (∀ n, ‖u n‖ = 1) ∧
    Tendsto (fun n ↦ T (u n)) atTop (nhds 0)

/-! ## Reporter graphs as exact relative-position objects -/

/-- The horizontal lattice and a reporter graph meet trivially exactly when the reporter is
injective.  Thus exact gauge blindness is literally a lattice-intersection defect. -/
theorem horizontal_inf_graph_eq_bot_iff
    {R E F : Type*} [Ring R]
    [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F]
    (T : E →ₗ[R] F) :
    Submodule.fst R E F ⊓ T.graph = ⊥ ↔ Function.Injective T := by
  constructor
  · intro hintersect x y hxy
    have hmem : (x - y, 0) ∈ Submodule.fst R E F ⊓ T.graph := by
      constructor
      · simp [Submodule.fst]
      · change (0 : F) = T (x - y)
        simp [hxy]
    have hzero : (x - y, 0) = 0 := by
      rw [hintersect] at hmem
      simpa using hmem
    exact sub_eq_zero.mp (congrArg Prod.fst hzero)
  · intro hinjective
    rw [eq_bot_iff]
    rintro ⟨x, y⟩ ⟨hhor, hgraph⟩
    have hy : y = 0 := by simpa [Submodule.fst] using hhor
    have hTx : T x = 0 := by
      change y = T x at hgraph
      exact hgraph.symm.trans hy
    have hx : x = 0 := hinjective (by simpa using hTx)
    simp [hx, hy]

/-- The sum of the horizontal lattice and a reporter graph is exactly the ambient source factor
times the reporter range. -/
theorem horizontal_sup_graph_eq_top_prod_range
    {R E F : Type*} [Ring R]
    [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F]
    (T : E →ₗ[R] F) :
    Submodule.fst R E F ⊔ T.graph =
      (⊤ : Submodule R E).prod (LinearMap.range T) := by
  ext p
  constructor
  · intro hp
    rcases Submodule.mem_sup.mp hp with ⟨a, ha, b, hb, hab⟩
    have ha2 : a.2 = 0 := by simpa [Submodule.fst] using ha
    have hb2 : b.2 = T b.1 := by simpa [LinearMap.mem_graph_iff] using hb
    constructor
    · simp
    · refine ⟨b.1, ?_⟩
      calc
        T b.1 = b.2 := hb2.symm
        _ = a.2 + b.2 := by simp [ha2]
        _ = p.2 := congrArg Prod.snd hab
  · rintro ⟨-, ⟨y, hy⟩⟩
    apply Submodule.mem_sup.mpr
    refine ⟨(p.1 - y, 0), ?_, (y, T y), ?_, ?_⟩
    · simp [Submodule.fst]
    · simp [LinearMap.mem_graph_iff]
    · apply Prod.ext
      · simp
      · simpa using hy

/-- Algebraic transversality of the horizontal lattice and reporter graph is exactly reporter
surjectivity. -/
theorem horizontal_sup_graph_eq_top_iff
    {R E F : Type*} [Ring R]
    [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F]
    (T : E →ₗ[R] F) :
    Submodule.fst R E F ⊔ T.graph = ⊤ ↔ Function.Surjective T := by
  rw [horizontal_sup_graph_eq_top_prod_range]
  rw [Submodule.prod_eq_top_iff]
  simp [LinearMap.range_eq_top]

/-- The horizontal/graph lattice sum is closed exactly when the reporter range is closed.  Hence
approximate gauge blindness is literally the non-strict relative position of the same pair whose
intersection detects exact blindness. -/
theorem isClosed_horizontal_sup_graph_iff_isClosed_range
    {R E F : Type*} [Ring R]
    [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F]
    [TopologicalSpace E] [TopologicalSpace F]
    (T : E →ₗ[R] F) :
    IsClosed ((Submodule.fst R E F ⊔ T.graph : Submodule R (E × F)) : Set (E × F)) ↔
      IsClosed (Set.range T) := by
  rw [horizontal_sup_graph_eq_top_prod_range]
  change IsClosed ((Set.univ : Set E) ×ˢ (Set.range T)) ↔ IsClosed (Set.range T)
  constructor
  · intro h
    have hpre := h.preimage (Continuous.prodMk_right (0 : E))
    simpa using hpre
  · exact isClosed_univ.prod

/-- For an injective operator between complex Banach spaces, normalized approximate invisible
directions exist exactly when the range is not closed. -/
theorem hasApproximateUnitKernel_iff_not_isClosed_range
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) (hT : Function.Injective T) :
    HasApproximateUnitKernel T ↔ ¬ IsClosed (Set.range T) := by
  constructor
  · rintro ⟨u, hu, hzero⟩ hclosed
    let e : E ≃L[ℂ] T.range := T.equivRange hT hclosed
    have hsub : Tendsto
        (fun n ↦ (⟨T (u n), T.mem_range_self (u n)⟩ : T.range))
        atTop (nhds 0) := by
      rw [tendsto_subtype_rng]
      simpa using hzero
    have hinv := e.symm.continuous.continuousAt.tendsto.comp hsub
    have hu0 : Tendsto u atTop (nhds 0) := by
      convert hinv using 1
      · funext n
        exact (T.equivRange_symm_apply hT hclosed (u n)).symm
      · simp
    have hnorm : Tendsto (fun n ↦ ‖u n‖) atTop (nhds 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mp hu0
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 0) := by
      simpa only [hu] using hnorm
    have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hone
    norm_num at h10
  · intro hclosed
    have hanti : ¬ ∃ K, AntilipschitzWith K T := by
      exact fun h ↦ hclosed
        ((T.isClosed_range_iff_antilipschitz_of_injective hT).2 h)
    rw [antilipschitzWith_iff_exists_mul_le_norm] at hanti
    push Not at hanti
    obtain ⟨φ, _hφ_anti, hφ_pos, hφ⟩ := exists_seq_strictAnti_tendsto (0 : ℝ)
    have hx : ∀ n : ℕ, ∃ x : E, ‖T x‖ < φ n * ‖x‖ := by
      intro n
      obtain ⟨x, hx⟩ := hanti (φ n) (hφ_pos n)
      exact ⟨x, hx⟩
    choose x hx using hx
    have hxne : ∀ n, x n ≠ 0 := by
      intro n hxn
      have hxn' := hx n
      rw [hxn, map_zero, norm_zero, norm_zero, mul_zero] at hxn'
      exact (lt_irrefl 0) hxn'
    let u : ℕ → E := fun n ↦ (((‖x n‖ : ℝ) : ℂ)⁻¹) • x n
    refine ⟨u, ?_, ?_⟩
    · intro n
      simp only [u, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (norm_nonneg _)]
      rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hxne n))]
    · apply squeeze_zero_norm (fun n ↦ ?_) hφ
      apply le_of_lt
      rw [map_smul, norm_smul]
      simp only [norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (norm_nonneg _)]
      rw [inv_mul_lt_iff₀ (norm_pos_iff.mpr (hxne n))]
      simpa [mul_comm] using hx n

/-- A compact injective reporter can have closed range only when its domain is finite-dimensional. -/
theorem finiteDimensional_of_compact_injective_isClosed_range
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) (hcompact : IsCompactOperator T)
    (hT : Function.Injective T) (hclosed : IsClosed (Set.range T)) :
    FiniteDimensional ℂ E := by
  let e : E ≃L[ℂ] T.range := T.equivRange hT hclosed
  have hrange : IsCompactOperator T.rangeRestrict :=
    hcompact.codRestrict (fun x ↦ T.mem_range_self x) hclosed
  have hid : IsCompactOperator
      ((e.symm : T.range →L[ℂ] E) ∘L T.rangeRestrict) :=
    hrange.clm_comp e.symm.toContinuousLinearMap
  apply FiniteDimensional.of_isCompactOperator_id
  convert hid using 1
  funext x
  exact (T.equivRange_symm_apply hT hclosed x).symm

/-- On an infinite-dimensional clock space, every compact injective reporter has normalized
approximate blind directions. -/
theorem compact_injective_hasApproximateUnitKernel
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) (hcompact : IsCompactOperator T)
    (hT : Function.Injective T) (hinfinite : ¬ FiniteDimensional ℂ E) :
    HasApproximateUnitKernel T := by
  apply (hasApproximateUnitKernel_iff_not_isClosed_range T hT).2
  intro hclosed
  exact hinfinite
    (finiteDimensional_of_compact_injective_isClosed_range T hcompact hT hclosed)

/-- Restrict a reporter to the residual gauge forgotten by the source boundary. -/
def residualGaugeReporter
    {E B F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (Q : E →L[ℂ] B) (R : E →L[ℂ] F) :
    LinearMap.ker Q.toLinearMap →L[ℂ] F :=
  R.comp Q.ker.subtypeL

/-- Compactness survives restriction to the residual source gauge. -/
theorem residualGaugeReporter_isCompact
    {E B F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (Q : E →L[ℂ] B) (R : E →L[ℂ] F) (hR : IsCompactOperator R) :
    IsCompactOperator (residualGaugeReporter Q R) := by
  exact hR.comp_clm Q.ker.subtypeL

/-- The source boundary together with the reporter is injective exactly when the reporter is
injective on the residual gauge. -/
theorem prod_injective_iff_residualGaugeReporter_injective
    {E B F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (Q : E →L[ℂ] B) (R : E →L[ℂ] F) :
    Function.Injective (Q.prod R) ↔
      Function.Injective (residualGaugeReporter Q R) := by
  constructor
  · intro h x y hxy
    apply Subtype.ext
    apply h
    apply Prod.ext
    · simp
    · exact hxy
  · intro h x y hxy
    have hQ : Q x = Q y := congrArg Prod.fst hxy
    have hR : R x = R y := congrArg Prod.snd hxy
    have hsub : x - y ∈ LinearMap.ker Q.toLinearMap := by
      simpa [LinearMap.mem_ker] using sub_eq_zero.mpr hQ
    have hz : (⟨x - y, hsub⟩ : LinearMap.ker Q.toLinearMap) = 0 := by
      apply h
      simpa [residualGaugeReporter] using sub_eq_zero.mpr hR
    exact sub_eq_zero.mp (congrArg Subtype.val hz)

/-- **Source-gauge observability trichotomy.** Every source/reporter pair has an exact invisible
gauge, normalized approximate invisible gauges, or stable anti-Lipschitz gauge separation. -/
theorem sourceGaugeObservability_trichotomy
    {E B F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (Q : E →L[ℂ] B) (R : E →L[ℂ] F) :
    (¬ Function.Injective (Q.prod R)) ∨
      (Function.Injective (Q.prod R) ∧
        HasApproximateUnitKernel (residualGaugeReporter Q R)) ∨
      (Function.Injective (Q.prod R) ∧
        ∃ K, AntilipschitzWith K (residualGaugeReporter Q R)) := by
  letI : CompleteSpace (LinearMap.ker Q.toLinearMap) :=
    Q.isClosed_ker.completeSpace_coe
  by_cases hinj : Function.Injective (Q.prod R)
  · have hres : Function.Injective (residualGaugeReporter Q R) :=
      (prod_injective_iff_residualGaugeReporter_injective Q R).mp hinj
    by_cases hclosed : IsClosed (Set.range (residualGaugeReporter Q R))
    · exact Or.inr (Or.inr ⟨hinj,
        (residualGaugeReporter Q R).antilipschitz_of_injective_of_isClosed_range
          hres hclosed⟩)
    · exact Or.inr (Or.inl ⟨hinj,
        (hasApproximateUnitKernel_iff_not_isClosed_range
          (residualGaugeReporter Q R) hres).2 hclosed⟩)
  · exact Or.inl hinj

/-- **Compact-source observability wall.** If the residual source gauge is infinite-dimensional,
then a compact reporter which is algebraically conservative with the source still has normalized
gauge directions whose reporter signal tends to zero. Stable reconstruction therefore requires a
noncompact transverse channel. -/
theorem compact_sourceGaugeReporter_hasApproximateUnitKernel
    {E B F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (Q : E →L[ℂ] B) (R : E →L[ℂ] F) (hR : IsCompactOperator R)
    (hconservative : Function.Injective (Q.prod R))
    (hinfinite : ¬ FiniteDimensional ℂ (LinearMap.ker Q.toLinearMap)) :
    HasApproximateUnitKernel (residualGaugeReporter Q R) := by
  letI : CompleteSpace (LinearMap.ker Q.toLinearMap) :=
    Q.isClosed_ker.completeSpace_coe
  apply compact_injective_hasApproximateUnitKernel
    (residualGaugeReporter Q R)
    (residualGaugeReporter_isCompact Q R hR)
    ((prod_injective_iff_residualGaugeReporter_injective Q R).mp hconservative)
    hinfinite

section Hilbert

variable {E B F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The positive observability Gram operator of a reporter restricted to the residual source
gauge. -/
def residualGaugeGram (Q : E →L[ℂ] B) (R : E →L[ℂ] F) :
    LinearMap.ker Q.toLinearMap →L[ℂ] LinearMap.ker Q.toLinearMap := by
  letI : CompleteSpace (LinearMap.ker Q.toLinearMap) :=
    Q.isClosed_ker.completeSpace_coe
  exact (residualGaugeReporter Q R).adjoint ∘L (residualGaugeReporter Q R)

/-- The residual-gauge Gram operator is positive. -/
theorem residualGaugeGram_positive (Q : E →L[ℂ] B) (R : E →L[ℂ] F) :
    (residualGaugeGram Q R).IsPositive := by
  letI : CompleteSpace (LinearMap.ker Q.toLinearMap) :=
    Q.isClosed_ker.completeSpace_coe
  unfold residualGaugeGram
  exact ContinuousLinearMap.isPositive_adjoint_comp_self (residualGaugeReporter Q R)

/-- Algebraic source/reporter conservativity is exactly injectivity of the positive
residual-gauge Gram operator. -/
theorem prod_injective_iff_residualGaugeGram_injective
    (Q : E →L[ℂ] B) (R : E →L[ℂ] F) :
    Function.Injective (Q.prod R) ↔
      Function.Injective (residualGaugeGram Q R) := by
  letI : CompleteSpace (LinearMap.ker Q.toLinearMap) :=
    Q.isClosed_ker.completeSpace_coe
  rw [prod_injective_iff_residualGaugeReporter_injective]
  unfold residualGaugeGram
  simpa only [ContinuousLinearMap.coe_comp] using
    (residualGaugeReporter Q R).adjoint_comp_self_injective_iff.symm

end Hilbert

end

end GaloisForLFunctions
