import GaloisForLFunctions.ArithmeticIndexDescent.FixedCellsControlTheCompleteSourceGraph
import GaloisForLFunctions.ArithmeticIndexDescent.TheClosedSectionHasABoundedWeilProjection
import GaloisForLFunctions.RHTower.CHMDInfiniteCriticalModes
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# A bounded Weil projection on one fixed unbounded arithmetic carrier

The chosen integer-log cell widths control the complete graph uniformly over
all finite independent profiles. Their literal range closure retains this
coercivity, so compression of the original Weil operator constructs a unique
bounded projection. Exact signed Schur subtraction and a global operator-energy
bound retain the cost of removal. The actual cusp escape lies outside the
carrier, and the inherited infinite theta radical survives in its complement.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
open RHTower RHTower.CHMDDoobGraph RHTower.CHMDPolar Zeta23

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics

/-- Finitely supported independent profiles, each confined to its specified cell. -/
def cellProfileSpace (centres w : ℕ → ℝ) : Submodule ℝ (ℕ →₀ realTests) where
  carrier := {G | ∀ i u, w i / 2 < |u - centres i| → (G i).1 u = 0}
  zero_mem' := by intro i u _; rfl
  add_mem' := by
    intro G H hG hH i u hu
    change (G i).1 u + (H i).1 u = 0
    rw [hG i u hu, hH i u hu, add_zero]
  smul_mem' := by
    intro c G hG i u hu
    change c * (G i).1 u = 0
    rw [hG i u hu, mul_zero]

/-- Synthesis adds the actual test profiles, preserving all presentation relations. -/
def cellProfileSynthesis : (ℕ →₀ realTests) →ₗ[ℝ] realTests :=
  Finsupp.lsum ℝ (fun _ : ℕ => LinearMap.id)

/-- The linear space of actual finite cell sums. -/
def finiteCellTestSpace (centres w : ℕ → ℝ) : Submodule ℝ realTests :=
  (cellProfileSpace centres w).map cellProfileSynthesis

private theorem cellProfileSynthesis_eq_prefix (G : ℕ →₀ realTests) :
    cellProfileSynthesis G = ∑ i ∈ Finset.range (G.support.sup id + 1), G i := by
  have hs : G.support ⊆ Finset.range (G.support.sup id + 1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  change (∑ i ∈ G.support, G i) = _
  apply Finset.sum_subset hs
  intro i _ hi
  exact Finsupp.notMem_support_iff.mp hi

/-- One fixed arithmetic choice of widths pays the complete graph at every prefix. -/
def fixedLogGraphCellWidth : ℕ → ℝ :=
  Classical.choose exists_fixedLogCellWidths_graph_coercive

theorem fixedLogGraphCellWidth_pos (n : ℕ) : 0 < fixedLogGraphCellWidth n :=
  (Classical.choose_spec exists_fixedLogCellWidths_graph_coercive).1 n

theorem fixedLogGraphCellWidth_le_one (n : ℕ) : fixedLogGraphCellWidth n ≤ 1 :=
  (Classical.choose_spec exists_fixedLogCellWidths_graph_coercive).2.1 n

/-- Every finite independently profiled sum on the chosen integer-log cells. -/
def fixedLogCellTests : Submodule ℝ realTests :=
  finiteCellTestSpace (fun n => Real.log ((n : ℝ) + 1)) fixedLogGraphCellWidth

/-- The complete graph bound is uniform on the whole algebraic carrier. -/
theorem norm_fixedLogCellTest_le_weil (f : fixedLogCellTests) :
    ‖realTestGraphLift f.1‖ ^ 2 ≤ 2 * realWeilForm f.1 f.1 := by
  obtain ⟨G, hG, hsyn⟩ := Submodule.mem_map.mp f.2
  change cellProfileSynthesis G = f.1 at hsyn
  rw [← hsyn, cellProfileSynthesis_eq_prefix]
  exact (Classical.choose_spec exists_fixedLogCellWidths_graph_coercive).2.2 _ G
    (fun i _ u hu => hG i u hu)

/-- Closure of the literal unbounded arithmetic cell carrier in the original graph norm. -/
def closedFixedLogCellGraph : Submodule ℝ SourceGraph :=
  (fixedLogCellTests.map realTestGraphMap).topologicalClosure

theorem isClosed_closedFixedLogCellGraph :
    IsClosed (closedFixedLogCellGraph : Set SourceGraph) :=
  (fixedLogCellTests.map realTestGraphMap).isClosed_topologicalClosure

instance : CompleteSpace closedFixedLogCellGraph :=
  isClosed_closedFixedLogCellGraph.completeSpace_coe

instance : closedFixedLogCellGraph.HasOrthogonalProjection := inferInstance

/-- Source coercivity survives closure with the same universal constant. -/
theorem norm_closedFixedLogCellGraph_le_weil (p : closedFixedLogCellGraph) :
    ‖p‖ ^ 2 ≤ 2 * weilForm (p : SourceGraph) := by
  have hc : IsClosed {q : SourceGraph | ‖q‖ ^ 2 ≤ 2 * weilForm q} :=
    isClosed_le (continuous_norm.pow 2) (continuous_weilForm.const_mul 2)
  have hr : (fixedLogCellTests.map realTestGraphMap : Set SourceGraph) ⊆
      {q : SourceGraph | ‖q‖ ^ 2 ≤ 2 * weilForm q} := by
    intro q hq
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hq
    change ‖realTestGraphLift f‖ ^ 2 ≤ 2 * weilForm (realTestGraphLift f)
    rw [weilForm_realTestGraphLift]
    exact norm_fixedLogCellTest_le_weil ⟨f, hf⟩
  exact closure_minimal hr hc p.2

/-- The actual primitive cusp escape eventually lies outside this uniformly coercive carrier. -/
theorem eventually_cuspEscape_not_mem_closedFixedLogCellGraph :
    ∀ᶠ t : ℝ in atTop, CHMDEscape.normalized t ∉ closedFixedLogCellGraph := by
  filter_upwards [CHMDEscape.normalized_graph_norm_sq_two.eventually
      (lt_mem_nhds (by norm_num : (1 : ℝ) < 2)),
    weilForm_normalized_tendsto_zero.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)]
    with t ht hw
  intro hm
  have hbound := norm_closedFixedLogCellGraph_le_weil ⟨CHMDEscape.normalized t, hm⟩
  change ‖CHMDEscape.normalized t‖ ^ 2 ≤ 2 * weilForm (CHMDEscape.normalized t) at hbound
  linarith only [ht, hw, hbound]

/-- A uniform source floor gives a proper closed carrier, even without assuming an off-line zero. -/
theorem closedFixedLogCellGraph_ne_top : closedFixedLogCellGraph ≠ ⊤ := by
  intro he
  obtain ⟨t, ht⟩ := eventually_cuspEscape_not_mem_closedFixedLogCellGraph.exists
  apply ht
  rw [he]
  trivial

/-- The actual infinite carrier has a bounded original-form projection on the whole graph. -/
theorem exists_fixedLogCellWeilProjection :
    ∃ P : SourceGraph →L[ℝ] SourceGraph, ∀ x : SourceGraph,
      P x ∈ closedFixedLogCellGraph ∧
        ∀ k ∈ closedFixedLogCellGraph, weilBilin k (x - P x) = 0 := by
  let K := closedFixedLogCellGraph
  let Q : SourceGraph →L[ℝ] K := K.orthogonalProjectionOnto.comp graphWeilOperator
  let T : K →L[ℝ] K := Q.comp K.subtypeL
  have hT : ∀ k : K, (1 / 2 : ℝ) * ‖k‖ * ‖k‖ ≤ inner ℝ (T k) k := by
    intro k
    change (1 / 2 : ℝ) * ‖k‖ * ‖k‖ ≤
      inner ℝ (K.orthogonalProjectionOnto (graphWeilOperator (k : SourceGraph))) k
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right, inner_graphWeilOperator]
    have h := norm_closedFixedLogCellGraph_le_weil k
    rw [weilForm_eq_weilBilin] at h
    nlinarith only [h]
  let e := HTGeometry.coerciveEquiv (V := K) (T := T) (κ := 1 / 2) (by norm_num) hT
  let P : SourceGraph →L[ℝ] SourceGraph := K.subtypeL.comp (e.symm.toContinuousLinearMap.comp Q)
  refine ⟨P, fun x => ⟨?_, ?_⟩⟩
  · change ((e.symm (Q x) : K) : SourceGraph) ∈ K
    exact (e.symm (Q x)).2
  · intro k hk
    let k' : K := ⟨k, hk⟩
    have he : T (e.symm (Q x)) = Q x := by
      rw [← HTGeometry.coerciveEquiv_apply (V := K) (T := T) (κ := 1 / 2) (by norm_num) hT]
      exact e.apply_symm_apply (Q x)
    have hi := congrArg (fun z : K => inner ℝ z k') he
    change inner ℝ (K.orthogonalProjectionOnto (graphWeilOperator (P x))) k' =
      inner ℝ (K.orthogonalProjectionOnto (graphWeilOperator x)) k' at hi
    simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
      inner_graphWeilOperator] at hi
    change weilBilin (P x) k = weilBilin x k at hi
    rw [weilBilin_sub_right, weilBilin_comm k x, weilBilin_comm k (P x)]
    exact sub_eq_zero.mpr hi.symm

/-- The full Weil projection onto the fixed unbounded integer-log carrier. -/
def fixedLogCellWeilProjection : SourceGraph →L[ℝ] SourceGraph :=
  Classical.choose exists_fixedLogCellWeilProjection

theorem fixedLogCellWeilProjection_mem (x : SourceGraph) :
    fixedLogCellWeilProjection x ∈ closedFixedLogCellGraph :=
  (Classical.choose_spec exists_fixedLogCellWeilProjection x).1

theorem fixedLogCellWeilProjection_orthogonal (x : SourceGraph) {k : SourceGraph}
    (hk : k ∈ closedFixedLogCellGraph) :
    weilBilin k (x - fixedLogCellWeilProjection x) = 0 :=
  (Classical.choose_spec exists_fixedLogCellWeilProjection x).2 k hk

/-- The source-derived graph floor makes the projection unique. -/
theorem fixedLogCellWeilProjection_unique (x : SourceGraph) {p : SourceGraph}
    (hp : p ∈ closedFixedLogCellGraph)
    (horth : ∀ k ∈ closedFixedLogCellGraph, weilBilin k (x - p) = 0) :
    p = fixedLogCellWeilProjection x := by
  let q := fixedLogCellWeilProjection x
  have hq : q ∈ closedFixedLogCellGraph := fixedLogCellWeilProjection_mem x
  have hd := closedFixedLogCellGraph.sub_mem hp hq
  have hp0 := horth (p - q) hd
  have hq0 := fixedLogCellWeilProjection_orthogonal x hd
  have he : weilBilin (p - q) (p - q) = 0 := by
    calc
      _ = weilBilin (p - q) ((x - q) - (x - p)) :=
        congrArg (weilBilin (p - q)) (by abel)
      _ = weilBilin (p - q) (x - q) - weilBilin (p - q) (x - p) :=
        weilBilin_sub_right (p - q) (x - q) (x - p)
      _ = 0 := by rw [hq0, hp0, sub_self]
  have hb := norm_closedFixedLogCellGraph_le_weil ⟨p - q, hd⟩
  change ‖p - q‖ ^ 2 ≤ 2 * weilForm (p - q) at hb
  rw [weilForm_eq_weilBilin, he, mul_zero] at hb
  have hz : ‖p - q‖ ^ 2 = 0 := le_antisymm hb (sq_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

theorem fixedLogCellWeilProjection_fixes {x : SourceGraph}
    (hx : x ∈ closedFixedLogCellGraph) : fixedLogCellWeilProjection x = x := by
  symm
  apply fixedLogCellWeilProjection_unique x hx
  intro k _
  rw [sub_self]
  change graphWeilPairing k 0 = 0
  exact map_zero _

theorem fixedLogCellWeilProjection_idempotent (x : SourceGraph) :
    fixedLogCellWeilProjection (fixedLogCellWeilProjection x) =
      fixedLogCellWeilProjection x :=
  fixedLogCellWeilProjection_fixes (fixedLogCellWeilProjection_mem x)

/-- The signed complement is exact on every graph vector, including both global poles. -/
theorem weilBilin_fixedLogCellResidual (x y : SourceGraph) :
    weilBilin (x - fixedLogCellWeilProjection x) (y - fixedLogCellWeilProjection y) =
      weilBilin x y - weilBilin (fixedLogCellWeilProjection x) (fixedLogCellWeilProjection y) := by
  let P := fixedLogCellWeilProjection
  have hl := fixedLogCellWeilProjection_orthogonal y (fixedLogCellWeilProjection_mem x)
  have hr := fixedLogCellWeilProjection_orthogonal x (fixedLogCellWeilProjection_mem y)
  change weilBilin (P x) (y - P y) = 0 at hl
  change weilBilin (P y) (x - P x) = 0 at hr
  rw [weilBilin_sub_right] at hl hr
  rw [weilBilin_comm (P y) x, weilBilin_comm (P y) (P x)] at hr
  change weilBilin (x - P x) (y - P y) = weilBilin x y - weilBilin (P x) (P y)
  simp only [weilBilin_sub_left, weilBilin_sub_right]
  linarith only [hl, hr]

/-- Orthogonality reads removed energy against the actual bounded Weil operator. -/
theorem weilForm_fixedLogCellWeilProjection (x : SourceGraph) :
    weilForm (fixedLogCellWeilProjection x) =
      inner ℝ (graphWeilOperator x) (fixedLogCellWeilProjection x) := by
  have h := fixedLogCellWeilProjection_orthogonal x (fixedLogCellWeilProjection_mem x)
  rw [weilBilin_sub_right] at h
  rw [inner_graphWeilOperator, weilForm_eq_weilBilin,
    ← weilBilin_comm (fixedLogCellWeilProjection x) x]
  exact (sub_eq_zero.mp h).symm

/-- The whole unbounded carrier has a universal source-operator Schur cost. -/
theorem fixedLogCellWeilProjection_cost_le (x : SourceGraph) :
    weilForm (fixedLogCellWeilProjection x) ≤ 2 * ‖graphWeilOperator x‖ ^ 2 := by
  have hcoer := norm_closedFixedLogCellGraph_le_weil
    ⟨fixedLogCellWeilProjection x, fixedLogCellWeilProjection_mem x⟩
  change ‖fixedLogCellWeilProjection x‖ ^ 2 ≤
    2 * weilForm (fixedLogCellWeilProjection x) at hcoer
  have hupper : weilForm (fixedLogCellWeilProjection x) ≤
      ‖graphWeilOperator x‖ * ‖fixedLogCellWeilProjection x‖ := by
    rw [weilForm_fixedLogCellWeilProjection]
    exact (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  nlinarith only [hcoer, hupper,
    sq_nonneg (‖fixedLogCellWeilProjection x‖ - 2 * ‖graphWeilOperator x‖)]

/-- Full graph removal has a uniform bound independent of aperture and profile count. -/
theorem norm_fixedLogCellWeilProjection_sq_le (x : SourceGraph) :
    ‖fixedLogCellWeilProjection x‖ ^ 2 ≤ 4 * ‖graphWeilOperator x‖ ^ 2 := by
  have hcoer := norm_closedFixedLogCellGraph_le_weil
    ⟨fixedLogCellWeilProjection x, fixedLogCellWeilProjection_mem x⟩
  change ‖fixedLogCellWeilProjection x‖ ^ 2 ≤
    2 * weilForm (fixedLogCellWeilProjection x) at hcoer
  linarith only [hcoer, fixedLogCellWeilProjection_cost_le x]

/-- The original signed residual retains a global lower bound with its source cost displayed. -/
theorem weilForm_fixedLogCellResidual_lower (x : SourceGraph) :
    weilForm x - 2 * ‖graphWeilOperator x‖ ^ 2 ≤
      weilForm (x - fixedLogCellWeilProjection x) := by
  rw [weilForm_eq_weilBilin (x - fixedLogCellWeilProjection x),
    weilBilin_fixedLogCellResidual, ← weilForm_eq_weilBilin x,
    ← weilForm_eq_weilBilin (fixedLogCellWeilProjection x)]
  linarith only [fixedLogCellWeilProjection_cost_le x]

/-- The complete polar correction preserves the inherited exact theta radical. -/
theorem graphWeilPair_critical (a : ℝ) (ha : 1 < 2 * Real.exp (-2 * |a|))
    (q : SourceGraph) : weilBilin (CHMDThetaTranslate.critical a ha) q = 0 := by
  let p := CHMDThetaTranslate.critical a ha
  have h1 : inner ℝ p.val.fst oneL = 0 := by
    rw [oneL_eq_constantLift]
    exact CHMDThetaTranslate.critical_primitive a ha
  have h2 : inner ℝ p.val.fst tanhL = 0 := critical_inner_tanhL a ha
  have hrad := CHMDThetaTranslate.critical_jump_identity a ha q
  change inner ℝ p.val.snd q.val.snd = inner ℝ p.val.fst q.val.fst at hrad
  change weilBilin p q = 0
  unfold weilBilin
  simp only [h1, h2, zero_mul, mul_zero, add_zero, sub_zero]
  change (inner ℝ p.val.fst q.val.fst + inner ℝ p.val.snd q.val.snd) -
    2 * inner ℝ p.val.fst q.val.fst = 0
  rw [hrad]
  ring

/-- Every exact theta critical mode is retained by the signed residual. -/
theorem fixedLogCellWeilProjection_critical (a : ℝ)
    (ha : 1 < 2 * Real.exp (-2 * |a|)) :
    fixedLogCellWeilProjection (CHMDThetaTranslate.critical a ha) = 0 := by
  symm
  apply fixedLogCellWeilProjection_unique _ closedFixedLogCellGraph.zero_mem
  intro k _
  rw [sub_zero, weilBilin_comm]
  exact graphWeilPair_critical a ha k

/-- The complementary graph contains an actual infinite independent zero-energy family. -/
theorem exists_infinite_critical_fixedLogCellResidual :
    ∃ p : ℕ → SourceGraph, LinearIndependent ℝ p ∧
      ∀ n, fixedLogCellWeilProjection (p n) = 0 ∧ weilForm (p n) = 0 := by
  refine ⟨CHMDThetaTranslate.sequence, CHMDThetaTranslate.sequence_linearIndependent, fun n => ?_⟩
  exact ⟨fixedLogCellWeilProjection_critical _ _, weilForm_critical _ _⟩

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.norm_fixedLogCellTest_le_weil
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.norm_closedFixedLogCellGraph_le_weil
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_fixedLogCellWeilProjection
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.weilBilin_fixedLogCellResidual

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.eventually_cuspEscape_not_mem_closedFixedLogCellGraph

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_infinite_critical_fixedLogCellResidual

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.fixedLogCellWeilProjection_cost_le
