import GaloisForLFunctions.ArithmeticIndexDescent.TheSectionProjectionConvergesInTheSourceGraph
import GaloisForLFunctions.HTGeometry.CoerciveOperatorInvertible

/-!
# A bounded arithmetic Weil projection on the entire source graph

The closed carrier of the actual arithmetic sections is coercive for the
original Weil form. Its compressed Weil operator is therefore invertible.
This constructs a bounded projection for every complete source vector, retaining
the signed complementary form. On literal tests it equals the finite-section
limit, so the two constructions describe the same arithmetic removal.
-/

open MeasureTheory Set
open scoped InnerProductSpace
open RHTower RHTower.CHMDDoobGraph RHTower.CHMDPolar Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics

theorem realTestGraphLift_smul (c : ℝ) (f : realTests) :
    realTestGraphLift (c • f) = c • realTestGraphLift f := by
  apply source_projection_injective
  apply Lp.ext
  filter_upwards [testLift_source (c • f).1 (c • f).2.1 (c • f).2.2,
    testLift_source f.1 f.2.1 f.2.2, Lp.coeFn_smul c (realTestGraphLift f).val.fst]
    with x h0 h1 h2
  change (realTestGraphLift (c • f)).val.fst x = (c • (realTestGraphLift f).val.fst) x
  change (realTestGraphLift (c • f)).val.fst x = phiDoobInv (c • f).1 x at h0
  change (realTestGraphLift f).val.fst x = phiDoobInv f.1 x at h1
  rw [h0, h2, Pi.smul_apply, h1]
  change (c * f.1 x) / riemannKernelReal x = c * (f.1 x / riemannKernelReal x)
  ring

/-- The literal compact-test lift as a linear source map. -/
def realTestGraphMap : realTests →ₗ[ℝ] SourceGraph where
  toFun := realTestGraphLift
  map_add' := realTestGraphLift_add
  map_smul' c f := by
    simpa only [RingHom.id_apply] using realTestGraphLift_smul c f

/-- The actual section source map, before taking its closure. -/
def arithmeticSectionGraphMap (N : ℕ) (w : ℝ) : arithmeticSectionTests N w →ₗ[ℝ] SourceGraph :=
  realTestGraphMap.comp (arithmeticSectionTests N w).subtype

/-- Closure of the literal arithmetic section range in the original graph norm. -/
def closedSectionGraph (N : ℕ) (w : ℝ) : Submodule ℝ SourceGraph :=
  (arithmeticSectionGraphMap N w).range.topologicalClosure

theorem mem_closedSectionGraph_iff (N : ℕ) (w : ℝ) (p : SourceGraph) :
    p ∈ closedSectionGraph N w ↔
      p ∈ closure (Set.range (fun q : arithmeticSectionTests N w => realTestGraphLift q.1)) := by
  change p ∈ closure (Set.range (arithmeticSectionGraphMap N w)) ↔ _
  rfl

theorem isClosed_closedSectionGraph (N : ℕ) (w : ℝ) :
    IsClosed (closedSectionGraph N w : Set SourceGraph) :=
  (arithmeticSectionGraphMap N w).range.isClosed_topologicalClosure

instance (N : ℕ) (w : ℝ) : CompleteSpace (closedSectionGraph N w) :=
  (isClosed_closedSectionGraph N w).completeSpace_coe

instance (N : ℕ) (w : ℝ) : (closedSectionGraph N w).HasOrthogonalProjection := inferInstance

private theorem graphWeil_add_left (p p' q : SourceGraph) :
    weilBilin (p + p') q = weilBilin p q + weilBilin p' q := by
  unfold weilBilin
  have hs : (p + p').val.fst = p.val.fst + p'.val.fst := rfl
  rw [hs]
  simp only [inner_add_left]
  ring

private theorem graphWeil_smul_left (c : ℝ) (p q : SourceGraph) :
    weilBilin (c • p) q = c * weilBilin p q := by
  unfold weilBilin
  have hs : (c • p).val.fst = c • p.val.fst := rfl
  rw [hs]
  simp only [inner_smul_graph, real_inner_smul_left]
  ring

private def graphWeilLinear : LinearMap.BilinForm ℝ SourceGraph :=
  LinearMap.mk₂ ℝ weilBilin graphWeil_add_left graphWeil_smul_left
    (fun p q q' => by
      rw [weilBilin_comm p (q + q'), graphWeil_add_left,
        weilBilin_comm q p, weilBilin_comm q' p])
    (fun c p q => by
      change weilBilin p (c • q) = c * weilBilin p q
      rw [weilBilin_comm, graphWeil_smul_left, weilBilin_comm q p])

/-- The original complete Weil pairing as a bounded bilinear map. -/
def graphWeilPairing : SourceGraph →L[ℝ] SourceGraph →L[ℝ] ℝ :=
  graphWeilLinear.mkContinuous₂ weilBilinConst fun p q => by
    change ‖weilBilin p q‖ ≤ weilBilinConst * ‖p‖ * ‖q‖
    simpa only [Real.norm_eq_abs, mul_assoc] using abs_weilBilin_le p q

/-- The bounded graph operator of the original full Weil form. -/
def graphWeilOperator : SourceGraph →L[ℝ] SourceGraph :=
  InnerProductSpace.continuousLinearMapOfBilin graphWeilPairing

theorem inner_graphWeilOperator (p q : SourceGraph) :
    inner ℝ (graphWeilOperator p) q = weilBilin p q :=
  InnerProductSpace.continuousLinearMapOfBilin_apply graphWeilPairing p q

variable {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw0 : 0 < w)
  (hw : w ≤ fullSectionRatio * atomSpacing N)

include hN hw0 hw

private theorem exists_closedSection_coercivity :
    ∃ κ : ℝ, 0 < κ ∧ ∀ p : closedSectionGraph N w,
      κ * ‖p‖ * ‖p‖ ≤ weilBilin (p : SourceGraph) (p : SourceGraph) := by
  obtain ⟨C, hC, hbound⟩ := exists_closedSection_graphNorm_bound hN hw0 hw
  refine ⟨C⁻¹, inv_pos.mpr hC, fun p => ?_⟩
  have hb := hbound p ((mem_closedSectionGraph_iff N w p).mp p.2)
  rw [weilForm_eq_weilBilin] at hb
  change ‖p‖ ^ 2 ≤ C * weilBilin (p : SourceGraph) (p : SourceGraph) at hb
  calc
    C⁻¹ * ‖p‖ * ‖p‖ = ‖p‖ ^ 2 / C := by ring
    _ ≤ _ := (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hb)

/-- Arithmetic coercivity constructs a bounded Weil projection for every graph vector. -/
theorem exists_closedSectionWeilProjection :
    ∃ P : SourceGraph →L[ℝ] SourceGraph, ∀ x : SourceGraph,
      P x ∈ closedSectionGraph N w ∧
        ∀ k ∈ closedSectionGraph N w, weilBilin k (x - P x) = 0 := by
  let K := closedSectionGraph N w
  obtain ⟨κ, hκ, hcoercive⟩ := exists_closedSection_coercivity hN hw0 hw
  let Q : SourceGraph →L[ℝ] K := K.orthogonalProjectionOnto.comp graphWeilOperator
  let T : K →L[ℝ] K := Q.comp K.subtypeL
  have hT : ∀ k : K, κ * ‖k‖ * ‖k‖ ≤ inner ℝ (T k) k := by
    intro k
    change κ * ‖k‖ * ‖k‖ ≤
      inner ℝ (K.orthogonalProjectionOnto (graphWeilOperator (k : SourceGraph))) k
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right, inner_graphWeilOperator]
    exact hcoercive k
  let e := HTGeometry.coerciveEquiv (V := K) (T := T) (κ := κ) hκ hT
  let P : SourceGraph →L[ℝ] SourceGraph := K.subtypeL.comp (e.symm.toContinuousLinearMap.comp Q)
  refine ⟨P, fun x => ⟨?_, ?_⟩⟩
  · change ((e.symm (Q x) : K) : SourceGraph) ∈ K
    exact (e.symm (Q x)).2
  · intro k hk
    let k' : K := ⟨k, hk⟩
    have he : T (e.symm (Q x)) = Q x := by
      rw [← HTGeometry.coerciveEquiv_apply (V := K) (T := T) (κ := κ) hκ hT]
      exact e.apply_symm_apply (Q x)
    have hi := congrArg (fun z : K => inner ℝ z k') he
    change inner ℝ (K.orthogonalProjectionOnto (graphWeilOperator (P x))) k' =
      inner ℝ (K.orthogonalProjectionOnto (graphWeilOperator x)) k' at hi
    simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right,
      inner_graphWeilOperator] at hi
    change weilBilin (P x) k = weilBilin x k at hi
    rw [weilBilin_sub_right, weilBilin_comm k x, weilBilin_comm k (P x)]
    exact sub_eq_zero.mpr hi.symm

/-- The bounded projection onto the closed arithmetic carrier for the original Weil form. -/
def closedSectionWeilProjection : SourceGraph →L[ℝ] SourceGraph :=
  Classical.choose (exists_closedSectionWeilProjection hN hw0 hw)

theorem closedSectionWeilProjection_mem (x : SourceGraph) :
    closedSectionWeilProjection hN hw0 hw x ∈ closedSectionGraph N w :=
  (Classical.choose_spec (exists_closedSectionWeilProjection hN hw0 hw) x).1

theorem closedSectionWeilProjection_orthogonal (x : SourceGraph) {k : SourceGraph}
    (hk : k ∈ closedSectionGraph N w) :
    weilBilin k (x - closedSectionWeilProjection hN hw0 hw x) = 0 :=
  (Classical.choose_spec (exists_closedSectionWeilProjection hN hw0 hw) x).2 k hk

/-- The arithmetic floor makes the original-form projection unique on the closed carrier. -/
theorem closedSectionWeilProjection_unique (x : SourceGraph) {p : SourceGraph}
    (hp : p ∈ closedSectionGraph N w)
    (horth : ∀ k ∈ closedSectionGraph N w, weilBilin k (x - p) = 0) :
    p = closedSectionWeilProjection hN hw0 hw x := by
  let q := closedSectionWeilProjection hN hw0 hw x
  have hq : q ∈ closedSectionGraph N w := closedSectionWeilProjection_mem hN hw0 hw x
  have hd := (closedSectionGraph N w).sub_mem hp hq
  have hp0 := horth (p - q) hd
  have hq0 := closedSectionWeilProjection_orthogonal hN hw0 hw x hd
  have he : weilBilin (p - q) (p - q) = 0 := by
    calc
      _ = weilBilin (p - q) ((x - q) - (x - p)) :=
        congrArg (weilBilin (p - q)) (by abel)
      _ = weilBilin (p - q) (x - q) - weilBilin (p - q) (x - p) :=
        weilBilin_sub_right (p - q) (x - q) (x - p)
      _ = 0 := by rw [hq0, hp0, sub_self]
  obtain ⟨C, _, hbound⟩ := exists_closedSection_graphNorm_bound hN hw0 hw
  have hb := hbound (p - q) ((mem_closedSectionGraph_iff N w (p - q)).mp hd)
  rw [weilForm_eq_weilBilin, he, mul_zero] at hb
  have hz : ‖p - q‖ ^ 2 = 0 := le_antisymm hb (sq_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- The bounded projection fixes the whole completed arithmetic carrier. -/
theorem closedSectionWeilProjection_fixes {x : SourceGraph} (hx : x ∈ closedSectionGraph N w) :
    closedSectionWeilProjection hN hw0 hw x = x := by
  symm
  apply closedSectionWeilProjection_unique hN hw0 hw x hx
  intro k _
  rw [sub_self]
  change graphWeilPairing k 0 = 0
  exact map_zero _

theorem closedSectionWeilProjection_idempotent (x : SourceGraph) :
    closedSectionWeilProjection hN hw0 hw (closedSectionWeilProjection hN hw0 hw x) =
      closedSectionWeilProjection hN hw0 hw x :=
  closedSectionWeilProjection_fixes hN hw0 hw (closedSectionWeilProjection_mem hN hw0 hw x)

/-- On literal tests, the bounded projection is exactly the canonical finite-subset limit. -/
theorem sectionGraphProjection_eq_closedSectionWeilProjection (g : realTests) :
    sectionGraphProjection hN hw0 hw g =
      closedSectionWeilProjection hN hw0 hw (realTestGraphLift g) := by
  apply closedSectionWeilProjection_unique hN hw0 hw (realTestGraphLift g)
  · exact (mem_closedSectionGraph_iff N w _).mpr
      (sectionGraphProjection_mem_closure hN hw0 hw g)
  · intro k hk
    exact sectionGraphResidual_orthogonal_closure hN hw0 hw
      ((mem_closedSectionGraph_iff N w k).mp hk) g

/-- Exact signed Schur subtraction holds on the entire original source graph. -/
theorem weilBilin_closedSectionWeilResidual (x y : SourceGraph) :
    weilBilin (x - closedSectionWeilProjection hN hw0 hw x)
        (y - closedSectionWeilProjection hN hw0 hw y) =
      weilBilin x y - weilBilin (closedSectionWeilProjection hN hw0 hw x)
        (closedSectionWeilProjection hN hw0 hw y) := by
  let P := closedSectionWeilProjection hN hw0 hw
  have hl := closedSectionWeilProjection_orthogonal hN hw0 hw y
    (closedSectionWeilProjection_mem hN hw0 hw x)
  have hr := closedSectionWeilProjection_orthogonal hN hw0 hw x
    (closedSectionWeilProjection_mem hN hw0 hw y)
  change weilBilin (P x) (y - P y) = 0 at hl
  change weilBilin (P y) (x - P x) = 0 at hr
  rw [weilBilin_sub_right] at hl hr
  rw [weilBilin_comm (P y) x, weilBilin_comm (P y) (P x)] at hr
  change weilBilin (x - P x) (y - P y) = weilBilin x y - weilBilin (P x) (P y)
  simp only [weilBilin_sub_left, weilBilin_sub_right]
  linarith only [hl, hr]

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_closedSectionWeilProjection
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.closedSectionWeilProjection_unique
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.sectionGraphProjection_eq_closedSectionWeilProjection
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.weilBilin_closedSectionWeilResidual
