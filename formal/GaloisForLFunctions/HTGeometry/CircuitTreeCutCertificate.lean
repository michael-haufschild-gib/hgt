import GaloisForLFunctions.HTGeometry.StaticLocalNestedThermodynamicRampReturnLaw
import GaloisForLFunctions.HTGeometry.TreeBooleanEdgeOrientation
import Mathlib.Data.Finset.Sym

/-!
# Tree cuts certified by two-qubit circuit support

An ancilla-free circuit with `G` two-qubit gates leaves a cut across all but at most `G` edges of
any prescribed spanning tree.  Every gate is wholly on one side of that cut.  Gate geometry may be
all-to-all; only support size and gate count enter.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The unique possible non-loop edge carried by a support of size two. -/
def gateTwoEdges (g : LocalGate Q) : Finset (Sym2 Q) :=
  if g.support.card = 2 then g.support.sym2.filter fun e => ¬e.IsDiag else ∅

/-- Distinct support edges used by the two-qubit gates of a circuit. -/
def circuitTwoEdges : List (LocalGate Q) → Finset (Sym2 Q)
  | [] => ∅
  | g :: c => gateTwoEdges g ∪ circuitTwoEdges c

def circuitSupportGraph (c : List (LocalGate Q)) : SimpleGraph Q :=
  SimpleGraph.fromEdgeSet (circuitTwoEdges c : Set (Sym2 Q))

theorem gateTwoEdges_card_le_one (g : LocalGate Q) :
    (gateTwoEdges g).card ≤ 1 := by
  unfold gateTwoEdges
  split_ifs with htwo
  · rw [Finset.card_le_one_iff]
    intro e f he hf
    simp only [Finset.mem_filter] at he hf
    rcases he with ⟨heS, heND⟩
    rcases hf with ⟨hfS, hfND⟩
    revert heS heND hfS hfND
    refine Sym2.inductionOn e ?_
    intro a b heS heND
    refine Sym2.inductionOn f ?_
    intro x y hfS hfND
    simp only [Finset.mk_mem_sym2_iff] at heS hfS
    have hab : a ≠ b := by simpa [Sym2.mk_isDiag_iff] using heND
    have hxy : x ≠ y := by simpa [Sym2.mk_isDiag_iff] using hfND
    have hpairAB : ({a, b} : Finset Q) = g.support := by
      apply Finset.eq_of_subset_of_card_le
      · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using heS
      · simpa [Finset.card_pair hab, htwo]
    have hpairXY : ({x, y} : Finset Q) = g.support := by
      apply Finset.eq_of_subset_of_card_le
      · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using hfS
      · simpa [Finset.card_pair hxy, htwo]
    have hsets : ({a, b} : Finset Q) = {x, y} := hpairAB.trans hpairXY.symm
    have hx : x = a ∨ x = b := by
      have : x ∈ ({a, b} : Finset Q) := by rw [hsets]; simp
      simpa [eq_comm] using this
    have hy : y = a ∨ y = b := by
      have : y ∈ ({a, b} : Finset Q) := by rw [hsets]; simp
      simpa [eq_comm] using this
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all
  · simp

theorem circuitTwoEdges_card_le_twoGateCount
    (c : List (LocalGate Q)) :
    (circuitTwoEdges c).card ≤
      c.countP fun g => g.support.card = 2 := by
  induction c with
  | nil => simp [circuitTwoEdges]
  | cons g c ih =>
      rw [circuitTwoEdges]
      refine le_trans (Finset.card_union_le _ _) ?_
      by_cases htwo : g.support.card = 2
      · rw [List.countP_cons]
        simp only [htwo, decide_true, if_true]
        exact (Nat.add_le_add (gateTwoEdges_card_le_one g) ih).trans_eq
          (Nat.add_comm 1 _)
      · simp [htwo, gateTwoEdges, ih]

theorem twoGateCount_eq_countP {L : ℕ}
    (c : List (LocalGate (PairQubit L))) :
    twoGateCount c = c.countP fun g => g.support.card = 2 := by
  induction c with
  | nil => rfl
  | cons g c ih =>
      rw [twoGateCount, List.countP_cons, ih]
      by_cases htwo : g.support.card = 2 <;> simp [htwo, Nat.add_comm]

noncomputable instance circuitSupportGraphFintypeEdgeSet
    (c : List (LocalGate Q)) : Fintype (circuitSupportGraph c).edgeSet :=
  Fintype.ofFinite _

theorem circuitSupportGraph_card_le_twoGateCount {L : ℕ}
    (c : List (LocalGate (PairQubit L))) :
    (circuitSupportGraph c).edgeFinset.card ≤ twoGateCount c := by
  have hsub : (circuitSupportGraph c).edgeFinset ⊆ circuitTwoEdges c := by
    intro e he
    have he' := SimpleGraph.mem_edgeFinset.mp he
    have he'' : e ∈ (circuitTwoEdges c : Set (Sym2 (PairQubit L))) \ Sym2.diagSet := by
      simpa only [circuitSupportGraph, SimpleGraph.edgeSet_fromEdgeSet] using he'
    exact he''.1
  refine le_trans (Finset.card_le_card hsub) ?_
  rw [twoGateCount_eq_countP]
  exact circuitTwoEdges_card_le_twoGateCount c

theorem circuitSupportGraph_adj_of_mem_support
    (c : List (LocalGate Q)) {g : LocalGate Q} (hg : g ∈ c)
    (htwo : g.support.card = 2) {u v : Q}
    (hu : u ∈ g.support) (hv : v ∈ g.support) (huv : u ≠ v) :
    (circuitSupportGraph c).Adj u v := by
  rw [circuitSupportGraph, SimpleGraph.fromEdgeSet_adj]
  refine ⟨?_, huv⟩
  change s(u, v) ∈ circuitTwoEdges c
  induction c with
  | nil => simp at hg
  | cons h c ih =>
      simp only [List.mem_cons] at hg
      rw [circuitTwoEdges, Finset.mem_union]
      rcases hg with rfl | hg
      · left
        simp [gateTwoEdges, htwo, hu, hv, huv]
      · exact Or.inr (ih hg)

theorem eq_of_reachable_of_adj_eq {G : SimpleGraph Q} {u v : Q}
    (hEq : ∀ ⦃a b⦄, G.Adj a b → (ε : Q → Bool) a = ε b)
    (hreach : G.Reachable u v) : ε u = ε v := by
  rcases hreach with ⟨p⟩
  induction p with
  | nil => rfl
  | cons h p ih => exact (hEq h).trans ih

/-- Every gate is monochromatic for the cut induced by a spanning-forest reachability class. -/
theorem gate_support_subset_or_disjoint_of_monochromatic
    {ε : Q → Bool} (g : LocalGate Q)
    (hmono : ∀ u ∈ g.support, ∀ v ∈ g.support, ε u = ε v)
    (A : Finset Q) (hA : ∀ q, q ∈ A ↔ ε q = true) :
    g.support ⊆ A ∨ Disjoint g.support A := by
  by_cases h : ∃ q ∈ g.support, q ∈ A
  · rcases h with ⟨q, hqg, hqA⟩
    left
    intro v hvg
    rw [hA]
    rw [← hmono q hqg v hvg]
    exact (hA q).mp hqA
  · right
    rw [Finset.disjoint_left]
    intro q hqg hqA
    exact h ⟨q, hqg, hqA⟩

theorem circuitMatrix_separatesAcross_of_gate_sides
    (c : List (LocalGate Q)) (A : Finset Q)
    (hsides : ∀ g ∈ c, g.support ⊆ A ∨ Disjoint g.support A) :
    SeparatesAcross A (circuitMatrix c) := by
  induction c with
  | nil => exact SeparatesAcross.one A
  | cons g c ih =>
      apply SeparatesAcross.mul
      · exact g.separates A (hsides g (by simp))
      · apply ih
        intro h hh
        exact hsides h (by simp [hh])

def edgeMonochromatic (ε : Q → Bool) : Sym2 Q → Bool :=
  Sym2.lift ⟨(fun u v => ε u == ε v), by intro u v; simp [eq_comm]⟩

@[simp] theorem edgeMonochromatic_mk (ε : Q → Bool) (u v : Q) :
    edgeMonochromatic ε s(u, v) = true ↔ ε u = ε v := by
  simp [edgeMonochromatic]

/-- **Circuit--tree cut certificate.**  For any target spanning tree, a circuit admits a cut across
all but at most as many target edges as it has two-qubit gates, while its matrix factorizes across
that cut. -/
theorem exists_tree_cut_separating_circuit {L : ℕ}
    (c : List (LocalGate (PairQubit L)))
    (P : SimpleGraph (PairQubit L)) [DecidableRel P.Adj] (hP : P.IsTree) :
    ∃ ε : PairQubit L → Bool, ∃ A : Finset (PairQubit L),
      (∀ q, q ∈ A ↔ ε q = true) ∧
      SeparatesAcross A (circuitMatrix c) ∧
      (P.edgeFinset.filter fun e => edgeMonochromatic ε e = true).card ≤
        twoGateCount c := by
  classical
  let C := circuitSupportGraph c
  obtain ⟨F, hFC, hFac, hreach⟩ := C.exists_isAcyclic_reachable_eq_le
  have hconn : (F ⊔ P).Connected := hP.connected.mono le_sup_right
  obtain ⟨T, hFT, hTsup, hTtree⟩ :=
    hconn.exists_isTree_le_of_le_of_isAcyclic le_sup_left hFac
  letI : Fintype F.edgeSet := Fintype.ofFinite _
  letI : Fintype T.edgeSet := Fintype.ofFinite _
  let label : PairQubit L → PairQubit L → Bool := fun u v =>
    if F.Adj u v then false else true
  have hsymm : BooleanEdgeFieldSymmetric T label := by
    intro u v huv
    simp only [label]
    rw [F.adj_comm]
  obtain ⟨ε, hε⟩ := exists_booleanOrientation_of_isTree hTtree label hsymm
  let A : Finset (PairQubit L) := Finset.univ.filter fun q => ε q = true
  have hA : ∀ q, q ∈ A ↔ ε q = true := by intro q; simp [A]
  have hFadj : ∀ ⦃u v⦄, F.Adj u v → ε u = ε v := by
    intro u v huv
    have hTuv : T.Adj u v := hFT huv
    have hc := hε hTuv
    simp only [label, huv, ↓reduceIte] at hc
    cases hεu : ε u <;> cases hεv : ε v <;> simp [hεu, hεv] at hc ⊢
  have hCmono : ∀ ⦃u v⦄, C.Adj u v → ε u = ε v := by
    intro u v huv
    have hFr : F.Reachable u v := by
      rw [hreach]
      exact huv.reachable
    exact eq_of_reachable_of_adj_eq hFadj hFr
  have hgateMono : ∀ g ∈ c, ∀ u ∈ g.support, ∀ v ∈ g.support, ε u = ε v := by
    intro g hg u hu v hv
    by_cases huv : u = v
    · exact congrArg ε huv
    · by_cases htwo : g.support.card = 2
      · exact hCmono (circuitSupportGraph_adj_of_mem_support c hg htwo hu hv huv)
      · have harity := g.arity_le_two
        have hle : g.support.card ≤ 1 := by omega
        have : u = v := by
          by_contra hne
          have hcard : ({u, v} : Finset (PairQubit L)).card ≤ 1 := by
            refine le_trans (Finset.card_le_card ?_) hle
            simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
            exact ⟨hu, hv⟩
          simp [Finset.card_pair hne] at hcard
        exact False.elim (huv this)
  have hsep : SeparatesAcross A (circuitMatrix c) := by
    apply circuitMatrix_separatesAcross_of_gate_sides
    intro g hg
    exact gate_support_subset_or_disjoint_of_monochromatic g (hgateMono g hg) A hA
  have hnewCross : ∀ e ∈ T.edgeFinset \ F.edgeFinset,
      edgeMonochromatic ε e ≠ true := by
    intro e he
    revert he
    refine Sym2.inductionOn e ?_
    intro u v he
    rcases Finset.mem_sdiff.mp he with ⟨heT, heF⟩
    have hTuv : T.Adj u v := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using heT
    have hnF : ¬F.Adj u v := by
      intro h
      exact heF (SimpleGraph.mem_edgeFinset.mpr (by
        simpa only [SimpleGraph.mem_edgeSet] using h))
    have hc := hε hTuv
    simp only [label, hnF, ↓reduceIte] at hc
    unfold edgeMonochromatic
    rw [Sym2.lift_mk]
    cases hεu : ε u <;> cases hεv : ε v <;> simp [hεu, hεv] at hc ⊢
  have hnewP : T.edgeFinset \ F.edgeFinset ⊆ P.edgeFinset := by
    intro e he
    rcases Finset.mem_sdiff.mp he with ⟨heT, heF⟩
    have hsup : e ∈ (F ⊔ P).edgeFinset :=
      SimpleGraph.edgeFinset_mono hTsup heT
    rw [SimpleGraph.edgeFinset_sup] at hsup
    rcases Finset.mem_union.mp hsup with h | h
    · exact False.elim (heF h)
    · exact h
  have hmonoSubset :
      P.edgeFinset.filter (fun e => edgeMonochromatic ε e = true) ⊆
        P.edgeFinset \ (T.edgeFinset \ F.edgeFinset) := by
    intro e he
    rcases Finset.mem_filter.mp he with ⟨heP, hemono⟩
    rw [Finset.mem_sdiff]
    exact ⟨heP, fun hnew => hnewCross e hnew hemono⟩
  have hFTedges : F.edgeFinset ⊆ T.edgeFinset := SimpleGraph.edgeFinset_mono hFT
  have hcardNew : (T.edgeFinset \ F.edgeFinset).card =
      P.edgeFinset.card - F.edgeFinset.card := by
    rw [Finset.card_sdiff_of_subset hFTedges]
    have hTc := hTtree.card_edgeFinset
    have hPc := hP.card_edgeFinset
    omega
  have hcardComplement :
      (P.edgeFinset \ (T.edgeFinset \ F.edgeFinset)).card = F.edgeFinset.card := by
    rw [Finset.card_sdiff_of_subset hnewP, hcardNew]
    have hFcard : F.edgeFinset.card ≤ P.edgeFinset.card := by
      have hle := Finset.card_le_card hFTedges
      have hTc := hTtree.card_edgeFinset
      have hPc := hP.card_edgeFinset
      omega
    omega
  refine ⟨ε, A, hA, hsep, ?_⟩
  refine le_trans (Finset.card_le_card hmonoSubset) ?_
  rw [hcardComplement]
  exact le_trans (Finset.card_le_card (SimpleGraph.edgeFinset_mono hFC))
    (circuitSupportGraph_card_le_twoGateCount c)

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
