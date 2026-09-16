import Mathlib.Combinatorics.Matroid.Closure
import Mathlib.Data.Finset.Max
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic

/-!
# Weighted matroid greedy stability

This file gives a closure characterization of deterministic weighted greedy selection. It
formalizes the monotonicity mechanism used in the matroid-secretary paper: decreasing competing
weights while fixing one selected element cannot remove that element. It also proves directly
that the closure characterization always selects an independent set.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

/-- Descending weight, followed by the ambient order as a deterministic tie-breaker. -/
noncomputable def weightedGreedyKey {α : Type*} [LinearOrder α]
    (w : α → ℝ) (e : α) : OrderDual ℝ ×ₗ α :=
  toLex (OrderDual.toDual (w e), e)

/-- Available elements considered before `e` by descending-weight greedy selection. -/
noncomputable def weightedPredecessors {α : Type*} [LinearOrder α]
    (V : Finset α) (w : α → ℝ) (e : α) : Set α :=
  {f | f ∈ V ∧ (w e < w f ∨ (w e = w f ∧ f < e))}

theorem mem_weightedPredecessors_iff_key_lt {α : Type*} [LinearOrder α]
    (V : Finset α) (w : α → ℝ) (e f : α) :
    f ∈ weightedPredecessors V w e ↔
      f ∈ V ∧ weightedGreedyKey w f < weightedGreedyKey w e := by
  simp [weightedPredecessors, weightedGreedyKey, Prod.Lex.toLex_lt_toLex, eq_comm]

/-- The deterministic weighted greedy set, expressed without an executable scan. -/
noncomputable def matroidGreedySet {α : Type*} [LinearOrder α]
    (M : Matroid α) (V : Finset α) (w : α → ℝ) : Finset α := by
  classical
  exact V.filter fun e => 0 < w e ∧ e ∉ M.closure (weightedPredecessors V w e)

theorem mem_matroidGreedySet {α : Type*} [LinearOrder α]
    (M : Matroid α) (V : Finset α) (w : α → ℝ) (e : α) :
    e ∈ matroidGreedySet M V w ↔
      e ∈ V ∧ 0 < w e ∧ e ∉ M.closure (weightedPredecessors V w e) := by
  classical
  simp [matroidGreedySet]

/-- If every available weight decreases while `e`'s weight stays fixed, the predecessor set of
`e` can only shrink. -/
theorem weightedPredecessors_mono_of_le_of_eq {α : Type*} [LinearOrder α]
    {V : Finset α} {w w' : α → ℝ} {e : α}
    (hle : ∀ f ∈ V, w' f ≤ w f) (heq : w' e = w e) :
    weightedPredecessors V w' e ⊆ weightedPredecessors V w e := by
  intro f hf
  rcases hf with ⟨hfV, hbefore⟩
  refine ⟨hfV, ?_⟩
  rcases hbefore with hlt | ⟨hfeq, hlabel⟩
  · left
    calc
      w e = w' e := heq.symm
      _ < w' f := hlt
      _ ≤ w f := hle f hfV
  · have hwe : w e ≤ w f := by
      calc
        w e = w' e := heq.symm
        _ = w' f := hfeq
        _ ≤ w f := hle f hfV
    rcases hwe.eq_or_lt with hsame | hstrict
    · right
      exact ⟨hsame, hlabel⟩
    · exact Or.inl hstrict

/-- Greedy monotonicity: lowering competing weights cannot remove a selected element whose own
weight remains fixed. -/
theorem mem_matroidGreedySet_of_weights_decrease {α : Type*} [LinearOrder α]
    (M : Matroid α) {V : Finset α} {w w' : α → ℝ} {e : α}
    (hle : ∀ f ∈ V, w' f ≤ w f) (heq : w' e = w e)
    (he : e ∈ matroidGreedySet M V w) :
    e ∈ matroidGreedySet M V w' := by
  rw [mem_matroidGreedySet] at he ⊢
  refine ⟨he.1, ?_⟩
  rw [heq]
  refine ⟨he.2.1, ?_⟩
  intro hclosure
  exact he.2.2 (M.closure_mono
    (weightedPredecessors_mono_of_le_of_eq hle heq) hclosure)

/-- The closure-characterized greedy set is independent whenever the available elements lie in
the matroid ground set. -/
theorem matroidGreedySet_indep {α : Type*} [LinearOrder α]
    (M : Matroid α) (V : Finset α) (w : α → ℝ) (hVE : (V : Set α) ⊆ M.E) :
    M.Indep (matroidGreedySet M V w : Set α) := by
  classical
  have haux : ∀ G : Finset α, G ⊆ matroidGreedySet M V w → M.Indep (G : Set α) := by
    intro G
    induction G using Finset.strongInduction with
    | _ G ih =>
        intro hG
        by_cases hGe : G = ∅
        · subst G
          rw [Finset.coe_empty]
          exact M.empty_indep
        have hGne : G.Nonempty := Finset.nonempty_iff_ne_empty.mpr hGe
        obtain ⟨e, heG, hmax⟩ := Finset.exists_max_image G (weightedGreedyKey w) hGne
        have herase : G.erase e ⊂ G := Finset.erase_ssubset heG
        have hInd : M.Indep (G.erase e : Set α) :=
          ih (G.erase e) herase ((Finset.erase_subset e G).trans hG)
        have heGreedy := hG heG
        rw [mem_matroidGreedySet] at heGreedy
        have hsub : (G.erase e : Set α) ⊆ weightedPredecessors V w e := by
          intro f hf
          have hfErase : f ∈ G.erase e := hf
          have hfG : f ∈ G := (Finset.mem_erase.mp hfErase).2
          have hfne : f ≠ e := (Finset.mem_erase.mp hfErase).1
          have hkeyne : weightedGreedyKey w f ≠ weightedGreedyKey w e := by
            intro hkey
            apply hfne
            simpa [weightedGreedyKey] using
              congrArg (fun x : OrderDual ℝ ×ₗ α => (ofLex x).2) hkey
          have hkeylt : weightedGreedyKey w f < weightedGreedyKey w e :=
            lt_of_le_of_ne (hmax f hfG) hkeyne
          rw [mem_weightedPredecessors_iff_key_lt]
          exact ⟨((mem_matroidGreedySet M V w f).mp (hG hfG)).1, hkeylt⟩
        have hnot : e ∉ M.closure (G.erase e : Set α) := by
          intro hecl
          exact heGreedy.2.2 (M.closure_mono hsub hecl)
        have heGround : e ∈ M.E := hVE heGreedy.1
        have hInsert : M.Indep (insert e (G.erase e : Set α)) :=
          (hInd.notMem_closure_iff_of_notMem (by simp) heGround).mp hnot
        simpa [Finset.coe_erase, heG] using hInsert
  exact haux _ (fun _ => id)

/-! ## One-coordinate sensitivity -/

/-- Two weight functions which agree away from `e` have identical predecessor sets after deleting
`e`. -/
theorem weightedPredecessors_sdiff_singleton_eq_of_eq_off {α : Type*} [LinearOrder α]
    {V : Finset α} {w w' : α → ℝ} {e f : α} (hfe : f ≠ e)
    (hoff : ∀ x, x ≠ e → w x = w' x) :
    weightedPredecessors V w f \ {e} = weightedPredecessors V w' f \ {e} := by
  ext x
  by_cases hxe : x = e
  · simp [hxe]
  · simp [weightedPredecessors, hxe, hoff x hxe, hoff f hfe]

theorem subset_insert_sdiff_singleton {α : Type*} (P : Set α) (e : α) :
    P ⊆ insert e (P \ {e}) := by
  intro x hx
  by_cases hxe : x = e
  · simp [hxe]
  · exact mem_insert_iff.mpr (Or.inr ⟨hx, by simpa using hxe⟩)

/-- Elements strictly earlier than `f`, together with `f`, are strictly earlier than every later
element `g`; deleting a distinguished element preserves this prefix inclusion. -/
theorem insert_predecessors_sdiff_subset_of_key_lt {α : Type*} [LinearOrder α]
    {V : Finset α} {w : α → ℝ} {e f g : α} (hfe : f ≠ e) (hfV : f ∈ V)
    (hfg : weightedGreedyKey w f < weightedGreedyKey w g) :
    insert f (weightedPredecessors V w f \ {e}) ⊆
      weightedPredecessors V w g \ {e} := by
  intro x hx
  rcases hx with rfl | hx
  · refine ⟨?_, by simpa using hfe⟩
    rw [mem_weightedPredecessors_iff_key_lt]
    exact ⟨hfV, hfg⟩
  · refine ⟨?_, hx.2⟩
    have hxP := hx.1
    rw [mem_weightedPredecessors_iff_key_lt] at hxP ⊢
    exact ⟨hxP.1, lt_trans hxP.2 hfg⟩

/-- Membership changed between two greedy sets. -/
def GreedyMembershipChanged {α : Type*} [LinearOrder α]
    (M : Matroid α) (V : Finset α) (w w' : α → ℝ) (f : α) : Prop :=
  Xor (f ∈ matroidGreedySet M V w) (f ∈ matroidGreedySet M V w')

theorem mem_available_of_greedyMembershipChanged {α : Type*} [LinearOrder α]
    {M : Matroid α} {V : Finset α} {w w' : α → ℝ} {f : α}
    (h : GreedyMembershipChanged M V w w' f) : f ∈ V := by
  rcases h with h | h
  · exact (mem_matroidGreedySet M V w f).mp h.1 |>.1
  · exact (mem_matroidGreedySet M V w' f).mp h.1 |>.1

/-- If the membership of `f ≠ e` changes after changing only `e`'s weight, then `f` and `e`
exchange across the closure of the common predecessor prefix. -/
theorem closure_exchange_witness_of_greedyMembershipChanged
    {α : Type*} [LinearOrder α] (M : Matroid α) {V : Finset α}
    {w w' : α → ℝ} {e f : α} (hfe : f ≠ e)
    (hoff : ∀ x, x ≠ e → w x = w' x)
    (hchange : GreedyMembershipChanged M V w w' f) :
    f ∈ M.closure (insert e (weightedPredecessors V w f \ {e})) \
        M.closure (weightedPredecessors V w f \ {e}) := by
  let P := weightedPredecessors V w f
  let Q := weightedPredecessors V w' f
  let X := P \ {e}
  have hXQ : X = Q \ {e} :=
    weightedPredecessors_sdiff_singleton_eq_of_eq_off hfe hoff
  have hfVpos : f ∈ V ∧ 0 < w f := by
    rcases hchange with h | h
    · have hmem := (mem_matroidGreedySet M V w f).mp h.1
      exact ⟨hmem.1, hmem.2.1⟩
    · have hmem := (mem_matroidGreedySet M V w' f).mp h.1
      exact ⟨hmem.1, by simpa [hoff f hfe] using hmem.2.1⟩
  have hfpos' : 0 < w' f := by simpa [← hoff f hfe] using hfVpos.2
  have hselP : f ∈ matroidGreedySet M V w ↔ f ∉ M.closure P := by
    simpa [P, hfVpos.1, hfVpos.2] using mem_matroidGreedySet M V w f
  have hselQ : f ∈ matroidGreedySet M V w' ↔ f ∉ M.closure Q := by
    simpa [Q, hfVpos.1, hfpos'] using mem_matroidGreedySet M V w' f
  have hcldiff : ¬(f ∈ M.closure P ↔ f ∈ M.closure Q) := by
    intro hiff
    rcases hchange with h | h
    · have hnP : f ∉ M.closure P := hselP.mp h.1
      have hQ : f ∈ M.closure Q := by
        by_contra hnQ
        exact h.2 (hselQ.mpr hnQ)
      exact hnP (hiff.mpr hQ)
    · have hnQ : f ∉ M.closure Q := hselQ.mp h.1
      have hP : f ∈ M.closure P := by
        by_contra hnP
        exact h.2 (hselP.mpr hnP)
      exact hnQ (hiff.mp hP)
  have hXP : X ⊆ P := sdiff_subset
  have hXQsub : X ⊆ Q := by
    rw [hXQ]
    exact sdiff_subset
  have hPbig : P ⊆ insert e X := subset_insert_sdiff_singleton P e
  have hQbig : Q ⊆ insert e X := by
    rw [hXQ]
    exact subset_insert_sdiff_singleton Q e
  refine ⟨?_, ?_⟩
  · by_contra hfbig
    have hnP : f ∉ M.closure P := fun hfP =>
      hfbig (M.closure_mono hPbig hfP)
    have hnQ : f ∉ M.closure Q := fun hfQ =>
      hfbig (M.closure_mono hQbig hfQ)
    exact hcldiff ⟨fun hfP => (hnP hfP).elim, fun hfQ => (hnQ hfQ).elim⟩
  · intro hfX
    have hfP : f ∈ M.closure P := M.closure_mono hXP hfX
    have hfQ : f ∈ M.closure Q := M.closure_mono hXQsub hfX
    exact hcldiff ⟨fun _ => hfQ, fun _ => hfP⟩

/-- **One-coordinate sensitivity.** Changing only `e`'s weight can change membership of at most
one other element in the deterministic weighted greedy set. -/
theorem greedyMembershipChanged_off_coordinate_subsingleton
    {α : Type*} [LinearOrder α] (M : Matroid α) (V : Finset α)
    (w w' : α → ℝ) (e : α) (hoff : ∀ x, x ≠ e → w x = w' x) :
    {f | f ≠ e ∧ GreedyMembershipChanged M V w w' f}.Subsingleton := by
  intro f hf g hg
  by_contra hfg
  have hkeyne : weightedGreedyKey w f ≠ weightedGreedyKey w g := by
    intro hkey
    apply hfg
    simpa [weightedGreedyKey] using
      congrArg (fun x : OrderDual ℝ ×ₗ α => (ofLex x).2) hkey
  rcases lt_or_gt_of_ne hkeyne with hkey | hkey
  · have hfexchange := M.closure_exchange
      (closure_exchange_witness_of_greedyMembershipChanged M hf.1 hoff hf.2)
    have hfgPrefix := insert_predecessors_sdiff_subset_of_key_lt hf.1
      (mem_available_of_greedyMembershipChanged hf.2) hkey
    have heG : e ∈ M.closure (weightedPredecessors V w g \ {e}) :=
      M.closure_mono hfgPrefix hfexchange.1
    have hgwitness := closure_exchange_witness_of_greedyMembershipChanged M hg.1 hoff hg.2
    apply hgwitness.2
    rw [← M.closure_insert_eq_of_mem_closure heG]
    exact hgwitness.1
  · have hgexchange := M.closure_exchange
      (closure_exchange_witness_of_greedyMembershipChanged M hg.1 hoff hg.2)
    have hgfPrefix := insert_predecessors_sdiff_subset_of_key_lt hg.1
      (mem_available_of_greedyMembershipChanged hg.2) hkey
    have heF : e ∈ M.closure (weightedPredecessors V w f \ {e}) :=
      M.closure_mono hgfPrefix hgexchange.1
    have hfwitness := closure_exchange_witness_of_greedyMembershipChanged M hf.1 hoff hf.2
    apply hfwitness.2
    rw [← M.closure_insert_eq_of_mem_closure heF]
    exact hfwitness.1

end GaloisForLFunctions.HTGeometry
