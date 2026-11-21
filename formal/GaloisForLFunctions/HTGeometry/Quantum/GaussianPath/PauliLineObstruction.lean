import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PauliContextuality

/-!
# Claws in the nearest-neighbour Pauli frustration graph

The words Z₀Z₁, X₀, X₁ and X₁X₂ form an induced claw. The onsite
words Z₀ and Z₂ distinguish the leaves, so retaining one vertex per
twin class still leaves a claw in the graph of Projansky et al.
(arXiv:2611.26315, Definitions 2 and 4).
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-- Adjacency in the two-element intersection model of a line graph,
allowing two vertices to share a label only when they are twins. -/
structure TwinLineModel {ι : Type*} (adj : ι → ι → Prop) (ρ : Type*)
    [DecidableEq ρ] where
  rootEdge : ι → Finset ρ
  card_rootEdge : ∀ v, (rootEdge v).card = 2
  adj_iff : ∀ u v, rootEdge u ≠ rootEdge v →
    (adj u v ↔ ¬Disjoint (rootEdge u) (rootEdge v))
  twin : ∀ u v, rootEdge u = rootEdge v →
    ∀ w, w ≠ u → w ≠ v → (adj u w ↔ adj v w)

/-- Three disjoint sets cannot all meet a two-element set. -/
theorem finset_two_cannot_meet_three {ρ : Type*} [DecidableEq ρ]
    (S A B C : Finset ρ) (hS : S.card = 2)
    (hab : Disjoint A B) (hac : Disjoint A C) (hbc : Disjoint B C) :
    Disjoint S A ∨ Disjoint S B ∨ Disjoint S C := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨a, ha, haA⟩ := Finset.not_disjoint_iff.mp h.1
  obtain ⟨b, hb, hbB⟩ := Finset.not_disjoint_iff.mp h.2.1
  obtain ⟨c, hc, hcC⟩ := Finset.not_disjoint_iff.mp h.2.2
  have hab' : a ≠ b := fun e => Finset.disjoint_left.mp hab (e ▸ haA) hbB
  have hac' : a ≠ c := fun e => Finset.disjoint_left.mp hac (e ▸ haA) hcC
  have hbc' : b ≠ c := fun e => Finset.disjoint_left.mp hbc (e ▸ hbB) hcC
  have hsub : ({a, b, c} : Finset ρ) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hcard := Finset.card_le_card hsub
  simp [hab', hac', hbc', hS] at hcard

/-- An induced claw with pairwise distinguishable leaves survives identification of twins. -/
theorem isEmpty_twinLineModel_of_claw {ι ρ : Type*} [DecidableEq ρ]
    (adj : ι → ι → Prop) (symm : Symmetric adj) (irrefl : Irreflexive adj)
    (o a b c : ι) (h₁ : adj o a) (h₂ : adj o b) (h₃ : adj o c)
    (hab : ¬adj a b) (hac : ¬adj a c) (hbc : ¬adj b c)
    (wab : ∃ w, adj a w ∧ ¬adj b w)
    (wac : ∃ w, adj a w ∧ ¬adj c w)
    (wbc : ∃ w, adj b w ∧ ¬adj c w) :
    IsEmpty (TwinLineModel adj ρ) := by
  refine ⟨fun M => ?_⟩
  have leaf (x y : ι) (hxy : ¬adj x y) (hw : ∃ w, adj x w ∧ ¬adj y w) :
      M.rootEdge x ≠ M.rootEdge y := by
    rintro he
    obtain ⟨w, hx, hy⟩ := hw
    have hwx : w ≠ x := fun e => irrefl x (e ▸ hx)
    have hwy : w ≠ y := fun e => hxy (e ▸ hx)
    exact hy ((M.twin x y he w hwx hwy).mp hx)
  have eab := leaf a b hab wab
  have eac := leaf a c hac wac
  have ebc := leaf b c hbc wbc
  have center (x y : ι) (hey : adj o y) (hxy : ¬adj x y)
      (hexy : M.rootEdge x ≠ M.rootEdge y) : M.rootEdge o ≠ M.rootEdge x := by
    intro he
    have hyo : y ≠ o := fun e => irrefl o (e ▸ hey)
    have hyx : y ≠ x := fun e => hexy (congrArg M.rootEdge e.symm)
    exact hxy ((M.twin o x he y hyo hyx).mp hey)
  have eoa := center a b h₂ hab eab
  have eob := center b c h₃ hbc ebc
  have eoc := center c a h₁ (fun h => hac (symm h)) eac.symm
  have d (x y : ι) (e : M.rootEdge x ≠ M.rootEdge y) (h : ¬adj x y) :
      Disjoint (M.rootEdge x) (M.rootEdge y) :=
    Classical.byContradiction fun hd => h ((M.adj_iff x y e).mpr hd)
  rcases finset_two_cannot_meet_three _ _ _ _ (M.card_rootEdge o)
      (d a b eab hab) (d a c eac hac) (d b c ebc hbc) with hd | hd | hd
  · exact ((M.adj_iff o a eoa).mp h₁) hd
  · exact ((M.adj_iff o b eob).mp h₂) hd
  · exact ((M.adj_iff o c eoc).mp h₃) hd

variable {n : ℕ}

private theorem edge_endpoint_ne (e : Fin (n + 1)) : e.castSucc ≠ e.succ := by
  intro h
  exact Nat.ne_of_lt (Nat.lt_succ_self e.val) (congrArg Fin.val h)

/-- An onsite word anticommutes with a bond exactly where its axis differs
from the incident bond axis. -/
theorem commute_onsite_coupling_iff (i : Fin (n + 2)) (a : Fin 3)
    (e : Fin (n + 1)) (bc : Fin 3 × Fin 3) :
    Commute (finitePauliMatrix (onsiteWord i a)) (finitePauliMatrix (couplingWord e bc)) ↔
      (i = e.castSucc → a = bc.1) ∧ (i = e.succ → a = bc.2) := by
  rw [finitePauli_commute_iff_sign]
  change finitePauliConjugationSign (singlePauliAxisLabel i a) (couplingWord e bc) = 1 ↔ _
  rw [finitePauliConjugationSign_singlePauliAxisLabel]
  have hneg := neg_ne_self.mpr (one_ne_zero : (1 : ℂ) ≠ 0)
  by_cases hl : i = e.castSucc
  · subst i
    simp [couplingWord, boolPauliConjugationSign, edge_endpoint_ne e, apply_ite, hneg]
  · by_cases hr : i = e.succ
    · subst i
      simp [couplingWord, boolPauliConjugationSign, hl, apply_ite, hneg]
    · simp [couplingWord, boolPauliConjugationSign, hl, hr]

/-- Consecutive bonds commute exactly when their shared-site axes agree. -/
theorem commute_consecutive_coupling_iff (e f : Fin (n + 1)) (hef : e.succ = f.castSucc)
    (ab cd : Fin 3 × Fin 3) :
    Commute (finitePauliMatrix (couplingWord e ab)) (finitePauliMatrix (couplingWord f cd)) ↔
      ab.2 = cd.1 := by
  rw [finitePauli_commute_iff_sign, finitePauliConjugationSign]
  have hleft : e.castSucc ≠ f.castSucc := by rw [← hef]; exact edge_endpoint_ne e
  have hfar : e.castSucc ≠ f.succ := by
    exact ne_of_lt (lt_trans (show e.castSucc < e.succ from Nat.lt_succ_self e.val)
      (hef ▸ (show f.castSucc < f.succ from Nat.lt_succ_self f.val)))
  rw [Finset.prod_eq_single e.succ]
  · have hneg := neg_ne_self.mpr (one_ne_zero : (1 : ℂ) ≠ 0)
    simp [couplingWord, boolPauliConjugationSign, (edge_endpoint_ne e).symm, hef,
      hleft.symm, apply_ite, hneg]
  · intro j _ hj
    by_cases hl : j = e.castSucc
    · subst j
      simp [couplingWord, boolPauliConjugationSign, hleft, hfar]
    · simp [couplingWord, boolPauliConjugationSign, hl, hj]
  · exact fun h => (h (Finset.mem_univ _)).elim

/-- Six terms supported on the first three sites obstruct the line-graph
test even when all other coefficients are arbitrary. -/
theorem path_no_twinLineModel_of_first_three {ρ : Type*} [DecidableEq ρ]
    (u : PathShell (n + 1)) :
    u (.inr (0, 2, 2)) ≠ 0 → u (.inr (1, 0, 0)) ≠ 0 →
    u (.inl (0, 0)) ≠ 0 → u (.inl (1, 0)) ≠ 0 →
    u (.inl (0, 2)) ≠ 0 → u (.inl (2, 2)) ≠ 0 →
    IsEmpty (TwinLineModel (fun p q : ActivePathLabels u =>
      ¬Commute (finitePauliMatrix (pathWord p.1)) (finitePauliMatrix (pathWord q.1))) ρ) := by
  intro ho hc ha hb h₀ h₂
  let A (v : ActivePathLabels u) := finitePauliMatrix (pathWord v.1)
  let adj (v w : ActivePathLabels u) := ¬Commute (A v) (A w)
  let o : ActivePathLabels u := ⟨.inr (0, 2, 2), ho⟩
  let a : ActivePathLabels u := ⟨.inl (0, 0), ha⟩
  let b : ActivePathLabels u := ⟨.inl (1, 0), hb⟩
  let c : ActivePathLabels u := ⟨.inr (1, 0, 0), hc⟩
  let z₀ : ActivePathLabels u := ⟨.inl (0, 2), h₀⟩
  let z₂ : ActivePathLabels u := ⟨.inl (2, 2), h₂⟩
  let e₀ : Fin ((n + 1) + 1) := 0
  let e₁ : Fin ((n + 1) + 1) := 1
  have he₀l : e₀.castSucc = 0 := rfl
  have he₀r : e₀.succ = 1 := rfl
  have he₁l : e₁.castSucc = 1 := rfl
  have he₁r : e₁.succ = 2 := rfl
  have haxis : (0 : Fin 3) ≠ 2 := fun h => Nat.zero_ne_add_one 1 (congrArg Fin.val h)
  have hsites (i j : Fin ((n + 1) + 2)) (h : i.val ≠ j.val) : i ≠ j :=
    fun e => h (congrArg Fin.val e)
  have h01 : (0 : Fin ((n + 1) + 2)) ≠ 1 := hsites _ _ (Nat.zero_ne_add_one 0)
  have h02 : (0 : Fin ((n + 1) + 2)) ≠ 2 := hsites _ _ (Nat.zero_ne_add_one 1)
  have h12 : (1 : Fin ((n + 1) + 2)) ≠ 2 := hsites _ _
    (Nat.ne_of_lt (Nat.lt_succ_self 1))
  have h₁ : adj o a := fun h => haxis
    (((commute_onsite_coupling_iff 0 0 e₀ (2, 2)).mp h.symm).1 he₀l.symm)
  have h₂' : adj o b := fun h => haxis
    (((commute_onsite_coupling_iff 1 0 e₀ (2, 2)).mp h.symm).2 he₀r.symm)
  have h₃ : adj o c := fun h => haxis
    (((commute_consecutive_coupling_iff e₀ e₁ (he₀r.trans he₁l.symm)
      (2, 2) (0, 0)).mp h).symm)
  have hab : Commute (A a) (A b) := (commute_onsitePauli_iff 0 1 0 0).mpr (Or.inl h01)
  have hac : Commute (A a) (A c) := (commute_onsite_coupling_iff 0 0 e₁ (0, 0)).mpr
    ⟨fun _ => rfl, fun _ => rfl⟩
  have hbc : Commute (A b) (A c) := (commute_onsite_coupling_iff 1 0 e₁ (0, 0)).mpr
    ⟨fun _ => rfl, fun _ => rfl⟩
  have ha₀ : adj a z₀ := fun h => ((commute_onsitePauli_iff 0 0 0 2).mp h).elim
    (fun hne => hne rfl) haxis
  have hb₀ : Commute (A b) (A z₀) := (commute_onsitePauli_iff 1 0 0 2).mpr (Or.inl h01.symm)
  have hc₀ : Commute (A c) (A z₀) := ((commute_onsite_coupling_iff 0 2 e₁ (0, 0)).mpr
    ⟨fun h => (h01 (h.trans he₁l)).elim, fun h => (h02 (h.trans he₁r)).elim⟩).symm
  have hc₂ : adj c z₂ := fun h => haxis
    (((commute_onsite_coupling_iff 2 2 e₁ (0, 0)).mp h.symm).2 he₁r.symm).symm
  have hb₂ : Commute (A b) (A z₂) := (commute_onsitePauli_iff 1 2 0 2).mpr (Or.inl h12)
  exact isEmpty_twinLineModel_of_claw adj (fun h hc => h hc.symm)
    (fun x h => h (Commute.refl (A x))) o a c b h₁ h₃ h₂'
    (fun h => h hac) (fun h => h hab) (fun h => h hbc.symm)
    ⟨z₀, ha₀, fun h => h hc₀⟩ ⟨z₀, ha₀, fun h => h hb₀⟩ ⟨z₂, hc₂, fun h => h hb₂⟩

/-- Almost surely, every prefix with at least three sites fails the
line-graph criterion on the full Gaussian Pauli support, even up to twins. -/
theorem gaussian_path_ae_no_twinLineModel {ρ : Type*} [DecidableEq ρ] :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n,
      IsEmpty (TwinLineModel (fun p q : ActivePathLabels (pathPauliDisorderShell ω (n + 1)) =>
        ¬Commute (finitePauliMatrix (pathWord p.1)) (finitePauliMatrix (pathWord q.1))) ρ) := by
  filter_upwards [gaussian_path_ae_nonzero_coordinates] with ω hω
  intro n
  exact path_no_twinLineModel_of_first_three (pathPauliDisorderShell ω (n + 1))
    (hω (0, .inr (2, 2))) (hω (1, .inr (0, 0)))
    (hω (0, .inl 0)) (hω (1, .inl 0)) (hω (0, .inl 2)) (hω (2, .inl 2))

#print axioms isEmpty_twinLineModel_of_claw
#print axioms commute_consecutive_coupling_iff
#print axioms path_no_twinLineModel_of_first_three
#print axioms gaussian_path_ae_no_twinLineModel

end GaloisForLFunctions.HTGeometry
