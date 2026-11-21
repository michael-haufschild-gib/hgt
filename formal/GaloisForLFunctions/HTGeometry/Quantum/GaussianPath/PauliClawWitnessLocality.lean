import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PauliThresholdObstruction

/-!
# Locality of claws that survive twin contraction

Three independent leaves need two outside vertices to separate their
neighborhoods. In a nearest-neighbour Pauli path, an anticommutation
edge changes the coefficient row by at most one. The center, leaves
and two witnesses therefore give six distinct terms in five rows.
-/

namespace GaloisForLFunctions.HTGeometry

private theorem three_not_iff_impossible {P Q R : Prop} (hPQ : ¬(P ↔ Q))
    (hPR : ¬(P ↔ R)) (hQR : ¬(Q ↔ R)) : False := by
  classical
  by_cases hp : P
  · have hq : ¬Q := fun h => hPQ (iff_of_true hp h)
    have hr : ¬R := fun h => hPR (iff_of_true hp h)
    exact hQR (iff_of_false hq hr)
  · have hq : Q := Classical.byContradiction fun h => hPQ (iff_of_false hp h)
    have hr : R := Classical.byContradiction fun h => hPR (iff_of_false hp h)
    exact hQR (iff_of_true hq hr)

/-- Distinct neighborhoods of the three leaves require two vertices
outside the claw, even when the directions of distinction are arbitrary. -/
theorem exists_two_claw_witnesses {ι : Type*} [DecidableEq ι]
    (adj : ι → ι → Prop) (symm : ∀ {x y}, adj x y → adj y x)
    (irrefl : ∀ x, ¬adj x x) (o a b c : ι)
    (hoa : adj o a) (hob : adj o b) (hoc : adj o c)
    (hab : ¬adj a b) (hac : ¬adj a c) (hbc : ¬adj b c)
    (wab : ∃ w, ¬(adj a w ↔ adj b w))
    (wac : ∃ w, ¬(adj a w ↔ adj c w))
    (wbc : ∃ w, ¬(adj b w ↔ adj c w)) :
    ∃ w x, w ≠ x ∧ w ∉ ({o, a, b, c} : Finset ι) ∧ x ∉ ({o, a, b, c} : Finset ι) ∧
      (adj a w ∨ adj b w ∨ adj c w) ∧ (adj a x ∨ adj b x ∨ adj c x) := by
  classical
  let L : Finset ι := {a, b, c}
  let C : Finset ι := insert o L
  have hleaves {p q : ι} (hp : p ∈ L) (hq : q ∈ L) : ¬adj p q := by
    simp only [L, Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
    · exact irrefl _
    · exact hab
    · exact hac
    · exact fun h => hab (symm h)
    · exact irrefl _
    · exact hbc
    · exact fun h => hac (symm h)
    · exact fun h => hbc (symm h)
    · exact irrefl _
  have hcenter {p : ι} (hp : p ∈ L) : adj p o := by
    simp only [L, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact symm hoa
    · exact symm hob
    · exact symm hoc
  have ha : a ∈ L := by simp [L]
  have hb : b ∈ L := by simp [L]
  have hc : c ∈ L := by simp [L]
  have witness {p q w : ι} (hp : p ∈ L) (hq : q ∈ L)
      (hw : ¬(adj p w ↔ adj q w)) : w ∉ C ∧ (adj a w ∨ adj b w ∨ adj c w) := by
    constructor
    · intro h
      rcases Finset.mem_insert.mp h with rfl | hm
      · exact hw (iff_of_true (hcenter hp) (hcenter hq))
      · exact hw (iff_of_false (hleaves hp hm) (hleaves hq hm))
    · have hpq : adj p w ∨ adj q w := by
        by_contra! h
        exact hw (iff_of_false h.1 h.2)
      have forward (v : ι) (hv : v ∈ L) (hadj : adj v w) : adj a w ∨ adj b w ∨ adj c w := by
        simp only [L, Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl
        · exact Or.inl hadj
        · exact Or.inr (Or.inl hadj)
        · exact Or.inr (Or.inr hadj)
      exact hpq.elim (forward p hp) (forward q hq)
  obtain ⟨u, hu⟩ := wab
  obtain ⟨v, hv⟩ := wac
  obtain ⟨w, hw⟩ := wbc
  have hu' := witness ha hb hu
  have hv' := witness ha hc hv
  have hw' := witness hb hc hw
  by_cases huv : u = v
  · by_cases huw : u = w
    · subst v
      subst w
      exact (three_not_iff_impossible hu hv hw).elim
    · exact ⟨u, w, huw, hu'.1, hw'.1, hu'.2, hw'.2⟩
  · exact ⟨u, v, huv, hu'.1, hv'.1, hu'.2, hv'.2⟩

variable {n : ℕ}

/-- The row of an onsite field or the left endpoint of a bond. -/
def pathPauliRow (l : PathLabel n) : ℕ := (pathPauliSourceCoordinate l).1

private theorem pathWord_support_rows (l : PathLabel n) (i : Fin (n + 2))
    (h : pathWord l i ≠ none) : pathPauliRow l ≤ i.val ∧ i.val ≤ pathPauliRow l + 1 := by
  rcases l with ⟨s, a⟩ | ⟨e, ab⟩
  · by_cases hi : i = s
    · subst i
      exact ⟨le_rfl, Nat.le_succ _⟩
    · exact (h (by simp [pathWord, onsiteWord, hi])).elim
  · by_cases hl : i = e.castSucc
    · subst i
      exact ⟨le_rfl, Nat.le_succ _⟩
    · by_cases hr : i = e.succ
      · subst i
        exact ⟨Nat.le_succ _, le_rfl⟩
      · exact (h (by simp [pathWord, couplingWord, hl, hr])).elim

/-- Two anticommuting terms have coefficient rows differing by at most one. -/
theorem pathFrustrationAdj_neighbor_rows (S : Set (PathLabel n)) (p q : S)
    (h : pathFrustrationAdj S p q) :
    pathPauliRow p.1 ≤ pathPauliRow q.1 + 1 ∧ pathPauliRow q.1 ≤ pathPauliRow p.1 + 1 := by
  by_contra hfar
  apply h
  rw [finitePauli_commute_iff_sign, finitePauliConjugationSign]
  apply Finset.prod_eq_one
  intro i _
  by_cases hp : pathWord p.1 i = none
  · simp [boolPauliConjugationSign, hp]
  · by_cases hq : pathWord q.1 i = none
    · simp [boolPauliConjugationSign, hq]
    · obtain ⟨hp₁, hp₂⟩ := pathWord_support_rows _ _ hp
      obtain ⟨hq₁, hq₂⟩ := pathWord_support_rows _ _ hq
      exact (hfar ⟨hp₁.trans hq₂, hq₁.trans hp₂⟩).elim

/-- Every induced path-Pauli claw with pairwise distinguishable leaves
uses six distinct retained terms within two rows of its center. -/
theorem exists_six_local_terms_of_distinguished_claw (S : Set (PathLabel n)) (o a b c : S)
    (hoa : pathFrustrationAdj S o a) (hob : pathFrustrationAdj S o b)
    (hoc : pathFrustrationAdj S o c)
    (hab : ¬pathFrustrationAdj S a b) (hac : ¬pathFrustrationAdj S a c)
    (hbc : ¬pathFrustrationAdj S b c)
    (wab : ∃ w, ¬(pathFrustrationAdj S a w ↔ pathFrustrationAdj S b w))
    (wac : ∃ w, ¬(pathFrustrationAdj S a w ↔ pathFrustrationAdj S c w))
    (wbc : ∃ w, ¬(pathFrustrationAdj S b w ↔ pathFrustrationAdj S c w)) :
    ∃ F : Finset (PathLabel n), F.card = 6 ∧ (∀ l ∈ F, l ∈ S) ∧
      ∀ l ∈ F, pathPauliRow l ≤ pathPauliRow o.1 + 2 ∧ pathPauliRow o.1 ≤ pathPauliRow l + 2 := by
  classical
  let adj := pathFrustrationAdj S
  have symm {p q : S} (h : adj p q) : adj q p := fun hc => h hc.symm
  have irrefl (p : S) : ¬adj p p := fun h => h (Commute.refl _)
  obtain ⟨u, v, huv, hu, hv, huAdj, hvAdj⟩ :=
    exists_two_claw_witnesses adj symm irrefl o a b c hoa hob hoc hab hac hbc wab wac wbc
  have oa : o ≠ a := fun h => irrefl a (h ▸ hoa)
  have ob : o ≠ b := fun h => irrefl b (h ▸ hob)
  have oc : o ≠ c := fun h => irrefl c (h ▸ hoc)
  have ab : a ≠ b := by
    intro h
    obtain ⟨w, hw⟩ := wab
    exact hw (by rw [h])
  have ac : a ≠ c := by
    intro h
    obtain ⟨w, hw⟩ := wac
    exact hw (by rw [h])
  have bc : b ≠ c := by
    intro h
    obtain ⟨w, hw⟩ := wbc
    exact hw (by rw [h])
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hu hv
  let V : Finset S := {u, v, o, a, b, c}
  have hcard : V.card = 6 := by
    simp [V, Finset.card_insert_of_notMem, huv, hu.1, hu.2.1, hu.2.2.1, hu.2.2.2,
      hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, oa, ob, oc, ab, ac, bc]
  let emb : S ↪ PathLabel n := ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨V.map emb, by simpa only [Finset.card_map] using hcard, ?_, ?_⟩
  · intro l hl
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hl
    exact x.2
  · intro l hl
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hl
    have near (q : S) (h : adj o q) :
        pathPauliRow q.1 ≤ pathPauliRow o.1 + 2 ∧ pathPauliRow o.1 ≤ pathPauliRow q.1 + 2 := by
      obtain ⟨h₁, h₂⟩ := pathFrustrationAdj_neighbor_rows S o q h
      omega
    have near_two (q r : S) (h : adj o q) (h' : adj q r) :
        pathPauliRow r.1 ≤ pathPauliRow o.1 + 2 ∧ pathPauliRow o.1 ≤ pathPauliRow r.1 + 2 := by
      obtain ⟨h₁, h₂⟩ := pathFrustrationAdj_neighbor_rows S o q h
      obtain ⟨h₃, h₄⟩ := pathFrustrationAdj_neighbor_rows S q r h'
      omega
    simp only [V, Finset.mem_insert, Finset.mem_singleton] at hx
    change pathPauliRow x.1 ≤ pathPauliRow o.1 + 2 ∧ pathPauliRow o.1 ≤ pathPauliRow x.1 + 2
    rcases hx with h | h | h | h | h | h <;> rw [h]
    · rcases huAdj with h | h | h
      · exact near_two a u hoa h
      · exact near_two b u hob h
      · exact near_two c u hoc h
    · rcases hvAdj with h | h | h
      · exact near_two a v hoa h
      · exact near_two b v hob h
      · exact near_two c v hoc h
    · omega
    · exact near a hoa
    · exact near b hob
    · exact near c hoc

#print axioms exists_two_claw_witnesses
#print axioms pathFrustrationAdj_neighbor_rows
#print axioms exists_six_local_terms_of_distinguished_claw

end GaloisForLFunctions.HTGeometry
