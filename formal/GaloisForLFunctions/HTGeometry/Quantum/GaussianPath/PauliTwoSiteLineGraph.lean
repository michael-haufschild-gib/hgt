import Mathlib.Data.Finset.Sum
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PauliLineObstruction

/-!
# The two-site Pauli line graph

The six root vertices are the three axes at each of two sites. An onsite
axis maps to the complementary pair on its site and a bond maps to its
two endpoint axes. This identifies the full two-site frustration graph
with the line graph of K₆ and gives a line graph for any active subset.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

private def otherAxes (a : Fin 3) : Finset (Fin 3) :=
  Finset.univ.erase a

private theorem card_otherAxes (a : Fin 3) : (otherAxes a).card = 2 := by
  simp [otherAxes]

private theorem otherAxes_injective : Function.Injective otherAxes :=
  fun a _ h => (Finset.erase_inj Finset.univ (Finset.mem_univ a)).mp h

private theorem otherAxes_intersect (a b : Fin 3) : ¬Disjoint (otherAxes a) (otherAxes b) := by
  intro h
  have hc := Finset.card_le_univ (s := otherAxes a ∪ otherAxes b)
  rw [Finset.card_union_of_disjoint h, card_otherAxes, card_otherAxes, Fintype.card_fin] at hc
  omega

private theorem disjoint_disjSum_iff {α β : Type*} (A C : Finset α) (B D : Finset β) :
    Disjoint (A.disjSum B) (C.disjSum D) ↔ Disjoint A C ∧ Disjoint B D := by
  simp only [Finset.disjoint_left]
  constructor
  · intro h
    exact ⟨fun a ha hc => h (Finset.inl_mem_disjSum.mpr ha) (Finset.inl_mem_disjSum.mpr hc),
      fun b hb hd => h (Finset.inr_mem_disjSum.mpr hb) (Finset.inr_mem_disjSum.mpr hd)⟩
  · rintro ⟨h₁, h₂⟩ (a | b)
    · simpa only [Finset.inl_mem_disjSum] using @h₁ a
    · simpa only [Finset.inr_mem_disjSum] using @h₂ b

/-- The root-vertex pair of a two-site Pauli term. -/
def twoSitePauliRootEdge : PathLabel 0 → Finset (Fin 3 ⊕ Fin 3)
  | .inl (i, a) => if i = 0 then (otherAxes a).disjSum ∅ else Finset.disjSum ∅ (otherAxes a)
  | .inr (_, a, b) => ({a} : Finset (Fin 3)).disjSum {b}

theorem card_twoSitePauliRootEdge (p : PathLabel 0) : (twoSitePauliRootEdge p).card = 2 := by
  rcases p with ⟨i, a⟩ | ⟨e, a, b⟩
  · by_cases h : i = 0 <;>
      simp only [twoSitePauliRootEdge, h, if_true, if_false, Finset.card_disjSum,
        card_otherAxes, Finset.card_empty]
  · simp only [twoSitePauliRootEdge, Finset.card_disjSum, Finset.card_singleton]

theorem twoSitePauliRootEdge_injective : Function.Injective twoSitePauliRootEdge := by
  have empty_ne (a : Fin 3) : ∅ ≠ otherAxes a := by
    intro h
    have hcard := congrArg Finset.card h
    rw [Finset.card_empty, card_otherAxes] at hcard
    exact Nat.zero_ne_add_one _ hcard
  have single_ne (a b : Fin 3) : ({a} : Finset (Fin 3)) ≠ otherAxes b := by
    intro h
    have hcard := congrArg Finset.card h
    rw [Finset.card_singleton, card_otherAxes] at hcard
    exact Nat.ne_of_lt (Nat.lt_succ_self _) hcard
  intro p q he
  rcases p with ⟨i, a⟩ | ⟨e, a, b⟩ <;> rcases q with ⟨j, c⟩ | ⟨f, c, d⟩
  · by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
      simp only [twoSitePauliRootEdge, hi, hj, if_true, if_false, Finset.disjSum_inj] at he
    · rw [hi, hj, otherAxes_injective he.1]
    · exact (empty_ne c he.2).elim
    · exact (empty_ne c he.1).elim
    · have hij : i = j := (Fin.eq_one_of_ne_zero i hi).trans (Fin.eq_one_of_ne_zero j hj).symm
      rw [hij, otherAxes_injective he.2]
  · by_cases hi : i = 0 <;>
      simp only [twoSitePauliRootEdge, hi, if_true, if_false, Finset.disjSum_inj] at he
    · exact (single_ne c a he.1.symm).elim
    · exact (single_ne d a he.2.symm).elim
  · by_cases hj : j = 0 <;>
      simp only [twoSitePauliRootEdge, hj, if_true, if_false, Finset.disjSum_inj] at he
    · exact (single_ne a c he.1).elim
    · exact (single_ne b c he.2).elim
  · simp only [twoSitePauliRootEdge, Finset.disjSum_inj, Finset.singleton_inj] at he
    rw [(Fin.eq_zero e).trans (Fin.eq_zero f).symm, he.1, he.2]

/-- Every edge among the six roots comes from a two-site Pauli label. -/
theorem exists_twoSitePauliRootEdge {E : Finset (Fin 3 ⊕ Fin 3)} (hE : E.card = 2) :
    ∃ p, twoSitePauliRootEdge p = E := by
  have hsplit : E.toLeft.disjSum E.toRight = E := Finset.toLeft_disjSum_toRight
  have hcards : E.toLeft.card + E.toRight.card = 2 := by
    rw [← Finset.card_disjSum, hsplit, hE]
  have hcomplement (S : Finset (Fin 3)) (hS : S.card = 2) : ∃ a, otherAxes a = S := by
    have hcard : (Finset.univ \ S).card = 1 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin, hS]
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    refine ⟨a, Finset.ext fun x => ?_⟩
    have hx : x ∉ S ↔ x = a := by
      simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton]
        using (Finset.ext_iff.mp ha x)
    simpa only [otherAxes, Finset.mem_erase, Finset.mem_univ, and_true, not_not] using
      (not_congr hx).symm
  have hcases :
      (E.toLeft.card = 2 ∧ E.toRight.card = 0) ∨
      (E.toLeft.card = 0 ∧ E.toRight.card = 2) ∨
      (E.toLeft.card = 1 ∧ E.toRight.card = 1) := by omega
  rcases hcases with ⟨hL, hR⟩ | ⟨hL, hR⟩ | ⟨hL, hR⟩
  · obtain ⟨a, ha⟩ := hcomplement _ hL
    refine ⟨.inl (0, a), ?_⟩
    simpa only [twoSitePauliRootEdge, if_true, ha, Finset.card_eq_zero.mp hR] using hsplit
  · obtain ⟨a, ha⟩ := hcomplement _ hR
    refine ⟨.inl (1, a), ?_⟩
    simpa only [twoSitePauliRootEdge, if_neg (Fin.zero_ne_one.symm), ha,
      Finset.card_eq_zero.mp hL] using hsplit
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hL
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hR
    exact ⟨.inr (0, a, b), by simpa only [twoSitePauliRootEdge, ha, hb] using hsplit⟩

private theorem twoSite_onsite_bond_adj (i : Fin 2) (a b c : Fin 3) (e : Fin 1) :
    (¬Commute (finitePauliMatrix (pathWord (.inl (i, a) : PathLabel 0)))
      (finitePauliMatrix (pathWord (.inr (e, b, c))))) ↔
      ¬Disjoint (twoSitePauliRootEdge (.inl (i, a))) (twoSitePauliRootEdge (.inr (e, b, c))) := by
  have he : e = 0 := Fin.eq_zero e
  subst e
  have hl : (0 : Fin 1).castSucc = 0 := rfl
  have hr : (0 : Fin 1).succ = 1 := rfl
  rcases eq_or_ne i 0 with rfl | hi
  · simp only [pathWord, commute_onsite_coupling_iff, hl, hr, twoSitePauliRootEdge,
      if_true, disjoint_disjSum_iff]
    simp [otherAxes, eq_comm]
  · have hi' := Fin.eq_one_of_ne_zero i hi
    subst i
    simp only [pathWord, commute_onsite_coupling_iff, hl, hr, twoSitePauliRootEdge,
      if_neg (Fin.zero_ne_one.symm : (1 : Fin 2) ≠ 0), disjoint_disjSum_iff]
    simp [otherAxes, eq_comm]

/-- Distinct terms anticommute precisely when their root edges meet. -/
theorem twoSitePauliRootEdge_adj_iff (p q : PathLabel 0) (hpq : p ≠ q) :
    (¬Commute (finitePauliMatrix (pathWord p)) (finitePauliMatrix (pathWord q))) ↔
      ¬Disjoint (twoSitePauliRootEdge p) (twoSitePauliRootEdge q) := by
  rcases p with ⟨i, a⟩ | ⟨e, a, b⟩ <;> rcases q with ⟨j, c⟩ | ⟨f, c, d⟩
  · change (¬Commute (finitePauliMatrix (onsiteWord i a))
      (finitePauliMatrix (onsiteWord j c))) ↔ _
    rw [commute_onsitePauli_iff]
    by_cases hij : i = j
    · subst j
      have hac : a ≠ c := fun h => hpq (by rw [h])
      by_cases hi : i = 0 <;>
        simp only [twoSitePauliRootEdge, hi, if_true, if_false, disjoint_disjSum_iff] <;>
        simp [hac, otherAxes_intersect]
    · have hs : i = 0 ∨ j = 0 := by
        by_contra h
        push Not at h
        exact hij ((Fin.eq_one_of_ne_zero i h.1).trans (Fin.eq_one_of_ne_zero j h.2).symm)
      rcases hs with rfl | rfl
      · have hj : j ≠ 0 := Ne.symm hij
        simp only [twoSitePauliRootEdge, if_true, if_neg hj, disjoint_disjSum_iff]
        simp [hij]
      · simp only [twoSitePauliRootEdge, if_true, if_neg hij, disjoint_disjSum_iff]
        simp [hij]
  · exact twoSite_onsite_bond_adj i a c d f
  · exact (not_congr ⟨Commute.symm, Commute.symm⟩).trans
      ((twoSite_onsite_bond_adj j c a b e).trans (not_congr disjoint_comm))
  · have he : e = 0 := Fin.eq_zero e
    have hf : f = 0 := Fin.eq_zero f
    subst e
    subst f
    have hl : (0 : Fin 1).castSucc = 0 := rfl
    have hr : (0 : Fin 1).succ = 1 := rfl
    simp only [twoSitePauliRootEdge, disjoint_disjSum_iff, Finset.disjoint_singleton]
    rw [finitePauli_commute_iff_sign]
    change (¬finitePauliConjugationSign (couplingWord (0 : Fin 1) (a, b))
      (couplingWord (0 : Fin 1) (c, d)) = 1) ↔ _
    rw [finitePauliConjugationSign, Fin.prod_univ_two]
    have hneg := neg_ne_self.mpr (one_ne_zero : (1 : ℂ) ≠ 0)
    by_cases hac : a = c <;> by_cases hbd : b = d
    · exact (hpq (by rw [hac, hbd])).elim
    · simp [couplingWord, hl, hr, boolPauliConjugationSign, hac, hbd, hneg]
    · simp [couplingWord, hl, hr, boolPauliConjugationSign, hac, hbd, hneg]
    · simp [couplingWord, hl, hr, boolPauliConjugationSign, hac, hbd]

/-- Any active support on the two-site path admits a line graph without
identifying distinct vertices. -/
def path_twoSite_twinLineModel (u : PathShell 0) :
    TwinLineModel (fun p q : ActivePathLabels u =>
      ¬Commute (finitePauliMatrix (pathWord p.1)) (finitePauliMatrix (pathWord q.1)))
      (Fin 3 ⊕ Fin 3) where
  rootEdge p := twoSitePauliRootEdge p.1
  card_rootEdge p := card_twoSitePauliRootEdge p.1
  adj_iff p q hpq := twoSitePauliRootEdge_adj_iff _ _ (fun h => hpq (congrArg _ h))
  twin p q hpq _ _ _ := by
    have he : p = q := Subtype.ext (twoSitePauliRootEdge_injective hpq)
    rw [he]

/-- On the common Gaussian draw the six-root model exists exactly for the
two-site prefix. The larger prefixes fail even with arbitrary root sets. -/
theorem gaussian_path_ae_twinLineModel_iff_twoSite :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n,
      Nonempty (TwinLineModel (fun p q : ActivePathLabels (pathPauliDisorderShell ω n) =>
        ¬Commute (finitePauliMatrix (pathWord p.1)) (finitePauliMatrix (pathWord q.1)))
        (Fin 3 ⊕ Fin 3)) ↔ n = 0 := by
  filter_upwards [gaussian_path_ae_no_twinLineModel (ρ := Fin 3 ⊕ Fin 3)] with ω hω
  intro n
  cases n with
  | zero => exact ⟨fun _ => rfl, fun _ => ⟨path_twoSite_twinLineModel _⟩⟩
  | succ n =>
    exact ⟨fun ⟨M⟩ => ((hω n).false M).elim, fun h => (Nat.succ_ne_zero _ h).elim⟩

#print axioms exists_twoSitePauliRootEdge
#print axioms twoSitePauliRootEdge_adj_iff
#print axioms gaussian_path_ae_twinLineModel_iff_twoSite

end GaloisForLFunctions.HTGeometry
