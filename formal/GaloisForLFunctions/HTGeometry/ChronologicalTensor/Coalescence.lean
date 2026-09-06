import GaloisForLFunctions.HTGeometry.ChronologicalTensor.MonotoneMerge

/-!
# Pointwise monotone coalescence

Every absolute-gap probe for a genuine pairing family is dominated by a
nonnegative probe of the same variation with nonadjacent active gaps.
The proof repeatedly chooses a response-improving adjacent merge and
terminates by strict decrease of the finite support count.

The construction preserves all initially zero gaps, including a terminal
unused coordinate. At most d active gaps remain for 2*d endpoints.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

def separatedSupport {n : ℕ} (g : Fin n → ℝ) : Prop :=
  ∀ a : Fin (n-1), g (adjacentLower a)=0 ∨ g (adjacentUpper a)=0

def gapPairIndex {d : ℕ} (q : Fin (2*d)) : Fin d :=
  ⟨q.val/2,by have h := q.isLt; omega⟩

theorem adjacent_gap_pigeonhole {d : ℕ} (g : Fin (2*d) → ℝ) :
    activeGapCount g ≤ d ∨ ∃ a : Fin (2*d-1),
      g (adjacentLower a) ≠ 0 ∧ g (adjacentUpper a) ≠ 0 := by
  classical
  by_cases hs : separatedSupport g
  · left
    let S := Finset.univ.filter (fun q => g q ≠ 0)
    have hordered (a b : Fin (2*d)) (ha : g a ≠ 0) (hb : g b ≠ 0)
        (hab : a.val/2=b.val/2) (hlt : a < b) : False := by
      have hval : a.val < b.val := hlt
      let q : Fin (2*d-1) := ⟨a.val,by have h := b.isLt; omega⟩
      have hl : adjacentLower q=a := Fin.ext rfl
      have hu : adjacentUpper q=b := by
        apply Fin.ext
        change a.val+1=b.val
        omega
      rcases hs q with h | h
      · exact ha (by simpa only [hl] using h)
      · exact hb (by simpa only [hu] using h)
    have hinj : Set.InjOn gapPairIndex (S : Set (Fin (2*d))) := by
      intro a ha b hb hab
      have ha0 : g a ≠ 0 := (Finset.mem_filter.mp ha).2
      have hb0 : g b ≠ 0 := (Finset.mem_filter.mp hb).2
      have hval : a.val/2=b.val/2 := congrArg Fin.val hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact hordered a b ha0 hb0 hval hlt
      · exact hordered b a hb0 ha0 hval.symm hgt
    have hc := Finset.card_le_card_of_injOn (s := S) (t := Finset.univ) gapPairIndex
      (fun _ _ => Finset.mem_univ _) hinj
    simpa only [Finset.card_univ,Fintype.card_fin,activeGapCount,S] using hc
  · right
    unfold separatedSupport at hs
    push Not at hs
    exact hs

theorem enumeratedFamily_monotone_coalescence {d m : ℕ}
    (E : Fin m → ((Fin d ⊕ Fin d) ≃ Fin (2*d))) (c : Fin m → ℝ)
    (g : Fin (2*d) → ℝ) :
    ∃ h : Fin (2*d) → ℝ,
      (∀ q, 0 ≤ h q) ∧ variation h=variation g ∧
      (∀ q, g q=0 → h q=0) ∧
      |familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c) (fun q => |g q|)| ≤
        |familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c) h| ∧
      separatedSupport h ∧ activeGapCount h ≤ d := by
  classical
  let F := familyValue (enumeratedFamilyWindows E) (enumeratedFamilyCoefficients E c)
  have hex (k : ℕ) : ∀ p : Fin (2*d) → ℝ, (∀ q, 0 ≤ p q) → activeGapCount p=k →
      ∃ h : Fin (2*d) → ℝ, (∀ q, 0 ≤ h q) ∧ variation h=variation p ∧
        (∀ q, p q=0 → h q=0) ∧ |F p| ≤ |F h| ∧ separatedSupport h := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro p hp hcount
      by_cases hs : separatedSupport p
      · exact ⟨p,hp,rfl,fun _ h => h,le_rfl,hs⟩
      · have hnot := hs
        unfold separatedSupport at hnot
        push Not at hnot
        obtain ⟨a,hal,har⟩ := hnot
        have habs : (fun q => |p q|)=p := funext (fun q => abs_of_nonneg (hp q))
        obtain ⟨side,hdom⟩ := enumeratedFamily_merge_choice E c p a
        rw [habs] at hdom
        let h := mergeAdjacent p a side
        have hnn : ∀ q, 0 ≤ h q := by
          intro q
          have hh := mergeAdjacent_nonneg p a side q
          rw [habs] at hh
          exact hh
        have hcost : variation h=variation p := by
          have hh := mergeAdjacent_variation p a side
          rw [habs] at hh
          exact hh
        have hlt : activeGapCount h < k := by
          rcases mergeAdjacent_support_decreases p a side with hh | hh | hh
          · exact (hal hh).elim
          · exact (har hh).elim
          · exact hh.trans_eq hcount
        have hzeros : ∀ q, p q=0 → h q=0 := by
          intro q hq
          have hql : q ≠ adjacentLower a := by
            intro heq
            exact hal (heq ▸ hq)
          have hqr : q ≠ adjacentUpper a := by
            intro heq
            exact har (heq ▸ hq)
          change mergeAdjacent p a side q=0
          simp only [mergeAdjacent_apply,if_neg hql,if_neg hqr,hq]
        obtain ⟨h',h'nn,h'cost,h'zeros,h'dom,h'sep⟩ := ih (activeGapCount h) hlt h hnn rfl
        exact ⟨h',h'nn,h'cost.trans hcost,fun q hq => h'zeros q (hzeros q hq),hdom.trans h'dom,h'sep⟩
  obtain ⟨h,hnn,hcost,hzeros,hdom,hsep⟩ := hex (activeGapCount (fun q => |g q|))
    (fun q => |g q|) (fun q => abs_nonneg _) rfl
  refine ⟨h,hnn,?_,?_,hdom,hsep,?_⟩
  · simpa only [variation,abs_abs] using hcost
  · intro q hq
    exact hzeros q (by rw [hq,abs_zero])
  · rcases adjacent_gap_pigeonhole h with hh | ⟨a,hal,har⟩
    · exact hh
    · rcases hsep a with hh | hh
      · exact (hal hh).elim
      · exact (har hh).elim

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
