import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.SitePartition

/-! # Contiguous packets between arbitrary selected bonds -/

open Finset
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section
variable {n : ℕ}

private def before (C : Finset (Fin (n+1))) (v : Fin (n+2)) :=
  C.filter fun e => e.val<v.val

/-- Number consecutive packets by the number of cuts strictly to the left. -/
def intervalOf (C : Finset (Fin (n+1))) (v : Fin (n+2)) : Fin (C.card+1) :=
  ⟨(before C v).card,Nat.lt_succ_of_le (card_le_card (filter_subset ..))⟩

/-- Adjacent sites have different packet numbers exactly on the chosen bonds. -/
theorem interval_crosses (C : Finset (Fin (n+1))) (e : Fin (n+1)) :
    intervalOf C e.castSucc≠intervalOf C e.succ ↔ e∈C := by
  have hrow : before C e.succ=if e∈C then insert e (before C e.castSucc) else before C e.castSucc := by
    ext j
    by_cases hc : e∈C
    · simp only [if_pos hc,before,mem_filter,mem_insert,Fin.val_succ,Fin.val_castSucc,Fin.ext_iff]
      constructor
      · rintro ⟨hj,hl⟩
        by_cases h : j.val=e.val
        · exact Or.inl h
        · exact Or.inr ⟨hj,by omega⟩
      · rintro (h|⟨hj,hl⟩)
        · exact ⟨(Fin.ext h).symm ▸ hc,by omega⟩
        · exact ⟨hj,by omega⟩
    · simp only [if_neg hc,before,mem_filter,Fin.val_succ,Fin.val_castSucc]
      apply and_congr_right
      intro hj
      have h : j.val≠e.val := fun hh => hc (Fin.ext hh ▸ hj)
      omega
  have hn : e∉before C e.castSucc := by simp [before]
  simp only [ne_eq,Fin.ext_iff,intervalOf]
  by_cases hc : e∈C
  · simp [hrow,if_pos hc,card_insert_of_notMem hn,hc]
  · simp [hrow,if_neg hc,hc]

private theorem fewer_before (C : Finset (Fin (n+1))) {v w : Fin (n+2)} {e : Fin (n+1)}
    (he : e∈C) (hv : v.val≤e.val) (hw : e.val<w.val) :
    (intervalOf C v).val<(intervalOf C w).val := by
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨fun j hj => mem_filter.mpr ⟨(mem_filter.mp hj).1,by have h := (mem_filter.mp hj).2; omega⟩,?_⟩
  intro h
  have hh : e∈before C w := mem_filter.mpr ⟨he,hw⟩
  rw [←h] at hh
  exact hv.not_gt (mem_filter.mp hh).2

/-- A cut in every interval of L bonds bounds every packet by L sites.
The proof uses injectivity of residue modulo L within a single packet. -/
theorem interval_size (C : Finset (Fin (n+1))) {L : ℕ} (hL : 0<L)
    (hcover : ∀ v w : Fin (n+2), v.val+L≤w.val → ∃ e∈C, v.val≤e.val ∧ e.val<w.val)
    (i : Fin (C.card+1)) : (sites (intervalOf C) i).card≤L := by
  let f (v : Fin (n+2)) : Fin L := ⟨v.val%L,Nat.mod_lt _ hL⟩
  have hdist {v w : Fin (n+2)} (hv : intervalOf C v=i) (hw : intervalOf C w=i) : w.val<v.val+L := by
    by_contra! hh
    obtain ⟨e,he,h₁,h₂⟩ := hcover v w hh
    have h := fewer_before C he h₁ h₂
    rw [hv,hw] at h
    exact (lt_irrefl _) h
  have hinj : Set.InjOn f (↑(sites (intervalOf C) i)) := by
    intro v hv w hw he
    have h₁ := hdist (mem_filter.mp hv).2 (mem_filter.mp hw).2
    have h₂ := hdist (mem_filter.mp hw).2 (mem_filter.mp hv).2
    have hr := congrArg Fin.val he
    change v.val%L=w.val%L at hr
    apply Fin.ext
    have hq : v.val/L=w.val/L := by
      have hv' := Nat.mod_add_div v.val L
      have hw' := Nat.mod_add_div w.val L
      rcases lt_trichotomy (v.val/L) (w.val/L) with h|h|h
      · have hm := Nat.mul_le_mul_left L (Nat.succ_le_of_lt h)
        rw [Nat.mul_succ] at hm
        omega
      · exact h
      · have hm := Nat.mul_le_mul_left L (Nat.succ_le_of_lt h)
        rw [Nat.mul_succ] at hm
        omega
    rw [←Nat.mod_add_div v.val L,hr,hq,Nat.mod_add_div]
  simpa using card_le_card_of_injOn f (fun _ _ => mem_univ _) hinj

#print axioms interval_crosses
#print axioms interval_size
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
