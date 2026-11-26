import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PhysicalPatterns
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PacketMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.BlockApproximation.PeriodicCuts

/-! # Spatial packets and the common boundary of all their dilations -/

open Finset
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section
variable {n : ℕ}

private abbrev Block (n L : ℕ) := Fin ((n+1)/L+1)

private def blockOf (L : ℕ) (v : Fin (n+2)) : Block n L :=
  ⟨v.val/L,Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))⟩

/-- Contiguous packets, including the possibly shorter last packet. -/
def periodicPacket (L : ℕ) (b : Block n L) : Finset (Fin (n+2)) :=
  univ.filter fun v => blockOf L v=b

theorem periodic_disjoint (L : ℕ) :
    Pairwise fun b c : Block n L => Disjoint (periodicPacket L b) (periodicPacket L c) := by
  intro b c hbc
  exact disjoint_left.mpr fun _ hb hc => hbc ((mem_filter.mp hb).2.symm.trans (mem_filter.mp hc).2)

theorem periodic_card {L : ℕ} (hL : 0<L) (b : Block n L) : (periodicPacket L b).card≤L := by
  let f (v : Fin (n+2)) : Fin L := ⟨v.val%L,Nat.mod_lt _ hL⟩
  have hi : Set.InjOn f (↑(periodicPacket L b)) := by
    intro v hv w hw h
    have hq := congrArg Fin.val ((mem_filter.mp hv).2.trans (mem_filter.mp hw).2.symm)
    change v.val/L=w.val/L at hq
    have hr := congrArg Fin.val h
    change v.val%L=w.val%L at hr
    apply Fin.ext
    rw [←Nat.mod_add_div v.val L,hr,hq,Nat.mod_add_div]
  simpa using card_le_card_of_injOn f (fun _ _ => mem_univ _) hi

theorem periodic_longitudinal (L : ℕ) (u : PathShell n) :
    (∑ b : Block n L, longitudinal (periodicPacket L b) u)=
      ∑ v : Fin (n+2), |u (.inl (v,2))| := by
  simp only [longitudinal,periodicPacket,sum_filter]
  rw [sum_comm]
  simp

private theorem belongs_of_uncut (L : ℕ) (q : PathLabel n)
    (hq : SpectralGapMass.Bulk.PeriodicCuts.owner L q≠none) :
    ∃ b, PathWordSupportedIn (periodicPacket L b) q := by
  rcases q with ⟨v,a⟩ | ⟨e,ab⟩
  · refine ⟨blockOf L v,fun w hw => ?_⟩
    exact if_neg (fun he => hw (mem_filter.mpr ⟨mem_univ _,congrArg (blockOf L) he⟩))
  · have he : blockOf L e.castSucc=blockOf L e.succ := by
      apply Fin.ext
      unfold SpectralGapMass.Bulk.PeriodicCuts.owner at hq
      split at hq
      next h => exact congrArg (fun v : Fin (n+2) => v.val) h
      next _ => exact (hq rfl).elim
    refine ⟨blockOf L e.castSucc,fun w hw => ?_⟩
    have h₁ : w≠e.castSucc := fun h => hw (mem_filter.mpr ⟨mem_univ _,congrArg (blockOf L) h⟩)
    have h₂ : w≠e.succ := fun h => hw (mem_filter.mpr ⟨mem_univ _,(congrArg (blockOf L) h).trans he.symm⟩)
    simp only [pathWord,couplingWord,if_neg h₁,if_neg h₂]

/-- An unchanged word meeting a changed word necessarily crosses a seam.
Changing an arbitrary union of internal packets has the same boundary envelope. -/
theorem outside_word_crosses (L : ℕ) (x : Block n L→Bool) {q l : PathLabel n}
    (hq : q∉selectedLabels (periodicPacket L) x)
    (hl : l∈selectedLabels (periodicPacket L) x) (hi : l∈pathOverlaps q) :
    q∈SpectralGapMass.Bulk.PeriodicCuts.labels L none := by
  classical
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  by_contra hn
  obtain ⟨b,hb⟩ := belongs_of_uncut L q hn
  simp only [selectedLabels,mem_filter,mem_univ,true_and] at hl hq
  obtain ⟨i,hx,hs⟩ := hl
  have hbi : b=i := by
    by_contra hne
    obtain ⟨v,hv,hw⟩ := not_disjoint_iff.mp (mem_pathOverlaps.mp hi)
    have h₁ : v∈periodicPacket L b := Classical.byContradiction fun h => (mem_labelSupport.mp hv) (hb v h)
    have h₂ : v∈periodicPacket L i := Classical.byContradiction fun h => (mem_labelSupport.mp hw) (hs v h)
    exact disjoint_left.mp (periodic_disjoint L hne) h₁ h₂
  exact hq ⟨i,hx,hbi ▸ hb⟩

#print axioms periodic_card
#print axioms periodic_longitudinal
#print axioms outside_word_crosses
end
end GaloisForLFunctions.HTGeometry.BlockDilations
