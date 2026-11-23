import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PauliThresholdObstruction
import GaloisForLFunctions.HTGeometry.PathHamiltonianSiteRestriction

/-! # Contiguous blocks of a physical Pauli path and the omitted bonds -/
open Finset Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk.PeriodicCuts
noncomputable section
variable {n : ℕ}

private def first : PathLabel n → Fin (n+2)
  | .inl (v,_) => v
  | .inr (e,_) => e.castSucc

private def last : PathLabel n → Fin (n+2)
  | .inl (v,_) => v
  | .inr (e,_) => e.succ

private def group (L : ℕ) (v : Fin (n+2)) : Fin (n+2) :=
  ⟨v.val/L,(Nat.div_le_self ..).trans_lt v.isLt⟩

/-- The block containing the full Pauli word, or none for a crossing bond. -/
def owner (L : ℕ) (l : PathLabel n) : Option (Fin (n+2)) :=
  if group L (first l)=group L (last l) then some (group L (first l)) else none

def sites (L : ℕ) (b : Fin (n+2)) := univ.filter (fun v => group L v=b)

def labels (L : ℕ) (b : Option (Fin (n+2))) := univ.filter (fun l : PathLabel n => owner L l=b)

/-- Retain the coefficients assigned to one block. -/
def piece (L : ℕ) (u : PathShell n) (b : Fin (n+2)) : PathShell n :=
  WithLp.toLp 2 fun l => if owner L l=some b then u l else 0

theorem disjoint_sites (L : ℕ) (b c : Fin (n+2)) (h : b≠c) : Disjoint (sites L b) (sites L c) :=
  Finset.disjoint_left.mpr fun _ hb hc => h ((mem_filter.mp hb).2.symm.trans (mem_filter.mp hc).2)

private theorem endpoints {L : ℕ} {l : PathLabel n} {b : Fin (n+2)} (h : owner L l=some b) :
    group L (first l)=b ∧ group L (last l)=b := by
  unfold owner at h
  split at h
  next he => exact ⟨Option.some.inj h,he.symm.trans (Option.some.inj h)⟩
  next => contradiction

theorem piece_supported (L : ℕ) (u : PathShell n) (b : Fin (n+2)) :
    IsSiteSupported (sites L b) (pathHamiltonian (piece L u b)) := by
  rw [pathHamiltonian_eq_sum]
  apply sum_induction _ (IsSiteSupported (sites L b)) (fun _ _ => IsSiteSupported.add)
    (IsSiteSupported.zero _)
  intro l _
  by_cases ho : owner L l=some b
  · apply IsSiteSupported.complex_smul
    apply finitePauliMatrix_isSiteSupported_of_eq_none
    intro v hv
    have h := endpoints ho
    have h₁ : v≠first l := fun he => hv (mem_filter.mpr ⟨mem_univ _,he ▸ h.1⟩)
    have h₂ : v≠last l := fun he => hv (mem_filter.mpr ⟨mem_univ _,he ▸ h.2⟩)
    rcases l with ⟨v',a⟩ | ⟨e,ab⟩
    · simp only [pathWord,onsiteWord,if_neg (show v≠v' from h₁)]
    · simp only [pathWord,couplingWord,if_neg (show v≠e.castSucc from h₁),if_neg (show v≠e.succ from h₂)]
  · have he : piece L u b l=0 := if_neg ho
    rw [he,Complex.ofReal_zero,zero_smul]
    exact IsSiteSupported.zero _

private theorem row_injective {l k : PathLabel n} (hr : (first l).val=(first k).val)
    (ha : (pathPauliSourceCoordinate l).2=(pathPauliSourceCoordinate k).2) : l=k := by
  rcases l with ⟨i,a⟩|⟨e,p⟩ <;> rcases k with ⟨j,b⟩|⟨f,q⟩
  · exact congrArg Sum.inl (Prod.ext (Fin.ext hr) (Sum.inl.inj ha))
  · contradiction
  · contradiction
  · exact congrArg Sum.inr (Prod.ext (Fin.ext hr) (Sum.inr.inj ha))

/-- At most twelve Pauli coefficients per row occur in one block. -/
theorem block_card {L : ℕ} (hL : 0<L) (b : Fin (n+2)) : (labels L (some b)).card ≤ 12*L := by
  let f (l : PathLabel n) : Fin L × PathPauliDirections :=
    (⟨(first l).val%L,Nat.mod_lt _ hL⟩,(pathPauliSourceCoordinate l).2)
  have he : Set.InjOn f (↑(labels L (some b))) := by
    intro l hl k hk h
    have h₁ := (endpoints (mem_filter.mp hl).2).1
    have h₂ := (endpoints (mem_filter.mp hk).2).1
    have hq := congrArg Fin.val (h₁.trans h₂.symm)
    change (first l).val/L=(first k).val/L at hq
    have hm := congrArg (fun x : Fin L × PathPauliDirections => x.1.val) h
    change (first l).val%L=(first k).val%L at hm
    refine row_injective (l:=l) (k:=k) ?_ (congrArg (fun x => (x : Fin L × PathPauliDirections).2) h)
    rw [←Nat.mod_add_div (first l).val L,hm,hq,Nat.mod_add_div]
  have hh := card_le_card_of_injOn f (fun _ _ => mem_univ _) he
  simpa only [card_univ,PathPauliDirections,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,
    show 3+3*3=12 from rfl,Nat.mul_comm L 12] using hh

private theorem crosses_after {L : ℕ} {l : PathLabel n} (h : owner L l=none) :
    (first l).val/L<((first l).val+1)/L := by
  have hn : group L (first l)≠group L (last l) := by
    intro he
    rw [owner,if_pos he] at h
    contradiction
  rcases l with ⟨i,a⟩|⟨e,p⟩
  · exact (hn rfl).elim
  · exact lt_of_le_of_ne (Nat.div_le_div_right (Nat.le_succ _)) (fun he => hn (Fin.ext he))

/-- Crossing bonds have distinct left block indices. At most twelve
labels per left block are needed even after retaining all spin axes. -/
theorem seam_card (L : ℕ) : (labels (n:=n) L none).card ≤ 12*((n+2)/L+1) := by
  let f (l : PathLabel n) : Fin ((n+2)/L+1) × PathPauliDirections :=
    (⟨(first l).val/L,Nat.lt_succ_of_le (Nat.div_le_div_right (first l).isLt.le)⟩,
      (pathPauliSourceCoordinate l).2)
  have he : Set.InjOn f (↑(labels (n:=n) L none)) := by
    intro l hl k hk h
    have hq := congrArg (fun x : Fin ((n+2)/L+1) × PathPauliDirections => x.1.val) h
    change (first l).val/L=(first k).val/L at hq
    refine row_injective (l:=l) (k:=k) ?_ (congrArg (fun x => (x : Fin ((n+2)/L+1) × PathPauliDirections).2) h)
    apply le_antisymm
    · apply le_of_not_gt
      intro hh
      exact (crosses_after (mem_filter.mp hk).2).not_ge
        ((Nat.div_le_div_right (Nat.succ_le_of_lt hh)).trans_eq hq)
    · apply le_of_not_gt
      intro hh
      exact (crosses_after (mem_filter.mp hl).2).not_ge
        ((Nat.div_le_div_right (Nat.succ_le_of_lt hh)).trans_eq hq.symm)
  have hh := card_le_card_of_injOn f (fun _ _ => mem_univ _) he
  simpa only [card_univ,PathPauliDirections,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,
    show 3+3*3=12 from rfl,Nat.mul_comm ((n+2)/L+1) 12] using hh

#print axioms block_card
#print axioms seam_card
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk.PeriodicCuts
