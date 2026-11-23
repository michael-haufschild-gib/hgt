import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.PathCuts
import Mathlib.Combinatorics.Pigeonhole

/-! # Separated path bonds with a common circuit-cut orientation -/
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

private theorem residue_spacing {L x y : ℕ} (h : x%L=y%L) (hxy : x<y) : x+L≤y := by
  have ex := Nat.mod_add_div x L
  have ey := Nat.mod_add_div y L
  have hq : x/L<y/L := by
    by_contra! hn
    have hp := Nat.mul_le_mul_left L hn
    omega
  have hp := Nat.mul_le_mul_left L (Nat.succ_le_of_lt hq)
  rw [Nat.mul_succ] at hp
  omega

/-- Coloring each crossed bond by its left color and position modulo L
extracts m bonds with identical orientation and spacing at least L.
The selected cut respects every gate, including gates on distant sites. -/
theorem oriented_subfamily {n L m : ℕ} (hL : 0<L) {C : TwoQubitCircuit (n+2)}
    (c : Cut C) (F : Finset (Fin (n+1))) (hF : F ⊆ crossed c) (hm : 2*L*m≤F.card) :
    ∃ S : Finset (Fin (n+2)), ∃ e : Fin m → Fin (n+1), Function.Injective e ∧
      (∀ i : Fin C.gateCount, (C.architecture.sites i).1∈S ↔ (C.architecture.sites i).2∈S) ∧
      (∀ i, e i∈F ∧ (e i).castSucc∈S ∧ (e i).succ∉S) ∧
      (∀ i j, (e i).val < (e j).val → (e i).val+L≤(e j).val) := by
  classical
  letI : NeZero L := ⟨hL.ne'⟩
  let key (e : Fin (n+1)) : Bool × Fin L := (c.val e.castSucc,⟨e.val%L,Nat.mod_lt _ hL⟩)
  let K := Finset.univ (α:=Bool × Fin L)
  have hc : K.card*m≤F.card := by
    simpa only [K,Finset.card_univ,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] using hm
  obtain ⟨k,_,hk⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (fun e (_ : e∈F) => Finset.mem_univ (key e)) Finset.univ_nonempty hc
  let T := F.filter fun e => key e=k
  have hT : m≤Fintype.card ↥T := by simpa only [Fintype.card_coe] using hk
  let pick (i : Fin m) : T := (Fintype.equivFin T).symm (Fin.castLE hT i)
  let e (i : Fin m) := (pick i).val
  let S := Finset.univ.filter fun j => c.val j=k.1
  have hey (i) : e i∈F ∧ key (e i)=k := Finset.mem_filter.mp (pick i).property
  refine ⟨S,e,?_,?_,?_,?_⟩
  · intro i j hij
    have h := (Fintype.equivFin T).symm.injective (Subtype.ext hij : pick i=pick j)
    exact Fin.ext (congrArg (fun k : Fin (Fintype.card T) => k.val) h)
  · intro i
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,c.gate_agrees i]
  · intro i
    have hleft := congrArg Prod.fst (hey i).2
    change c.val (e i).castSucc=k.1 at hleft
    have hcross := (mem_crossed_iff c (e i)).mp (hF (hey i).1)
    refine ⟨(hey i).1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hleft⟩,?_⟩
    exact fun h => hcross (hleft.trans (Finset.mem_filter.mp h).2.symm)
  · intro i j hij
    exact residue_spacing (congrArg (fun z : Bool × Fin L => z.2.val) ((hey i).2.trans (hey j).2.symm)) hij

#print axioms oriented_subfamily
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
