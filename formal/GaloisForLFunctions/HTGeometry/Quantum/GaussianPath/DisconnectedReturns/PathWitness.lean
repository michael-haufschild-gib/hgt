import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.DisconnectedReturns.IsingPropagation
import GaloisForLFunctions.HTGeometry.PathChainLabelIdentification

/-! # A single physical coupling vector detects every nonempty bond subset -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.DisconnectedReturns
noncomputable section

/-- The part of the path Hamiltonian carried on a selected set of bonds. -/
def bondPart {n : ℕ} (u : PathShell n) (s : Finset (Fin (n+1))) : Register (n+2) :=
  ∑ e∈s, edgePart u e

def witness (n : ℕ) : PathShell n :=
  WithLp.toLp 2 fun l => match l with
  | .inl (i,a) => if a=0 then weight i else if a=2 then weight (Sum.inl i : ZIndex n) else 0
  | .inr (e,p) => if p=(2,2) then weight (Sum.inr e : ZIndex n) else 0

private theorem edge_witness {n : ℕ} (e : Fin (n+1)) :
    edgePart (witness n) e=(weight (Sum.inr e : ZIndex n):ℂ) • longitudinal (.inr e) := by
  unfold edgePart
  rw [Finset.sum_eq_single (2,2)]
  · change ((if ((2,2):Fin 3×Fin 3)=(2,2) then _ else 0 : ℝ):ℂ) • _=_
    rw [if_pos rfl,couplingWord_zz]; rfl
  · intro p _ hp
    simp [witness,hp]
  · simp

private theorem hf_site {n : ℕ} (i : Fin (n+2)) :
    (∑ a : Fin 3, (witness n (.inl (i,a)):ℂ) • finitePauliMatrix (onsiteWord i a)) =
      (weight i:ℂ) • transverse i + (weight (Sum.inl i : ZIndex n):ℂ) • longitudinal (.inl i) := by
  rw [Fin.sum_univ_three]
  simp only [witness,WithLp.ofLp_toLp,if_neg (by decide : (1:Fin 3)≠0),
    if_neg (by decide : (1:Fin 3)≠2),if_neg (by decide : (2:Fin 3)≠0),
    Complex.ofReal_zero,zero_smul,add_zero,onsiteWord_two]
  rfl

theorem witness_hamiltonian (n : ℕ) : pathHamiltonian (witness n)=tilted n := by
  rw [pathHamiltonian,onsitePart,Fintype.sum_prod_type]
  simp_rw [hf_site,edge_witness]
  simp only [tilted,weighted,Fintype.sum_sum_type,Finset.sum_add_distrib,add_assoc]

/-- The same physical Hamiltonian works even if the selected bonds split
the register into many alternating intervals. -/
theorem witness_joint_scalar {n : ℕ} (s : Finset (Fin (n+1))) (hs : s.Nonempty)
    (r : Fin (n+2)→Bool) (X : Register (n+2))
    (hH : Commute X (pathHamiltonian (witness n))) (hB : Commute X (bondPart (witness n) s)) :
    X=X r r • (1 : Register (n+2)) := by
  classical
  let T := s.map (Function.Embedding.inr : Fin (n+1) ↪ ZIndex n)
  have hT : weighted longitudinal T=bondPart (witness n) s := by
    simp only [weighted,T,Finset.sum_map,bondPart,edge_witness]; rfl
  obtain ⟨e,he⟩ := hs
  apply tilted_bond_scalar X T e (Finset.mem_map.mpr ⟨_,he,rfl⟩) r
  · rwa [←witness_hamiltonian]
  · rwa [hT]

#print axioms witness_joint_scalar
end
end GaloisForLFunctions.HTGeometry.DisconnectedReturns
