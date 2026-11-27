import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.IntervalLabels

/-! # Independent physical coordinates of two blocks and their joining bond -/
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
open FirstAscent.ThermodynamicEdges
noncomputable section

/-- Embed the left block at zero and the right block after its last wire.
The remaining nine labels are precisely the Pauli terms on the joining bond. -/
def joinLabel (l r : ℕ) : PathLabel l ⊕ (PathLabel r ⊕ (Fin 3×Fin 3)) → PathLabel (l+r+2)
  | .inl i => translateLabel (B:=0) (by omega) i
  | .inr (.inl i) => translateLabel (B:=l+2) (by omega) i
  | .inr (.inr p) => .inr (⟨l+1,by omega⟩,p)

private def start {n : ℕ} : PathLabel n→ℕ
  | .inl (i,_) => i.val
  | .inr (i,_) => i.val

private theorem joinLabel_injective (l r : ℕ) : Function.Injective (joinLabel l r) := by
  let f := joinLabel l r
  have hleft (x : PathLabel l) : lastRow (f (.inl x)) < l+2 := by
    rcases x with ⟨s,a⟩|⟨s,p⟩ <;> have := s.isLt <;>
      simp only [f,joinLabel,translateLabel,numberWires,Equiv.coe_fn_mk,lastRow,Nat.zero_add] <;> omega
  have hright (x : PathLabel r) : l+2 ≤ start (f (.inr (.inl x))) := by
    rcases x with ⟨s,a⟩|⟨s,p⟩ <;> change l+2 ≤ l+2+s.val <;> omega
  have hlast (x : PathLabel (l+r+2)) : start x≤lastRow x := by
    rcases x with ⟨s,a⟩|⟨s,p⟩ <;> simp [start,lastRow]
  have hlr (a b) : f (.inl a) ≠ f (.inr (.inl b)) := by
    intro e
    have hh := hleft a
    rw [e] at hh
    exact hh.not_ge ((hright b).trans (hlast _))
  have hls (a b) : f (.inl a) ≠ f (.inr (.inr b)) := by
    intro e
    have hh := hleft a
    rw [e] at hh
    exact (Nat.lt_irrefl (l+2)) hh
  have hrs (a b) : f (.inr (.inl a)) ≠ f (.inr (.inr b)) := by
    intro e
    have hh := hright a
    rw [e] at hh
    change l+2 ≤ l+1 at hh
    omega
  rintro (a|(a|a)) (b|(b|b)) he
  · exact congrArg Sum.inl (translateLabel_injective (B:=0) _ he)
  · exact False.elim (hlr _ _ he)
  · exact False.elim (hls _ _ he)
  · exact False.elim (hlr _ _ he.symm)
  · exact congrArg (fun x => Sum.inr (Sum.inl x)) (translateLabel_injective (B:=l+2) _ he)
  · exact False.elim (hrs _ _ he)
  · exact False.elim (hls _ _ he.symm)
  · exact False.elim (hrs _ _ he.symm)
  · exact congrArg (fun x => Sum.inr (Sum.inr x)) (congrArg Prod.snd (Sum.inr.inj he))

def joinEquiv (l r : ℕ) : PathLabel l ⊕ (PathLabel r ⊕ (Fin 3×Fin 3)) ≃ PathLabel (l+r+2) :=
  Equiv.ofBijective (joinLabel l r) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨joinLabel_injective l r,by
      simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
      omega⟩)

#print axioms joinEquiv
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
