import GaloisForLFunctions.HTGeometry.ChainPauliFinFamily
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.LastSpinBlocks

/-! # Numbered physical Pauli coordinates of the directed chain -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

private theorem terminal_support (n : ℕ) (q : Fin 3) :
    IsSiteLabel (Fin.last n) (Fin.snoc (pauliIdentityLabel n) (some q)) := by
  intro i hi
  rcases snoc_some_support _ q hi with h|⟨j,_,hj⟩
  · exact h
  · exact (hj rfl).elim

/-- The newest onsite Pauli. -/
def terminalLabel (n : ℕ) (q : Fin 3) : ChainLabel (n+1) :=
  ⟨Fin.snoc (pauliIdentityLabel n) (some q),isChainLabel_of_isSiteLabel (terminal_support n q),
    snoc_some_ne_identity _ q⟩

/-- Acting trivially on the appended spin retains an old physical coordinate. -/
def liftedLabel {n : ℕ} (p : ChainLabel n) : ChainLabel (n+1) :=
  ⟨Fin.snoc p.1 none,by
    intro i j hi hj
    obtain ⟨i,rfl,hi'⟩ := snoc_none_support p.1 hi
    obtain ⟨j,rfl,hj'⟩ := snoc_none_support p.1 hj
    exact p.2.1 i j hi' hj',snoc_ne_identity_of_ne p.2.2 none⟩

/-- X on the old endpoint and Z on the appended spin. -/
def lastBondLabel (n : ℕ) : ChainLabel (n+2) := by
  let p := (terminalLabel n 0).1
  refine ⟨Fin.snoc p (some 2),?_,snoc_some_ne_identity _ _⟩
  have hs (i : Fin (n+2)) (hi : (Fin.snoc p (some 2) : Fin (n+2)→Option (Fin 3)) i≠none) :
      i.val=n ∨ i.val=n+1 := by
    rcases snoc_some_support _ 2 hi with h|⟨j,rfl,hj⟩
    · right; rw [h]; rfl
    · left; rw [terminal_support n 0 j hj]; rfl
  intro i j hi hj
  rcases hs i hi with h|h <;> rcases hs j hj with h'|h' <;> omega

def edgeLabel : (n : ℕ) → Fin n → ChainLabel (n+1)
  | 0,i => Fin.elim0 i
  | n+1,i => Fin.lastCases (lastBondLabel n) (fun j => liftedLabel (edgeLabel n j)) i

def fieldLabels (n : ℕ) : Fin (n+1)→ChainLabel (n+1) :=
  Fin.snoc (edgeLabel n) (terminalLabel n 0)

theorem matrix_liftedLabel {n : ℕ} (p : ChainLabel n) :
    finitePauliMatrix (liftedLabel p).1=coupleSnoc n (boolPauliOption none) (finitePauliMatrix p.1) :=
  (coupleSnoc_pauli n _ none).symm

theorem matrix_lastBondLabel (n : ℕ) :
    finitePauliMatrix (lastBondLabel n).1=coupleSnoc (n+1) (finiteQubitPauli 2) (lastPauli n 0) := by
  rw [lastPauli_word]
  exact (coupleSnoc_pauli (n+1) _ (some 2)).symm

theorem matrix_terminalLabel (n : ℕ) (q : Fin 3) : finitePauliMatrix (terminalLabel n q).1=lastPauli n q :=
  (lastPauli_word n q).symm

end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
