import GaloisForLFunctions.HTGeometry.PauliChainSpan

/-! # Computational basis blocks of a Pauli chain after appending a spin -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
noncomputable section
abbrev Config (N : ℕ) := Fin N → Bool
abbrev Register (N : ℕ) := Matrix (Config N) (Config N) ℂ

private def spinTag (I : Type*) : I ⊕ I ≃ I × Bool where
  toFun := Sum.elim (fun i => (i,false)) (fun i => (i,true))
  invFun := fun q => if q.2 then Sum.inr q.1 else Sum.inl q.1
  left_inv i := by cases i <;> rfl
  right_inv q := by rcases q with ⟨i,b⟩; cases b <;> rfl

/-- The first block is the new spin's positive Z eigenspace. -/
def blockConfig (n : ℕ) : Config n ⊕ Config n ≃ Config (n+1) := (spinTag _).trans (snocConfig n)

def blocks (n : ℕ) (H : Register (n+1)) := Matrix.reindex (blockConfig n).symm (blockConfig n).symm H

theorem blocks_tensor (n : ℕ) (B : Matrix Bool Bool ℂ) (A : Register n) :
    blocks n (coupleSnoc n B A) =
      fromBlocks (B false false • A) (B false true • A) (B true false • A) (B true true • A) := by
  ext i j
  cases i <;> cases j <;>
    simp [blocks,blockConfig,spinTag,Matrix.reindex_apply,Matrix.submatrix_apply,layerMatrixCoupling,
      Matrix.fromBlocks,Matrix.smul_apply,mul_comm]

/-- The new spin's onsite Pauli, in the original register indexing. -/
def lastPauli (n : ℕ) (q : Fin 3) : Register (n+1) := coupleSnoc n (finiteQubitPauli q) 1

theorem lastPauli_word (n : ℕ) (q : Fin 3) :
    lastPauli n q=finitePauliMatrix (Fin.snoc (pauliIdentityLabel n) (some q)) := by
  have hid : (1 : Register n)=finitePauliMatrix (pauliIdentityLabel n) := by
    ext x y
    rw [finitePauliMatrix_pauliIdentityLabel]
    simp only [Matrix.one_apply]
  unfold lastPauli
  rw [hid]
  exact coupleSnoc_pauli n _ (some q)

theorem lastPauli_square (n : ℕ) (q : Fin 3) : lastPauli n q * lastPauli n q=1 := by
  rw [lastPauli_word,finitePauliMatrix_mul_self]

theorem lastPauli_mem (n : ℕ) (q : Fin 3) : lastPauli n q ∈ pauliSiteSpan (n+1) (Fin.last n) :=
  couple_field_mem_pauliSiteSpan n q

theorem blocks_add (n : ℕ) (A B : Register (n+1)) : blocks n (A+B)=blocks n A+blocks n B := rfl

theorem blocks_real_smul (n : ℕ) (c : ℝ) (A : Register (n+1)) : blocks n (c • A)=(c:ℂ) • blocks n A := by
  ext i j
  exact Complex.real_smul

end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
