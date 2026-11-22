import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.PhysicalExtension
import Mathlib.Data.Fin.Rev

/-! # Transporting the distinguishing field to the fixed first site -/
open Matrix
open GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
namespace GaloisForLFunctions.HTGeometry.FirstGate.Boundary
noncomputable section

def reflected (N : ℕ) : Config N ≃ Config N where
  toFun x i := x i.rev
  invFun x i := x i.rev
  left_inv x := funext fun i => by simp
  right_inv x := funext fun i => by simp

private theorem reflect_pauli {N : ℕ} (P : Fin N→Option (Fin 3)) :
    Matrix.reindex (reflected N) (reflected N) (finitePauliMatrix P) =
      finitePauliMatrix (fun i => P i.rev) := by
  ext x y
  change (∏ i, boolPauliOptionEntry (P i) (x i.rev,y i.rev)) = _
  let F (i : Fin N) := boolPauliOptionEntry (P i) (x i.rev,y i.rev)
  exact (Equiv.prod_comp (Fin.revPerm (n := N)) F).symm.trans (by simp [F,Fin.revPerm,finitePauliMatrix])

private theorem reflect_span {N : ℕ} {H : Register N} (hH : H ∈ pauliChainSpan N) :
    Matrix.reindex (reflected N) (reflected N) H ∈ pauliChainSpan N := by
  induction hH using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨P,hP,hn,rfl⟩ := hx
    rw [reflect_pauli]
    apply finitePauliMatrix_mem_pauliLabelSpan
    · intro i j hi hj
      have hij := hP j.rev i.rev hj hi
      simp only [Fin.val_rev] at hij
      have := i.isLt
      have := j.isLt
      omega
    · intro he
      apply hn
      funext i
      simpa [pauliIdentityLabel] using congrFun he i.rev
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih => exact Submodule.smul_mem _ a ih

theorem reflect_lastZ (n : ℕ) :
    Matrix.reindex (reflected (n+1)) (reflected (n+1)) (lastPauli n 2) =
      finitePauliMatrix (pauliZLabel (0 : Fin (n+1))) := by
  rw [lastPauli_word,reflect_pauli]
  apply congrArg finitePauliMatrix
  funext i
  by_cases hi : i=0
  · subst i; simp [pauliZLabel]
  · have hn : i.rev≠Fin.last n := by
      intro he
      exact hi (by simpa using congrArg Fin.rev he)
    obtain ⟨j,hj⟩ := Fin.exists_castSucc_eq.mpr hn
    rw [←hj,Fin.snoc_castSucc]
    simp [pauliIdentityLabel,pauliZLabel,hi]

/-- For each length the same first-site Z distinguishes every level at some
real nearest-neighbour Hamiltonian. -/
theorem exists_resolved_first (n : ℕ) :
    ∃ H ∈ pauliChainSpan (n+1), Resolved H (finitePauliMatrix (pauliZLabel (0 : Fin (n+1)))) := by
  obtain ⟨H,hH,hr⟩ := exists_resolved_end n
  exact ⟨_,reflect_span hH,reflect_lastZ n ▸ hr.reindex (reflected (n+1))⟩

#print axioms exists_resolved_first
end
end GaloisForLFunctions.HTGeometry.FirstGate.Boundary
