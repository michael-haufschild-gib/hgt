import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.JoinLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.Intervals

/-! # The restored physical chain differs from its two blocks by nine Pauli terms -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
open FirstAscent.ThermodynamicEdges
open private translate_word place_sum from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.Intervals
noncomputable section

private theorem place_block {n m B : ℕ} (h : B+(m+2)≤n+2) (x : PathLabel n→ℝ) :
    Subregister.place (numberWires h) (pathHamiltonian
      (WithLp.toLp 2 (fun i => x (translateLabel h i)) : PathShell m)) =
      ∑ i : PathLabel m, ((x (translateLabel h i):ℝ):ℂ) • finitePauliMatrix (pathWord (translateLabel h i)) := by
  rw [pathHamiltonian_eq_sum,place_sum]
  apply sum_congr rfl
  intro i _
  rw [Subregister.place_smul,←translate_word]

/-- Hamiltonian obtained by deleting the single joining bond. -/
def blockSum (l r : ℕ) (x : PathLabel (l+r+2)→ℝ) : Register (l+r+2+2) :=
  Subregister.place (numberWires (B:=0) (m:=l) (n:=l+r+2) (by omega))
      (pathHamiltonian (WithLp.toLp 2 (extractBlocks l r x).1.1 : PathShell l)) +
    Subregister.place (numberWires (B:=l+2) (m:=r) (n:=l+r+2) (by omega))
      (pathHamiltonian (WithLp.toLp 2 (extractBlocks l r x).1.2 : PathShell r))

/-- Each seam coefficient has its original operator normalization. -/
theorem seam_error (l r : ℕ) (x : PathLabel (l+r+2)→ℝ) {δ : ℝ}
    (hs : ∀ j, |(extractBlocks l r x).2 j|≤δ) :
    ‖blockSum l r x-pathHamiltonian (WithLp.toLp 2 x : PathShell (l+r+2))‖ ≤ 9*δ := by
  classical
  let term (i : PathLabel (l+r+2)) := ((x i:ℝ):ℂ) • finitePauliMatrix (pathWord i)
  let cut := ∑ j : Fin 3×Fin 3, term (joinLabel l r (.inr (.inr j)))
  have he : pathHamiltonian (WithLp.toLp 2 x : PathShell (l+r+2))=blockSum l r x + cut := by
    rw [pathHamiltonian_eq_sum]
    change (∑ i, term i)=_
    rw [←(joinEquiv l r).sum_comp term]
    simp only [Fintype.sum_sum_type]
    change _=(Subregister.place _ (pathHamiltonian (WithLp.toLp 2 (fun i => x (translateLabel (B:=0) _ i)) : PathShell l))+
      Subregister.place _ (pathHamiltonian (WithLp.toLp 2 (fun i => x (translateLabel (B:=l+2) _ i)) : PathShell r)))+cut
    rw [place_block,place_block,add_assoc]
    rfl
  rw [he,sub_add_eq_sub_sub,sub_self,zero_sub,norm_neg]
  apply (norm_sum_le ..).trans
  calc _ ≤ ∑ _ : Fin 3×Fin 3, δ := by
         apply sum_le_sum
         intro i _
         rw [term,norm_smul,norm_finitePauliMatrix,mul_one,Complex.norm_real,Real.norm_eq_abs]
         exact hs i
       _ = _ := by simp [nsmul_eq_mul]

#print axioms seam_error
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
