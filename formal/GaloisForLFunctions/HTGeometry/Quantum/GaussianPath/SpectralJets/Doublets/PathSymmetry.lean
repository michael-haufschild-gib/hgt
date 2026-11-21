import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.SplitPencil
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.WalshWords

/-! # Spin reversal along the physical splitting pencil -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section

def reversal (n : ℕ) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun := reverseSpins
  invFun := reverseSpins
  left_inv s := by funext i; simp [reverseSpins]
  right_inv s := by funext i; simp [reverseSpins]

theorem reversed_ne {n : ℕ} (s : Fin (n+1) → Bool) : s≠reverseSpins s := by
  intro he
  have h := congrFun he 0
  change s 0 = !(s 0) at h
  exact (Bool.not_eq_self (s 0)).mp h.symm

private theorem reversed_bondEnergy {n : ℕ} (s : Fin (n+1) → Bool) :
    bondEnergy (reverseSpins s)=bondEnergy s := by
  have h := (walls_eq_iff _ s).mpr (Or.inr rfl)
  simp only [bondEnergy,h]

private theorem reversed_toggle {n : ℕ} (s : Fin n → Bool) (i : Fin n) :
    reverseSpins (boolToggle s i)=boolToggle (reverseSpins s) i := by
  funext j
  by_cases hj : j=i
  · subst j; simp [reverseSpins,boolToggle]
  · simp [reverseSpins,boolToggle,Function.update_of_ne hj]

theorem split_matrix (n : ℕ) (v : ℝ) :
    pathHamiltonian (splitShell n v) =
      (1-v) • pathHamiltonian (isingShell n) + v • pathHamiltonian (transverseShell n) :=
  (pathHamiltonianLM n).map_add _ _ |>.trans (by rw [map_smul,map_smul]; rfl)

/-- Global bit reversal preserves each matrix entry of the full local
pencil. Only the additional longitudinal perturbations change sign. -/
theorem reversed_split {n : ℕ} (v : ℝ) (s t : Fin (n+2) → Bool) :
    pathHamiltonian (splitShell n v) (reverseSpins s) (reverseSpins t) =
      pathHamiltonian (splitShell n v) s t := by
  have hst : reverseSpins s=reverseSpins t ↔ s=t := (reversal (n+2)).injective.eq_iff
  rw [split_matrix,diagonal_ising,transverse_matrix]
  simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.diagonal_apply,hst,reversed_bondEnergy,
    Walsh.transverseOnly,Matrix.of_apply]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  have hi : reverseSpins t=boolToggle (reverseSpins s) i ↔ t=boolToggle s i := by
    rw [←reversed_toggle]
    exact (reversal (n+2)).injective.eq_iff
  by_cases h : t=boolToggle s i
  · rw [if_pos (hi.mpr h),if_pos h]
  · rw [if_neg (fun he => h (hi.mp he)),if_neg h]

/-- Every longitudinal direction used in the doublet response is an
onsite Z coefficient of the original path family. -/
def longitudinalShell {n : ℕ} (h : Fin (n+2) → ℝ) : PathShell n := WithLp.toLp 2 fun l => match l with
  | .inl (i,a) => if a=2 then h i else 0
  | .inr _ => 0

theorem longitudinal_matrix {n : ℕ} (h : Fin (n+2) → ℝ) :
    pathHamiltonian (longitudinalShell h) = diagonal
      (fun s => fieldEnergy (fun i => Walsh.boolSign (s i)) (fun i => (h i:ℂ))) := by
  rw [pathHamiltonian_eq_diagonal (longitudinalShell h) (by
    rintro (⟨i,a⟩|⟨i,ab⟩) ha
    · exact if_neg ha
    · rfl)]
  apply congrArg Matrix.diagonal
  funext s
  have hb (e : Fin (n+1)) : longitudinalShell h (.inr (e,2,2))=0 := rfl
  have hz (i : Fin (n+2)) : longitudinalShell h (.inl (i,2))=h i := by
    change (if (2:Fin 3)=2 then h i else 0)=h i
    rw [if_pos rfl]
  simp only [pathDiagEnergy,hb,hz,zero_mul,Finset.sum_const_zero,add_zero,
    Complex.ofReal_sum,Complex.ofReal_mul,fieldEnergy]
  apply Finset.sum_congr rfl
  intro i _
  cases hi : s i <;> simp [zSetSign,Walsh.boolSign,hi]

#print axioms reversed_split
#print axioms longitudinal_matrix
end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
