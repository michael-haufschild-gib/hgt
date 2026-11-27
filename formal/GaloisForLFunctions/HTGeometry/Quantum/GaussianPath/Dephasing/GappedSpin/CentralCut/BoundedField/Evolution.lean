import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.CommutatorBounds.Sectors.StableInverse
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Transverse

/-! # Quadratic transverse error near a bounded separated Ising carrier -/

open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open DiagonalSynthesis DiagonalSynthesis.CommutatorBounds.Sectors
open private spin_core spin_offAxis from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Transverse
noncomputable section
variable {n : ℕ}

/-- The diagonal spacing alone controls transverse mixing. The
longitudinal central field may have the same size as the other fields. -/
theorem separated_core_evolution (q : Fin (n+2)) (u : PathShell n) (d : (Fin (n+2) → Bool) → ℝ)
    {g : ℝ} (hg : 0 < g) (hsep : ∀ i j, i≠j → g ≤ |d i-d j|)
    (htiny : 2*(sqrt packConstant/g)*‖pathHamiltonian (core q u)-diagonal (fun i => (d i:ℂ))‖ ≤ 1/2)
    (t : ℝ) :
    let H := pathHamiltonian (core q u)
    let V := pathHamiltonian (offAxis q u)
    ‖unitaryEvolution (pathHamiltonian u) t-unitaryEvolution H t‖ ≤
      (2+|t| * ‖V‖)*(2*(sqrt packConstant/g)*‖V‖) := by
  intro H V
  let D := diagonal fun i => (d i:ℂ)
  let b := fun i : Fin (n+2) → Bool => zSign (i q)
  letI : CStarAlgebra (Register (n+2)) := {}
  have hz : spin q = diagonal b := by
    ext x y
    change finitePauliMatrix (pauliZLabel q) x y=_
    rw [finitePauliMatrix_pauliZLabel]
    by_cases he : x=y
    · subst y; rw [if_pos rfl,diagonal_apply_eq]
    · rw [if_neg he,diagonal_apply_ne _ he]
  have hb (i) : b i≠0 := by dsimp only [b,zSign]; split <;> norm_num
  have he : Within b (H-D) := by
    have hc : Commute (diagonal b) H := hz ▸ spin_core q u
    intro i j hij
    have hne : i≠j := fun h => hij (congrArg b h)
    rw [Matrix.sub_apply,within_of_commute b hc i j hij,show D i j=0 from diagonal_apply_ne _ hne,sub_zero]
  have ho : Across b V := by
    apply across_of_anticommute b hb
    rw [←hz]
    exact spin_offAxis q u
  obtain ⟨X,_,hcomm,hbound⟩ := stable_inverse b d hg hsep (H-D) V he ho htiny
  have hh : D+(H-D)=H := by abel
  change (D+(H-D))*X-X*(D+(H-D))=V at hcomm
  rw [hh] at hcomm
  have hfit := field_evolution_bound H V 0 X (isSelfAdjoint_pathHamiltonian _)
    (isSelfAdjoint_pathHamiltonian _) (IsSelfAdjoint.zero _) (by simpa only [sub_zero] using hcomm) 1 t
  simp only [one_smul,add_zero,abs_one,mul_one,one_pow,mul_zero,zero_sub,norm_neg] at hfit
  have hsplit : H+V=pathHamiltonian u := (sum_restricted (axial q) u).symm
  change ‖unitaryEvolution (H+V) t-unitaryEvolution H t‖ ≤ _ at hfit
  rw [hsplit] at hfit
  calc
    _ ≤ 2*‖X‖+|t| * ‖V*X‖ := hfit
    _ ≤ 2*‖X‖+|t| * (‖V‖*‖X‖) := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (norm_mul_le ..) (abs_nonneg t))
    _ = (2+|t| * ‖V‖)*‖X‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)

#print axioms separated_core_evolution
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
