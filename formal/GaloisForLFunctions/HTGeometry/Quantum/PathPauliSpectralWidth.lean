import GaloisForLFunctions.HTGeometry.PathHamiltonianSiteRestriction
import GaloisForLFunctions.HTGeometry.EternityObservableHorizonLaw
import GaloisForLFunctions.HTGeometry.ProjectiveOperatorNormReturnTarget

/-!
# Spectral width from the onsite fields of an interacting Pauli chain

Align the computational bits with the onsite Z fields. Flipping every bit
reverses those fields and preserves all ZZ energies. Off-diagonal Pauli
terms have zero expectation in both configurations.
-/
open Matrix
open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {n : ℕ}

private theorem pauli_diag_zero_of_xy {p : Fin (n+2) → Option (Fin 3)}
    (x : Fin (n+2) → Bool) (s : Fin (n+2)) {a : Fin 3}
    (hs : p s = some a) (ha : a ≠ 2) : finitePauliMatrix p x x = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ s)
  rw [hs]
  fin_cases a <;> simp_all [boolPauliOptionEntry,boolPauliOption,finiteQubitPauli]

private theorem path_word_offdiag_zero (l : PathLabel n) (hl : ¬ IsDiagLabel l)
    (x : Fin (n+2) → Bool) : finitePauliMatrix (pathWord l) x x = 0 := by
  rcases l with ⟨s,a⟩ | ⟨e,a,b⟩
  · exact pauli_diag_zero_of_xy x s (by simp [pathWord,onsiteWord]) hl
  · by_cases ha : a = 2
    · have hb : b ≠ 2 := fun h => hl (by simp [IsDiagLabel,ha,h])
      have he : e.succ ≠ e.castSucc := fun h => by have := congrArg Fin.val h; simp at this
      exact pauli_diag_zero_of_xy x e.succ (by simp [pathWord,couplingWord,he]) hb
    · exact pauli_diag_zero_of_xy x e.castSucc (by simp [pathWord,couplingWord]) ha

/-- The diagonal entries equal the classical Ising energies for arbitrary
coefficients, including transverse fields and off-diagonal couplings. -/
theorem pathHamiltonian_diagonal_entry (u : PathShell n) (x : Fin (n+2) → Bool) :
    pathHamiltonian u x x = (pathDiagEnergy u x : ℂ) := by
  let v : PathShell n := WithLp.toLp 2 (fun l => if IsDiagLabel l then u l else 0)
  have hv (l : PathLabel n) : v l = if IsDiagLabel l then u l else 0 := rfl
  have he : pathHamiltonian u x x = pathHamiltonian v x x := by
    simp only [pathHamiltonian_eq_sum,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro l _
    by_cases h : IsDiagLabel l
    · rw [hv,if_pos h]
    · rw [path_word_offdiag_zero l h x,mul_zero,mul_zero]
  rw [he,pathHamiltonian_eq_diagonal v (fun l h => by rw [hv,if_neg h]),Matrix.diagonal_apply_eq]
  simp only [pathDiagEnergy,hv,IsDiagLabel,if_true]

private def alignField (u : PathShell n) (s : Fin (n+2)) : Bool :=
  decide (u (.inl (s,2)) < 0)

private theorem aligned_energy_difference (u : PathShell n) :
    pathDiagEnergy u (alignField u) - pathDiagEnergy u (fun i => !(alignField u i))
      = 2 * ∑ s : Fin (n+2), |u (.inl (s,2))| := by
  let x := alignField u
  have flip_pair (a b : Bool) :
      (if !a then (-1:ℝ) else 1) * (if !b then -1 else 1) =
        (if a then -1 else 1) * (if b then -1 else 1) := by
    cases a <;> cases b <;> norm_num
  have hedge (e : Fin (n+1)) :
      zSetSign {e.castSucc,e.succ} (fun i => !(x i)) = zSetSign {e.castSucc,e.succ} x := by
    have he : e.castSucc ≠ e.succ := fun h => by have := congrArg Fin.val h; simp at this
    simp only [zSetSign,Finset.prod_insert (Finset.notMem_singleton.mpr he),Finset.prod_singleton]
    exact flip_pair _ _
  change pathDiagEnergy u x - pathDiagEnergy u (fun i => !(x i)) = _
  simp only [pathDiagEnergy,hedge,add_sub_add_right_eq_sub,← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : u (.inl (s,2)) < 0
  · simp [zSetSign_singleton,x,alignField,h,abs_of_neg h]; ring
  · simp [zSetSign_singleton,x,alignField,h,abs_of_nonneg (le_of_not_gt h)]; ring

private theorem diag_distance_le_half_spread {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {H : Matrix I I ℂ} (hH : H.IsHermitian) (a b : ℝ)
    (ha : ∀ k, a ≤ hH.eigenvalues k) (hb : ∀ k, hH.eigenvalues k ≤ b) (x : I) :
    ‖H x x - (((a+b)/2 : ℝ) : ℂ)‖ ≤ (b-a)/2 := by
  let z : ℂ := (((a+b)/2 : ℝ) : ℂ)
  let V := (hH.eigenvectorUnitary : Matrix I I ℂ)
  have hV : V ∈ unitary (Matrix I I ℂ) := hH.eigenvectorUnitary.2
  have hone : z • (1 : Matrix I I ℂ) = V * Matrix.diagonal (fun _ : I => z) * star V := by
    rw [← smul_one_eq_diagonal_const z,Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,
      (Unitary.mem_iff.mp hV).2]
  have hentry := norm_entry_le_l2_opNorm (H-z • (1 : Matrix I I ℂ)) x x
  simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one] at hentry
  apply hentry.trans
  conv_lhs => rw [isHermitian_eq_conj_diagonal hH,hone]
  rw [← Matrix.sub_mul,← Matrix.mul_sub,Matrix.diagonal_sub,l2_opNorm_unitary_conj_eq hV,
    Matrix.l2_opNorm_diagonal,pi_norm_le_iff_of_nonempty]
  intro k
  change ‖(hH.eigenvalues k : ℂ) - (((a+b)/2 : ℝ) : ℂ)‖ ≤ _
  rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_le]
  constructor <;> linarith only [ha k,hb k]

/-- The spectral diameter dominates twice the sum of the absolute onsite
Z fields, independently of all other coefficients. The displayed pair
realizes the diameter among the full interacting eigenvalues. -/
theorem exists_path_spectral_width_ge_onsite (u : PathShell n) :
    let E := (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues
    ∃ i j, 2 * ∑ s : Fin (n+2), |u (.inl (s,2))| ≤ E i - E j ∧
      ∀ k l, E k - E l ≤ E i - E j := by
  classical
  let hH := (isSelfAdjoint_pathHamiltonian u).isHermitian
  let E := hH.eigenvalues
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ E Finset.univ_nonempty
  obtain ⟨j,_,hj⟩ := Finset.exists_min_image Finset.univ E Finset.univ_nonempty
  have hlo k := hj k (Finset.mem_univ k)
  have hhi k := hi k (Finset.mem_univ k)
  refine ⟨i,j,?_,fun k l => sub_le_sub (hhi k) (hlo l)⟩
  have hdist (x : Fin (n+2) → Bool) :
      |pathDiagEnergy u x - (E j + E i)/2| ≤ (E i-E j)/2 := by
    have h := diag_distance_le_half_spread hH (E j) (E i) hlo hhi x
    rwa [pathHamiltonian_diagonal_entry,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at h
  have hx := (abs_le.mp (hdist (alignField u))).2
  have hy := (abs_le.mp (hdist (fun k => !(alignField u k)))).1
  rw [← aligned_energy_difference u]
  change _ ≤ E i - E j
  linarith only [hx,hy]

#print axioms exists_path_spectral_width_ge_onsite
end
end GaloisForLFunctions.HTGeometry
