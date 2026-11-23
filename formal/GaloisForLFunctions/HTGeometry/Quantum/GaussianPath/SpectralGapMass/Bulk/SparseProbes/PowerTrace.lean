import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.SparseProbes.LocalTrace
import GaloisForLFunctions.HTGeometry.Quantum.LocalPacketComparison

/-! # Spectral moments of a sparse circuit composed with physical evolution -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk.SparseProbes
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

private theorem rotate_regTrace {N : ℕ} (A B C : Reg N) :
    regTrace (A*B*C)=regTrace (C*A*B) :=
  congrArg (fun z : ℂ => z/(2:ℂ)^N) (Matrix.trace_mul_cycle A B C)

private theorem test_powers {N : ℕ} {A B : Reg N} (ha : A ∈ unitary _) (hb : B ∈ unitary _)
    {d : ℝ} (h : ∀ Z : Reg N, Z ∈ unitary _ → ‖regTrace (Z*A)-regTrace (Z*B)‖ ≤ d)
    (k : ℕ) (Z : Reg N) (hz : Z ∈ unitary _) :
    ‖regTrace (Z*A^k)-regTrace (Z*B^k)‖ ≤ k*d := by
  induction k generalizing Z with
  | zero => simp
  | succ k ih =>
    have h₁ := ih (Z*A) ((unitary _).mul_mem hz ha)
    have h₂ := h (B^k*Z) ((unitary _).mul_mem ((unitary _).pow_mem hb k) hz)
    rw [←rotate_regTrace Z A (B^k),←rotate_regTrace Z B (B^k)] at h₂
    rw [pow_succ' A,pow_succ' B,←mul_assoc,←mul_assoc]
    exact (norm_sub_le_norm_sub_add_norm_sub _ (regTrace (Z*A*B^k)) _).trans
      ((add_le_add h₁ h₂).trans_eq (by push_cast; ring))

private theorem supported_pow {N : ℕ} {S : Finset (Fin N)} {A : Reg N} (ha : IsSiteSupported S A)
    (k : ℕ) : IsSiteSupported S (A^k) := by
  induction k with
  | zero => simpa only [pow_zero] using IsSiteSupported.one S
  | succ k ih => rw [pow_succ]; exact ih.matrix_mul ha

private theorem inserted_powers {n : ℕ} (u v : PathShell n) (t : ℝ) (k : ℕ)
    (W : Reg (n+2)) (hw : W ∈ unitary _) :
    let U := unitaryEvolution (pathHamiltonian u) t
    let V := unitaryEvolution (pathHamiltonian v) t
    ‖regTrace ((W*U)^k)-regTrace ((W*V)^k)‖ ≤
      k*(|t| *Real.sqrt (∑ l : PathLabel n, (u l-v l)^2)) := by
  intro U V
  have hu := unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian u) t
  have hv := unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian v) t
  have h (Z : Reg (n+2)) (hz : Z ∈ unitary _) :
      ‖regTrace (Z*(W*U))-regTrace (Z*(W*V))‖ ≤ |t| *Real.sqrt (∑ l : PathLabel n, (u l-v l)^2) := by
    let T : unitaryGroup (Fin (n+2)→Bool) ℂ := ⟨(Z*W)ᴴ,Unitary.star_mem ((unitary _).mul_mem hz hw)⟩
    have hh := trace_change u v t T
    change ‖regTrace ((Z*W)ᴴᴴ*U)-regTrace ((Z*W)ᴴᴴ*V)‖ ≤ _ at hh
    simpa only [Matrix.conjTranspose_conjTranspose,mul_assoc] using hh
  simpa only [one_mul] using test_powers ((unitary _).mul_mem hw hu) ((unitary _).mul_mem hw hv) h k
    (1 : Reg (n+2)) (unitary _).one_mem

/-- Every Fourier mode of the relative circuit spectrum nearly factors.
The error is linear in the mode and uniform over all unitaries on S. -/
theorem supported_power_covariance {n : ℕ} (S : Finset (Fin (n+2))) (u : PathShell n)
    (t : ℝ) (k : ℕ) (W : Reg (n+2)) (hw : W ∈ unitary _) (hs : IsSiteSupported S W) :
    let U := unitaryEvolution (pathHamiltonian u) t
    ‖regTrace ((W*U)^k)-regTrace (W^k)*regTrace (U^k)‖ ≤
      2*k* |t| *Real.sqrt (∑ l ∈ S.biUnion pathIncidentLabels, (u l)^2) := by
  intro U
  let v := pathShellOnSites Sᶜ u
  let V := unitaryEvolution (pathHamiltonian v) t
  let d := |t| *Real.sqrt (∑ l : PathLabel n, (u l-v l)^2)
  have hV : IsSiteSupported Sᶜ V := by
    apply isSiteSupported_unitaryEvolution
    rw [←pathHamiltonianOnSites_eq_pathHamiltonian_pathShellOnSites]
    exact pathHamiltonianOnSites_isSiteSupported _ _
  have he : regTrace ((W*V)^k)=regTrace (W^k)*regTrace (V^k) := by
    rw [(commute_of_isSiteSupported_disjoint disjoint_compl_right hs hV).mul_pow]
    exact disjoint_regTrace disjoint_compl_right (supported_pow hs k) (supported_pow hV k)
  have h₁ : ‖regTrace ((W*U)^k)-regTrace ((W*V)^k)‖ ≤ k*d := inserted_powers u v t k W hw
  have h₂ : ‖regTrace (U^k)-regTrace (V^k)‖ ≤ k*d := by
    simpa only [one_mul] using inserted_powers u v t k 1 (unitary _).one_mem
  have h₃ := norm_sub_le_norm_sub_add_norm_sub (regTrace ((W*U)^k)) (regTrace ((W*V)^k))
    (regTrace (W^k)*regTrace (U^k))
  rw [he] at h₁ h₃
  rw [←mul_sub,norm_mul,norm_sub_rev (regTrace (V^k))] at h₃
  have hterm := mul_le_of_le_one_left (norm_nonneg (regTrace (U^k)-regTrace (V^k)))
    (norm_regTrace_le_one ((unitary _).pow_mem hw k))
  have hm := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (deleted_mass S u)) (abs_nonneg t)
  change d ≤ _ at hm
  exact (h₃.trans (add_le_add h₁ (hterm.trans h₂))).trans
    ((add_le_add (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg k))
      (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg k))).trans_eq (by ring))

#print axioms supported_power_covariance
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk.SparseProbes
