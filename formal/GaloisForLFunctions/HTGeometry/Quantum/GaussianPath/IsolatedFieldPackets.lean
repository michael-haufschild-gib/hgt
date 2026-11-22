import GaloisForLFunctions.HTGeometry.Quantum.DisjointSiteCircuitApproximation
import GaloisForLFunctions.HTGeometry.Quantum.PathPauliSpectralWidth
import GaloisForLFunctions.HTGeometry.AveragedCentralizerProjectionFloor

/-! # Spectral distance for a packet of equal longitudinal fields -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Longitudinal field of strength q on each selected site, zero elsewhere. -/
def longitudinalPacket {n : ℕ} (S : Finset (Fin (n+2))) (q : ℝ) : PathShell n :=
  WithLp.toLp 2 fun l => match l with
  | .inl (s,a) => if a=2 ∧ s ∈ S then q else 0
  | .inr _ => 0

/-- Total absolute mass of a uniform longitudinal packet, both as a full
Pauli shell and as a list of onsite Z coefficients. -/
theorem longitudinalPacket_mass {n : ℕ} (S : Finset (Fin (n+2))) (q : ℝ) :
    (∑ l : PathLabel n, |longitudinalPacket S q l|) = S.card*|q| ∧
      (∑ v : Fin (n+2), |longitudinalPacket S q (.inl (v,2))|) = S.card*|q| := by
  classical
  have hz (s : Fin (n+2)) :
      (∑ a : Fin 3, |longitudinalPacket S q (.inl (s,a))|) =
        if s ∈ S then |q| else 0 := by
    by_cases hs : s ∈ S <;> simp [longitudinalPacket,hs,abs_ite]
  constructor
  · rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
    simp only [hz,show ∀ e : Fin (n+1) × Fin 3 × Fin 3,
      |longitudinalPacket S q (.inr e)| = 0 from fun _ => abs_zero,
      Finset.sum_const_zero,add_zero]
    simp
  · simp [longitudinalPacket,abs_ite]

/-- At time t the scalar-approximation deficit of a packet of identical fields
is at most the distance of t q |S| from π/2. -/
theorem longitudinal_packet_scalar_floor {n : ℕ} (S : Finset (Fin (n+2))) (hS : 0 < S.card)
    (q : ℝ) (hq : 0 < q) (t : ℝ) (z : ℂ) :
    1 ≤ ‖unitaryEvolution (pathHamiltonian (longitudinalPacket S q)) t-z • (1:Reg (n+2))‖ +
      |t*((S.card:ℝ)*q)-Real.pi/2| := by
  let u := longitudinalPacket S q
  let H := pathHamiltonian u
  let M := (S.card:ℝ)*q
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨h1,h2⟩ := longitudinalPacket_mass S q
  rw [abs_of_pos hq] at h1 h2
  have hnorm : ‖H‖ ≤ M := by
    change ‖pathHamiltonian u‖ ≤ (S.card:ℝ)*q
    rw [← h1,pathHamiltonian_eq_sum]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro l _
    rw [norm_smul,norm_finitePauliMatrix,mul_one,Complex.norm_real,Real.norm_eq_abs]
  let hH := (isSelfAdjoint_pathHamiltonian u).isHermitian
  obtain ⟨i,j,hlo,_⟩ := exists_path_spectral_width_ge_onsite u
  let E := hH.eigenvalues
  change 2*(∑ s : Fin (n+2), |u (.inl (s,2))|) ≤ E i-E j at hlo
  rw [h2] at hlo
  have hi := (abs_le.mp (abs_eigenvalue_le_l2_opNorm hH i)).2
  have hj := (abs_le.mp (abs_eigenvalue_le_l2_opNorm hH j)).1
  change E i ≤ ‖H‖ at hi
  change -‖H‖ ≤ E j at hj
  have hgap : E i-E j = 2*M := le_antisymm (by linarith only [hi,hj,hnorm]) hlo
  have hne : E i ≠ E j := by intro he; rw [he,sub_self] at hgap; linarith
  have hhard := half_gap_time_scalar_error_ge_one hH i j hne z
  change 1 ≤ ‖unitaryEvolution H (Real.pi/(E i-E j))-z • (1:Reg (n+2))‖ at hhard
  rw [hgap] at hhard
  let v := Real.pi/(2*M)
  have heq : (v-t)*M = Real.pi/2-t*M := by dsimp [v]; field_simp [hM.ne']
  have hs : ‖unitaryEvolution H v-unitaryEvolution H t‖ ≤ |t*M-Real.pi/2| := by
    calc
      _ ≤ ‖H‖*|v-t| := norm_unitaryEvolution_time_sub_le (isSelfAdjoint_pathHamiltonian u) _ _
      _ ≤ M*|v-t| := mul_le_mul_of_nonneg_right hnorm (abs_nonneg _)
      _ = _ := by
        calc
          _ = |(v-t)*M| := by rw [abs_mul,abs_of_pos hM,mul_comm]
          _ = _ := by rw [heq,abs_sub_comm]
  have hh := norm_sub_le_norm_sub_add_norm_sub (unitaryEvolution H v) (unitaryEvolution H t)
    (z • (1:Reg (n+2)))
  change 1 ≤ ‖unitaryEvolution H v - z • (1:Reg (n+2))‖ at hhard
  change 1 ≤ ‖unitaryEvolution H t - z • (1:Reg (n+2))‖ + |t*M-Real.pi/2|
  linarith only [hhard,hh,hs]

#print axioms longitudinal_packet_scalar_floor
end
end GaloisForLFunctions.HTGeometry
