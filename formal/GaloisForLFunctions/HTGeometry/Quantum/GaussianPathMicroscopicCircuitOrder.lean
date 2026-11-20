import GaloisForLFunctions.HTGeometry.Quantum.SparsePathCircuitCompiler
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathMicroscopicCircuitFloor

/-!
# Sharp circuit order on an inverse-size time interval

A single constant number of Lie product steps suffices throughout any
fixed multiple of the inverse system size. At half the period of the
spectral width the extensive upper bound coincides in order with the
support-deletion lower bound.
-/
open MeasureTheory Filter Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private theorem coefficient_mass_le {n : ℕ} (u : PathShell n) (b : ℝ)
    (hb : ‖u‖^2 ≤ b*((n+2:ℕ):ℝ)) :
    ∑ l : PathLabel n, |u l| ≤ (12+b)*((n+2:ℕ):ℝ) := by
  have h (l : PathLabel n) : |u l| ≤ 1+(u l)^2 := by
    rw [← sq_abs (u l)]
    nlinarith only [sq_nonneg (|u l|-1/2)]
  have hs := Finset.sum_le_sum (s := Finset.univ) fun l _ => h l
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hs
  have hn : ∑ l, (u l)^2 = ‖u‖^2 := by simp [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs]
  have hd : (Fintype.card (PathLabel n):ℝ) ≤ 12*((n+2:ℕ):ℝ) := by
    simp [PathLabel,Fintype.card_sum,Fintype.card_prod]
    linarith
  linarith only [hs,hn,hb,hd]

/-- At one-tenth error, almost surely the gate count on a growing Gaussian
path is bounded above by a fixed multiple of its length for all times
whose absolute value is bounded by a fixed multiple of its inverse length. -/
theorem gaussian_path_inverse_size_circuit_upper (B : ℝ) :
    ∃ k : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      ((n+2:ℕ):ℝ)*|t| ≤ B → ∃ z : ℂ, ‖z‖ = 1 ∧ ∃ C : TwoQubitCircuit (n+2),
        C.gateCount ≤ k*(n+2) ∧
        ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t -
          z • (C.eval : Reg (n+2))‖ ≤ 1/10 := by
  obtain ⟨a,b,_,hb,h⟩ := gaussian_path_eventual_coefficient_mass
  let L := 12+b
  have hL : 0 ≤ L := by dsimp [L]; linarith
  obtain ⟨r,hr⟩ := exists_nat_gt (10*(L*B)^2)
  have hr0 : 0 < r := by exact_mod_cast (lt_of_le_of_lt (by positivity : 0 ≤ 10*(L*B)^2) hr)
  refine ⟨r*12,?_⟩
  filter_upwards [h] with ω hω
  filter_upwards [hω] with n hn
  intro t ht
  let u := pathPauliDisorderShell ω n
  have hm := coefficient_mass_le u b hn.2
  have htm : (∑ l, |u l|)*|t| ≤ L*B := by
    calc
      _ ≤ (L*((n+2:ℕ):ℝ))*|t| := mul_le_mul_of_nonneg_right hm (abs_nonneg _)
      _ = L*(((n+2:ℕ):ℝ)*|t|) := mul_assoc _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left ht hL
  have hq := pow_le_pow_left₀ (mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (abs_nonneg _)) htm 2
  obtain ⟨z,hz,C,hC,he⟩ := exists_sparse_path_circuit u t r hr0
  refine ⟨z,hz,C,?_,he.trans ?_⟩
  · have hd : Fintype.card (PathLabel n) ≤ 12*(n+2) := by
      simp [PathLabel,Fintype.card_sum,Fintype.card_prod]
      omega
    rw [hC,mul_assoc]
    exact Nat.mul_le_mul_left r hd
  · rw [div_le_iff₀ (by exact_mod_cast hr0)]
    rw [mul_pow] at hq
    linarith only [hr,hq]

/-- Almost surely, every sufficiently long prefix of the same Gaussian
Pauli chain has a time interval of width of order 1/N, centered at the
spectral half-period, on which minimum gate count has order N. -/
theorem gaussian_path_inverse_bandwidth_circuit_order :
    ∃ A B W c : ℝ, ∃ k : ℕ, 0 < A ∧ 0 < B ∧ 0 < W ∧ 0 < c ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
        let u := pathPauliDisorderShell ω n
        let N : ℝ := n+2
        let E := (isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues
        ∃ i j, (∀ p q, E p - E q ≤ E i - E j) ∧
          let t := Real.pi/(E i-E j)
          A ≤ N*t ∧ N*t ≤ B ∧
          ∀ τ : ℝ, N*|t-τ| ≤ W →
            (∃ z : ℂ, ‖z‖ = 1 ∧ ∃ C : TwoQubitCircuit (n+2), C.gateCount ≤ k*(n+2) ∧
              ‖unitaryEvolution (pathHamiltonian u) τ - z • (C.eval : Reg (n+2))‖ ≤ 1/10) ∧
            (∀ (C : TwoQubitCircuit (n+2)) (z : ℂ),
              ‖unitaryEvolution (pathHamiltonian u) τ - z • (C.eval : Reg (n+2))‖ ≤ 1/10 →
                c*N ≤ C.gateCount) := by
  obtain ⟨A,B,W,c,hA,hB,hW,hc,hlo⟩ := gaussian_path_microscopic_circuit_floor
  obtain ⟨k,hhi⟩ := gaussian_path_inverse_size_circuit_upper (B+W)
  refine ⟨A,B,W,c,k,hA,hB,hW,hc,?_⟩
  filter_upwards [hlo,hhi] with ω hω hω'
  filter_upwards [hω,hω'] with n hn hn'
  obtain ⟨i,j,hmax,hA',hB',hl⟩ := hn
  refine ⟨i,j,hmax,hA',hB',?_⟩
  intro τ hτ
  refine ⟨hn' τ ?_,hl τ hτ⟩
  let N : ℝ := n+2
  let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)).isHermitian.eigenvalues
  let t := Real.pi/(E i-E j)
  change A ≤ N*t at hA'
  change N*t ≤ B at hB'
  change N*|t-τ| ≤ W at hτ
  have hN : 0 < N := by dsimp [N]; positivity
  have ht : 0 < t := pos_of_mul_pos_right (hA.trans_le hA') hN.le
  have hab : |τ| ≤ |t|+|t-τ| := by simpa [abs_sub_comm t τ,add_comm] using abs_sub_le τ t 0
  rw [abs_of_pos ht] at hab
  have hx := mul_le_mul_of_nonneg_left hab hN.le
  change ((n+2:ℕ):ℝ)*|τ| ≤ _
  push_cast
  change N*|τ| ≤ _
  linarith only [hx,hB',hτ]

#print axioms gaussian_path_inverse_bandwidth_circuit_order
end
end GaloisForLFunctions.HTGeometry
