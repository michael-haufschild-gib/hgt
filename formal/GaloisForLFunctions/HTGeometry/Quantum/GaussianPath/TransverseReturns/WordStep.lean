import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliRotations
import GaloisForLFunctions.HTGeometry.Quantum.CoefficientMassLieProduct

/-! # A single circuit step for an arbitrary sparse family of bounded-weight Pauli words -/
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.TransverseReturns
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ
local instance (n : ℕ) : CStarAlgebra (Reg n) where

private theorem compile_word {n : ℕ} (Z : List (Reg n)) (t : ℝ) (B : ℕ)
    (hc : ∀ X ∈ Z, ∃ z : ℂ, ‖z‖=1 ∧ ∃ C : TwoQubitCircuit n,
      C.gateCount≤B ∧ exp (t • X)=z • (C.eval : Reg n)) :
    ∃ z : ℂ, ‖z‖=1 ∧ ∃ C : TwoQubitCircuit n, C.gateCount≤Z.length*B ∧
      (Z.map fun X => exp (t • X)).prod=z • (C.eval : Reg n) := by
  induction Z with
  | nil => exact ⟨1,norm_one,TwoQubitCircuit.one n,by simp [TwoQubitCircuit.one],by simp [TwoQubitCircuit.one_eval]⟩
  | cons X Z ih =>
    obtain ⟨a,ha,C,hC,he⟩ := hc X List.mem_cons_self
    obtain ⟨b,hb,F,hF,hf⟩ := ih (fun z hz => hc z (List.mem_cons_of_mem _ hz))
    refine ⟨a*b,by rw [norm_mul,ha,hb,mul_one],C.mul F,?_,?_⟩
    · rw [TwoQubitCircuit.mul_gateCount,List.length_cons,Nat.succ_mul]
      exact Nat.add_le_add hF hC
    · simp only [List.map_cons,List.prod_cons,he,hf,TwoQubitCircuit.mul_eval]
      change (a • (C.eval : Reg n))*(b • (F.eval : Reg n)) = (a*b) • ((C.eval : Reg n)*(F.eval : Reg n))
      rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul]

/-- A real sum of k-body words admits a one-step error at most A t².
The same (2k+1) times the support-list length bounds the gate count
at every time. Repeated words and zero coefficients are allowed. -/
theorem sparse_word_step {n : ℕ} (hn : 2 ≤ n) {I : Type*} [Fintype I]
    (P : I → Fin n → Option (Fin 3)) (a : I → ℝ) (k : ℕ) (hk : ∀ i, pauliWeight (P i) ≤ k) :
    let H := ∑ i, a i • finitePauliMatrix (P i)
    ∃ A > (0:ℝ), ∀ t : ℝ, HasProjectiveCircuitApproximation n (A*t^2)
      (Fintype.card I*(2*k+1)) (unitaryEvolution H t) := by
  classical
  intro H
  let X (i : I) := a i • ((-Complex.I) • finitePauliMatrix (P i))
  let e := (Fintype.equivFin I).symm
  let Z := List.ofFn (fun j => X (e j))
  have hlen : Z.length=Fintype.card I := by simp only [Z,List.length_ofFn]
  have hsum : Z.sum=(-Complex.I) • H := by
    dsimp only [Z,H]
    rw [List.sum_ofFn,Equiv.sum_comp e X,Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  have hmem (z : Reg n) (hz : z∈Z) : ∃ i, z=X i := by
    obtain ⟨j,he⟩ := List.mem_ofFn.mp hz
    exact ⟨e j,he.symm⟩
  have hskew (z : Reg n) (hz : z∈Z) : z∈skewAdjoint (Reg n) := by
    obtain ⟨i,rfl⟩ := hmem z hz
    apply skewAdjoint.smul_mem
    rw [skewAdjoint.mem_iff,star_smul,show star (finitePauliMatrix (P i))=finitePauliMatrix (P i) from finitePauliMatrix_isHermitian _]
    simp
  let K := (Z.map norm).sum^2
  have hK : 0≤K := sq_nonneg _
  refine ⟨K+1,by linarith only [hK],?_⟩
  intro t
  have hc (z : Reg n) (hz : z∈Z) : ∃ c : ℂ, ‖c‖=1 ∧ ∃ C : TwoQubitCircuit n,
      C.gateCount≤2*k+1 ∧ exp (t • z)=c • (C.eval : Reg n) := by
    obtain ⟨i,rfl⟩ := hmem z hz
    obtain ⟨c,hc,C,hC,he⟩ := exists_projective_pauli_rotation_circuit hn (P i) (t*a i)
    refine ⟨c,hc,C,hC.trans (by have h := hk i; omega),?_⟩
    change exp (t • (a i • ((-Complex.I) • finitePauliMatrix (P i))))=_
    rwa [smul_smul]
  obtain ⟨c,hc,C,hC,he⟩ := compile_word Z t (2*k+1) hc
  have herr := list_lie_product_mass_error Z hskew t
  rw [hsum,he,norm_sub_rev,sq_abs] at herr
  rw [hlen] at hC
  exact ⟨c,hc,C,hC,herr.trans (mul_le_mul_of_nonneg_right (by linarith only [hK] : K≤K+1) (sq_nonneg t))⟩

#print axioms sparse_word_step
end
end GaloisForLFunctions.HTGeometry.TransverseReturns
