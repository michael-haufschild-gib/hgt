import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliRotations
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.BoundedOrbitLogarithm
import GaloisForLFunctions.HTGeometry.Quantum.CoefficientMassLieProduct

/-! # A time-independent gate bound for finite-register evolution -/
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ
private abbrev Words (n : ℕ) := Fin n → Option (Fin 3)
local instance (n : ℕ) : CStarAlgebra (Reg n) where

private theorem card_words (n : ℕ) : Fintype.card (Words n) = 4^n := by
  simp [Words,Fintype.card_option]

/-- Cauchy–Schwarz and Pauli orthogonality control the squared coefficient
mass by the number of Pauli words times the squared operator norm. -/
private theorem mass_sq_le {n : ℕ} (K : selfAdjoint (Reg n)) :
    (∑ P : Words n, |realPauliCoefficient K P|)^2 ≤ (4:ℝ)^n * ‖K.val‖^2 := by
  let f (P : Words n) := ‖pauliCoeff K.val P‖
  have hf (P : Words n) : f P = |realPauliCoefficient K P| := by
    simp [f,pauliCoeff_eq_realPauliCoefficient]
  have hl := le_opNorm_pauliCombination (pauliCoeff K.val)
  rw [sum_pauliCoeff_smul] at hl
  have hs : 0 ≤ ∑ P : Words n, f P ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq := sq_le_sq' ((neg_nonpos.mpr (Real.sqrt_nonneg _)).trans (norm_nonneg _)) hl
  rw [Real.sq_sqrt hs] at hsq
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Words n => (1:ℝ)) f
  have hcard := congrArg (fun i : ℕ => (i:ℝ)) (card_words n)
  push_cast at hcard
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,hcard] at hcs
  simpa only [hf] using hcs.trans (mul_le_mul_of_nonneg_left hsq (by positivity))

private theorem product_circuit {n b : ℕ} (A : List (Reg n))
    (h : ∀ x ∈ A, ∃ z : ℂ, ‖z‖ = 1 ∧ ∃ C : TwoQubitCircuit n,
      C.gateCount ≤ b ∧ x = z • (C.eval : Reg n)) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∃ C : TwoQubitCircuit n, C.gateCount ≤ A.length*b ∧
      A.prod = z • (C.eval : Reg n) := by
  induction A with
  | nil => exact ⟨1,norm_one,TwoQubitCircuit.one n,le_rfl,by simp [TwoQubitCircuit.one_eval]⟩
  | cons x A ih =>
    obtain ⟨u,hu,C,hC,he⟩ := h x List.mem_cons_self
    obtain ⟨v,hv,D,hD,hf⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    refine ⟨u*v,by simp [norm_mul,hu,hv],C.mul D,?_,?_⟩
    · rw [TwoQubitCircuit.mul_gateCount,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    simp only [List.prod_cons,he,hf,TwoQubitCircuit.mul_eval]
    change (u • (C.eval : Reg n)) * (v • (D.eval : Reg n)) = (u*v) • (_ * _)
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul]

/-- A product formula for a Hermitian generator on an arbitrary qubit
register, using two-site gates without ancillary qubits. -/
theorem exists_full_pauli_product_circuit {n : ℕ} (hn : 2 ≤ n) (K : selfAdjoint (Reg n))
    (r : ℕ) (hr : 0 < r) :
    HasProjectiveCircuitApproximation n ((4:ℝ)^n * ‖K.val‖^2 / r)
      (r*(4^n*(2*n+1))) (unitaryEvolution K.val 1) := by
  classical
  let X (P : Words n) : Reg n := (-Complex.I) • ((realPauliCoefficient K P : ℂ) • finitePauliMatrix P)
  let e := (Fintype.equivFin (Words n)).symm
  let Z := List.ofFn (fun i => X (e i))
  let h := (1:ℝ)/r
  have hsum : Z.sum = (-Complex.I) • K.val := by
    change (List.ofFn (fun i => X (e i))).sum = _
    rw [List.sum_ofFn,Equiv.sum_comp e X]
    unfold X
    rw [← Finset.smul_sum]
    congr 1
    simpa only [← pauliCoeff_eq_realPauliCoefficient] using sum_pauliCoeff_smul K.val
  have hmass : (Z.map norm).sum = ∑ P : Words n, |realPauliCoefficient K P| := by
    simp only [Z,List.map_ofFn,Function.comp_apply,List.sum_ofFn]
    rw [Equiv.sum_comp e (fun P => ‖X P‖)]
    simp [X,norm_smul,norm_finitePauliMatrix]
  have hmem (x) (hx : x ∈ Z) : ∃ P, x = X P := by
    rw [List.mem_ofFn] at hx
    obtain ⟨i,rfl⟩ := hx
    exact ⟨_,rfl⟩
  have hz x (hx : x ∈ Z) : x ∈ skewAdjoint (Reg n) := by
    obtain ⟨P,rfl⟩ := hmem x hx
    rw [skewAdjoint.mem_iff]
    change star ((-Complex.I) • ((_ : ℂ) • finitePauliMatrix P)) = _
    rw [star_smul,star_smul,show star (finitePauliMatrix P) = _ from (finitePauliMatrix_isHermitian P)]
    simp [X]
  let A := Z.map fun x => exp (h • x)
  have hgate y (hy : y ∈ A) : ∃ z : ℂ, ‖z‖ = 1 ∧ ∃ C : TwoQubitCircuit n,
      C.gateCount ≤ 2*n+1 ∧ y = z • (C.eval : Reg n) := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    obtain ⟨P,rfl⟩ := hmem x hx
    obtain ⟨z,hz,C,hC,hrot⟩ := exists_projective_pauli_rotation_circuit hn P (h*realPauliCoefficient K P)
    have hw : pauliWeight P ≤ n := (Finset.card_le_univ _).trans (by simp)
    refine ⟨z,hz,C,by omega,?_⟩
    rw [← hrot,unitaryEvolution]
    congr 1
    ext i j
    simp [X,Matrix.smul_apply]
    ring
  obtain ⟨z,hz',C,hC,he⟩ := product_circuit A hgate
  refine ⟨z^r,by simp [norm_pow,hz'],C.pow r,?_,?_⟩
  · rw [TwoQubitCircuit.pow_gateCount]
    apply Nat.mul_le_mul_left r
    simpa only [A,Z,List.length_map,List.length_ofFn,card_words] using hC
  have herr := list_lie_product_pow_mass_error Z hz 1 r hr
  change ‖A.prod^r - exp ((1:ℝ) • Z.sum)‖ ≤ _ at herr
  rw [he,smul_pow,hsum,hmass] at herr
  rw [TwoQubitCircuit.pow_eval_coe,norm_sub_rev]
  apply herr.trans
  simpa only [abs_one,one_pow,mul_one] using
    (div_le_div_of_nonneg_right (mass_sq_le K) (Nat.cast_nonneg r))

/-- Every time on every Hermitian orbit has a two-qubit circuit of cost at
most 160 (2n+1) 16ⁿ at projective operator error 1/10. -/
theorem evolution_uniform_projective_gate_cap {n : ℕ} (hn : 2 ≤ n) (H : selfAdjoint (Reg n)) (t : ℝ) :
    HasProjectiveCircuitApproximation n (1/10:ℝ) (160 * (2*n+1) * 16^n) (unitaryEvolution H.val t) := by
  obtain ⟨K,hK,hU⟩ := exists_bounded_unit_time_generator H t
  let r := 160*4^n
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨z,hz,C,hC,he⟩ := exists_full_pauli_product_circuit hn K r hr
  refine ⟨z,hz,C,?_,?_⟩
  · have h16 : (16:ℕ)^n = 4^n*4^n := by rw [← mul_pow]; rfl
    simpa only [r,h16,mul_assoc,mul_left_comm,mul_comm] using hC
  rw [← hU]
  apply he.trans
  apply (div_le_iff₀ (by exact_mod_cast hr : (0:ℝ)<r)).mpr
  have h2 := sq_le_sq' ((neg_nonpos.mpr (norm_nonneg _)).trans (by norm_num : (0:ℝ) ≤ 4))
    (hK.trans Real.pi_lt_four.le)
  push_cast [r]
  nlinarith only [mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ (4:ℝ)^n)]

#print axioms evolution_uniform_projective_gate_cap
end
end GaloisForLFunctions.HTGeometry
