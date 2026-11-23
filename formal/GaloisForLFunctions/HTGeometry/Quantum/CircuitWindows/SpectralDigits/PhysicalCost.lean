import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralDigits.Quantization
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.ShortWord
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.Boundary.SpectralAlgebra
import GaloisForLFunctions.HTGeometry.UnitaryL2OperatorNorm

/-! # A physical circuit lower bound for a specified spectral digit -/
open Matrix Finset Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralDigits
open FirstGate.Boundary ClockSpectrum
noncomputable section
variable {N : ℕ}
private abbrev I (N : ℕ) := Fin N → Bool
private abbrev Reg (N : ℕ) := Matrix (I N) (I N) ℂ

/-- A fixed rotation on the energy levels selected by one digit of the phase. -/
def digitMatrix (V : unitaryGroup (I N) ℂ) (x : I N → ℝ) (j : Fin 8) : Reg N :=
  spectralFunction V (fun i => expTurns (digitTurn j (x i)))

/-- Fitting all eight binary rotations gives a physical fit at error 1/10.
The digit budgets are charged separately, so the conclusion also tests
one specified collection of eight unequal budgets. -/
theorem compile_digits (V : unitaryGroup (I N) ℂ) (x : I N → ℝ)
    (hx : ∀ i, x i ∈ Icc (0:ℝ) 1) (b : Fin 8 → ℕ)
    (hf : ∀ j, HasProjectiveCircuitApproximation N (1/100) (b j) (digitMatrix V x j)) :
    HasProjectiveCircuitApproximation N (1/10) (∑ j, b j)
      (spectralFunction V (fun i => expTurns (x i))) := by
  let Φ := Unitary.conjStarAlgAut ℂ (Reg N) V
  let f (j : Fin 8) (i : I N) := expTurns (digitTurn j (x i))
  let F (s : Finset (Fin 8)) (i : I N) := ∏ j∈s, f j i
  let U (s : Finset (Fin 8)) := spectralFunction V (F s)
  have hunit (s) : U s ∈ unitary _ := by
    have hD := StaticLocalLaboratoryComplexityGrowthLaw.mem_unitaryGroup_diagonal_general (F s)
      (fun i => by simp only [F,norm_prod,f,norm_expTurns,prod_const_one])
    exact mul_mem (mul_mem V.property hD) (Unitary.star_mem V.property)
  have hfit (s : Finset (Fin 8)) : HasProjectiveCircuitApproximation N ((s.card:ℝ)/100)
      (∑ j∈s, b j) (U s) := by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨1,norm_one,TwoQubitCircuit.one N,by simp,?_⟩
      have he : U ∅=1 := by change Φ (diagonal _)=_; simp [F,Matrix.diagonal_one]
      simp [he,TwoQubitCircuit.one_eval]
    | @insert j s hj ih =>
      have he : U (insert j s)=digitMatrix V x j*U s := by
        change Φ (diagonal _)=Φ (diagonal _)*Φ (diagonal _)
        rw [←map_mul,diagonal_mul_diagonal]
        exact congrArg (fun g : I N → ℂ => Φ (diagonal g)) (funext fun i => prod_insert hj ..)
      rw [he,sum_insert hj,card_insert_of_notMem hj,Nat.cast_add,Nat.cast_one]
      convert LocalPatches.approx_product (hunit s) (hf j) ih using 1 <;> ring
  obtain ⟨z,hz,C,hC,herr⟩ := hfit univ
  let a := expTurns (1/512)
  have ha := norm_expTurns (1/512)
  let B := spectralFunction V (fun i => expTurns (x i))
  have hround : ‖B-a • U univ‖ ≤ Real.pi/256 := by
    change ‖Φ (diagonal _)-a • Φ (diagonal _)‖ ≤ _
    rw [←map_smul,←map_sub,Unitary.conjStarAlgAut_apply,l2_opNorm_unitary_conj_eq V.property,
      ←Matrix.diagonal_smul,Matrix.diagonal_sub,Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => phase_error (hx i)
  have hrot : ‖a • U univ-(a*z) • (C.eval : Reg N)‖ ≤ 8/100 := by
    rw [←smul_smul,←smul_sub,norm_smul,show ‖a‖=1 from ha,one_mul]
    simpa only [card_univ,Fintype.card_fin,Nat.cast_ofNat] using herr
  refine ⟨a*z,by rw [norm_mul,ha,hz,one_mul],C,hC,?_⟩
  have h := (norm_sub_le_norm_sub_add_norm_sub B (a • U univ) _).trans (add_le_add hround hrot)
  exact h.trans (by linarith only [Real.pi_lt_four])

/-- Above any physical budget, at least one of eight known two-valued
spectral unitaries exceeds one eighth of that budget at error 1/100. -/
theorem exists_hard_digit (V : unitaryGroup (I N) ℂ) (x : I N → ℝ)
    (hx : ∀ i, x i ∈ Icc (0:ℝ) 1) (s : ℕ)
    (h : ¬HasProjectiveCircuitApproximation N (1/10) s
      (spectralFunction V (fun i => expTurns (x i)))) :
    ∃ j : Fin 8, ¬HasProjectiveCircuitApproximation N (1/100) (s/8) (digitMatrix V x j) := by
  by_contra! hfit
  obtain ⟨z,hz,C,hC,he⟩ := compile_digits V x hx _ hfit
  have hs : C.gateCount ≤ 8*(s/8) := by simpa only [sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul] using hC
  exact h ⟨z,hz,C,hs.trans (Nat.mul_div_le ..),he⟩

#print axioms exists_hard_digit
end
end GaloisForLFunctions.HTGeometry.SpectralDigits
