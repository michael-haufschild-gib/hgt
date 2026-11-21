import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.Walsh
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliRotations
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Exact circuits for arbitrary diagonal phases on the original register -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis
noncomputable section
abbrev Register (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Exact two-qubit synthesis, up to one global phase. -/
def Realizes {n : ℕ} (P : ℕ) (U : Register n) : Prop :=
  ∃ z : ℂ, ‖z‖=1 ∧ ∃ C : TwoQubitCircuit n, C.gateCount ≤ P ∧ U=z • (C.eval : Register n)

theorem Realizes.one (n : ℕ) : Realizes 0 (1 : Register n) :=
  ⟨1,norm_one,TwoQubitCircuit.one n,le_rfl,by simp [TwoQubitCircuit.one_eval]⟩

theorem Realizes.mul {n P Q : ℕ} {U V : Register n} (hU : Realizes P U) (hV : Realizes Q V) :
    Realizes (P+Q) (U*V) := by
  obtain ⟨a,ha,C,hC,rfl⟩ := hU
  obtain ⟨b,hb,D,hD,rfl⟩ := hV
  refine ⟨a*b,by rw [norm_mul,ha,hb,mul_one],C.mul D,by rw [TwoQubitCircuit.mul_gateCount]; omega,?_⟩
  rw [TwoQubitCircuit.mul_eval]
  change _ = (a*b) • ((C.eval : Register n)*(D.eval : Register n))
  rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul]

theorem Realizes.adjoint {n P : ℕ} {U : Register n} (h : Realizes P U) : Realizes P (star U) := by
  obtain ⟨z,hz,C,hC,rfl⟩ := h
  refine ⟨star z,by simpa only [norm_star] using hz,C.adjoint,hC,?_⟩
  rw [star_smul,TwoQubitCircuit.adjoint_eval]
  rfl

theorem Realizes.approx {n P : ℕ} {U : Register n} (h : Realizes P U) {ε : ℝ} (hε : 0 ≤ ε) :
    HasProjectiveCircuitApproximation n ε P U := by
  obtain ⟨z,hz,C,hC,rfl⟩ := h
  exact ⟨z,hz,C,hC,by simpa only [sub_self,norm_zero] using hε⟩

/-- Each binary character contributes one commuting Pauli rotation. -/
theorem diagonal_angles {n : ℕ} (hn : 2 ≤ n) (f : (Fin n → Bool) → ℝ) :
    Realizes (2^n*(2*n+1)) (diagonal (fun x => Complex.exp (-Complex.I*(f x:ℂ)))) := by
  classical
  let A := Fin n → Bool
  let F (s : Finset A) (x : A) : ℝ := ∑ a ∈ s, coefficient f a * character a x
  let U (s : Finset A) : Register n := diagonal (fun x => Complex.exp (-Complex.I*(F s x:ℂ)))
  have hs (s : Finset A) : Realizes (s.card*(2*n+1)) (U s) := by
    induction s using Finset.induction_on with
    | empty => simpa [U,F] using Realizes.one n
    | @insert a s ha ih =>
      obtain ⟨z,hz,C,hC,he⟩ := exists_projective_pauli_rotation_circuit hn (zWord a) (coefficient f a)
      have hw : pauliWeight (zWord a) ≤ n := (Finset.card_le_univ _).trans (by simp)
      let V : Register n := unitaryEvolution (finitePauliMatrix (zWord a)) (coefficient f a)
      have hV : Realizes (2*n+1) V := ⟨z,hz,C,by omega,he⟩
      have hprod : U (insert a s) = V*U s := by
        dsimp only [V,U]
        rw [zWord_diagonal,unitaryEvolution_diagonal,diagonal_mul_diagonal]
        congr 1; funext x
        simp only [F,Finset.sum_insert ha,Complex.ofReal_add,Complex.ofReal_mul,← Complex.exp_add]
        congr 1; ring
      rw [hprod,Finset.card_insert_of_notMem ha,Nat.add_mul,Nat.one_mul,Nat.add_comm]
      exact hV.mul ih
  have hfu x : F Finset.univ x = f x := walsh_inversion f x
  simpa only [U,hfu,Finset.card_univ,A,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool] using hs Finset.univ

/-- Every computational-basis diagonal unitary has an exact projective
circuit with at most (2n+1)2^n gates. -/
theorem diagonal_phases {n : ℕ} (hn : 2 ≤ n) (v : (Fin n → Bool) → ℂ) (hv : ∀ x, ‖v x‖=1) :
    Realizes (2^n*(2*n+1)) (diagonal v) := by
  have he (x) : Complex.exp (-Complex.I*((-(v x).arg:ℝ):ℂ)) = v x := by
    have h := Complex.norm_mul_exp_arg_mul_I (v x)
    rw [hv,Complex.ofReal_one,one_mul] at h
    simpa [mul_comm] using h
  simpa only [he] using diagonal_angles hn (fun x => -(v x).arg)

#print axioms diagonal_phases
end
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis
