import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.MultiplexedPhases.StatePreparation
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.Eigenphases

/-! # Gate budgets for one eigenline and a complete fixed eigenbasis -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis.MultiplexedPhases
open private origin isolated_row from GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.Eigenphases
noncomputable section

/-- An exact phase rotation about one column of an arbitrary eigenbasis uses at most 35·2ⁿ gates. -/
theorem linear_eigenline_phase {n : ℕ} (hn : 2 ≤ n) (V : Matrix.unitaryGroup (Config n) ℂ)
    (i : Config n) (z : ℂ) (hz : ‖z‖=1) :
    Realizes (35*2^n) ((V : Register n)*diagonal (pointPhase i z)*star (V : Register n)) := by
  let v (x : Config n) := (V : Register n) x i
  obtain ⟨C,hC,hcol⟩ := prepare_to_origin hn v
  let Q : Register n := C.eval
  let R : Register n := Q*(V : Register n)
  let D₀ := diagonal (pointPhase (origin n) z)
  let D := diagonal (pointPhase i z)
  have hQ : star Q*Q=1 := (Unitary.mem_iff.mp C.eval.2).1
  have hV : (V : Register n)*star (V : Register n)=1 := (Unitary.mem_iff.mp V.2).2
  have hr (x) (hx : x≠origin n) : R x i=0 := hcol x hx
  have hr' {j : Config n} (hj : j ≠ i) : R (origin n) j=0 :=
    isolated_row R (mul_mem C.eval.2 V.2) (origin n) i hr hj
  have hcomm : D₀*R=R*D := by
    ext x y
    simp only [D₀,D,diagonal_mul,mul_diagonal,pointPhase]
    by_cases hx : x=origin n <;> by_cases hy : y=i
    · simp [hx,hy,mul_comm]
    · simp [hx,hy,hr' hy]
    · simp [hx,hy,hr _ hx]
    · simp [hx,hy]
  have hchange : star Q*D₀*Q = (V : Register n)*D*star (V : Register n) := by
    calc
      _ = (star Q*(D₀*R))*star (V : Register n) := by
        simp only [R,mul_assoc,hV,mul_one]
      _ = _ := by rw [hcomm]; simp only [R,← mul_assoc,hQ,one_mul]
  have hcost : Realizes (16*2^n) Q := ⟨1,norm_one,C,hC,by simp [Q]⟩
  have hphase := full_register_phases hn (pointPhase (origin n) z) (fun x => by
    by_cases hh : x=origin n <;> simp [pointPhase,hh,hz])
  change Realizes _ ((V : Register n)*D*star (V : Register n))
  rw [← hchange]
  convert (hcost.adjoint.mul hphase).mul hcost using 1
  omega

/-- Synthesize an arbitrary diagonal in an arbitrary fixed eigenbasis by
applying one phase to each of its eigenlines. -/
theorem quadratic_eigenbasis_phases {n : ℕ} (hn : 2 ≤ n) (V : Matrix.unitaryGroup (Config n) ℂ)
    (p : Config n → ℂ) (hp : ∀ x, ‖p x‖=1) :
    Realizes (35*(2^n)^2) ((V : Register n)*diagonal p*star (V : Register n)) := by
  classical
  let f (s : Finset (Config n)) (x : Config n) := if x∈s then p x else 1
  let U (s : Finset (Config n)) := (V : Register n)*diagonal (f s)*star (V : Register n)
  have hV := Unitary.mem_iff.mp V.2
  have hconj (B C : Register n) :
      ((V : Register n)*B*star (V : Register n))*((V : Register n)*C*star (V : Register n)) =
      (V : Register n)*(B*C)*star (V : Register n) := by
    calc
      _ = (V : Register n)*B*(star (V : Register n)*(V : Register n))*C*star (V : Register n) := by
        simp only [mul_assoc]
      _ = _ := by rw [hV.1,mul_one]; simp only [mul_assoc]
  have h (s : Finset (Config n)) : Realizes (s.card*(35*2^n)) (U s) := by
    induction s using Finset.induction_on with
    | empty => simpa [U,f,hV.2] using Realizes.one n
    | @insert i s hi ih =>
      let D := diagonal (pointPhase i (p i))
      have hf : diagonal (f (insert i s))=D*diagonal (f s) := by
        rw [diagonal_mul_diagonal]
        congr 1; funext x
        by_cases hx : x=i
        · subst x; simp [pointPhase,f,hi]
        · simp [pointPhase,f,hx]
      have he : U (insert i s)=((V : Register n)*D*star (V : Register n))*U s := by
        simp only [U,hf,hconj]
      rw [he,Finset.card_insert_of_notMem hi,Nat.add_mul,Nat.one_mul,Nat.add_comm]
      exact (linear_eigenline_phase hn V i (p i) (hp i)).mul ih
  obtain ⟨z,hz,C,hC,he⟩ := h Finset.univ
  refine ⟨z,hz,C,?_,by simpa [U,f] using he⟩
  simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at hC
  apply hC.trans
  exact le_of_eq (by ring)

/-- At every time, every Hermitian evolution on n qubits has an exact
ancilla-free projective circuit of size at most 35·4ⁿ. -/
theorem quadratic_evolution_gate_cap {n : ℕ} (hn : 2 ≤ n) (H : selfAdjoint (Register n)) (t : ℝ) :
    Realizes (35*(2^n)^2) (unitaryEvolution H.val t) := by
  rw [unitaryEvolution_spectral H.2.isHermitian]
  apply quadratic_eigenbasis_phases hn _ _
  intro x
  simp [Complex.norm_exp]

#print axioms linear_eigenline_phase
#print axioms quadratic_evolution_gate_cap
end
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis.MultiplexedPhases
