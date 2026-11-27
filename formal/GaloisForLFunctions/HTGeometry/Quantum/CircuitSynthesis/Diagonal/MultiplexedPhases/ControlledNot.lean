import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.PhaseCircuit
import GaloisForLFunctions.HTGeometry.HaferkampTwoQubitCliffordSeeds
import Mathlib.Logic.Function.DependsOn

/-! # Controlled signs on a diagonal rotation -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis.MultiplexedPhases
noncomputable section
variable {n : ℕ}
abbrev Config (n : ℕ) := Fin n → Bool

/-- The real eigenvalue of one computational-basis Pauli Z. -/
def spin (b : Bool) : ℝ := if b then -1 else 1

/-- Diagonal evolution with the specified real angle at each configuration. -/
def phases (f : Config n → ℝ) : Register n :=
  diagonal fun x => Complex.exp (-Complex.I*(f x:ℂ))

theorem phases_add (f h : Config n → ℝ) :
    phases (fun x => f x+h x)=phases f*phases h := by
  rw [phases,phases,phases,diagonal_mul_diagonal]
  congr 1; funext x
  simp only [Complex.ofReal_add,mul_add,Complex.exp_add]

open private rotate_short_word from GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliRotations

/-- A rotation with no controls takes one physical gate. -/
theorem onsite (hn : 2 ≤ n) (p : Fin n) (t : ℝ) :
    Realizes 1 (phases fun x => spin (x p)*t) := by
  have hD : finitePauliMatrix (pauliZLabel p)=diagonal (fun x : Config n => (spin (x p):ℂ)) := by
    ext x y
    rw [finitePauliMatrix_pauliZLabel,diagonal_apply]
    by_cases h : x=y
    · subst y
      cases x p <;> simp [spin,zSign]
    · simp [h]
  have h := rotate_short_word hn (pauliZLabel p) (by rw [pauliWeight_pauliZLabel]; decide) t
  rw [hD,unitaryEvolution_diagonal] at h
  simpa only [Realizes,phases,Complex.ofReal_mul,neg_mul,mul_comm (t:ℂ)] using h

private def controlGate (j p : Fin n) (hjp : j≠p) :=
  TwoQubitCircuit.singleOn j p hjp boolTwoQubitCNOTSpecial

/-- On nonzero entries the control and the spectators agree; the
target spin acquires exactly the sign of the control. -/
private theorem control_entry {j p : Fin n} (hjp : j≠p) (x y : Config n)
    (hne : ((controlGate j p hjp).eval : Register n) x y≠0) :
    (∀ i, i≠p → x i=y i) ∧ spin (y p)=spin (x j)*spin (x p) := by
  rw [controlGate,TwoQubitCircuit.singleOn_eval] at hne
  let R := {k : Fin n // k≠j ∧ k≠p}
  let X : R→Bool := fun i => x i.1
  let Y : R→Bool := fun i => y i.1
  change (boolTwoQubitCNOTSpecial : Matrix (Bool × Bool) (Bool × Bool) ℂ) (x j,x p) (y j,y p) *
    (1 : Matrix (R→Bool) (R→Bool) ℂ) X Y ≠ 0 at hne
  have hlocal := left_ne_zero_of_mul hne
  have hrest := right_ne_zero_of_mul hne
  have hxy : X=Y := by
    by_contra h
    exact hrest (one_apply_ne h)
  change (scalarSpecialUnitaryRepresentative boolTwoQubitCNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ) _ _ ≠ 0 at hlocal
  rw [scalarSpecialUnitaryRepresentative_coe,Matrix.smul_apply] at hlocal
  have hbits : x j=y j ∧ x p=Bool.xor (y j) (y p) := by
    by_contra h
    exact hlocal (by simp [boolTwoQubitCNOT,boolTwoQubitCNOTMatrix,h])
  refine ⟨fun i hip => ?_,?_⟩
  · by_cases hij : i=j
    · simpa only [hij] using hbits.1
    · exact congrFun hxy ⟨i,hij,hip⟩
  · rw [hbits.1,hbits.2]
    cases y j <;> cases y p <;> norm_num [spin,Bool.xor]

/-- A CNOT and its adjoint multiply a target rotation's angle by the
control sign whenever the angle is independent of the target. -/
theorem control_sign {j p : Fin n} (hjp : j≠p) {S : Finset (Fin n)} (hp : p∉S)
    {f : Config n → ℝ} (hf : DependsOn f (S:Set (Fin n))) {P : ℕ}
    (h : Realizes P (phases fun x => spin (x p)*f x)) :
    Realizes (1+P+1) (phases fun x => spin (x p)*(spin (x j)*f x)) := by
  let C := controlGate j p hjp
  let L : Register n := C.eval
  let A := phases fun x => spin (x p)*f x
  let B := phases fun x => spin (x p)*(spin (x j)*f x)
  have hL : Realizes 1 L := ⟨1,norm_one,C,le_rfl,by rw [one_smul]⟩
  have hi : L*A=B*L := by
    ext x y
    dsimp only [A,B,phases]
    rw [mul_diagonal,diagonal_mul]
    by_cases hxy : L x y=0
    · rw [hxy,zero_mul,mul_zero]
    obtain ⟨hoff,hspin⟩ := control_entry hjp x y hxy
    have he : f x=f y := hf (fun i hi => hoff i (fun eq => hp (eq ▸ hi)))
    rw [show spin (y p)*f y=spin (x p)*(spin (x j)*f x) by rw [hspin,he]; ring,mul_comm]
  have hu : L*star L=1 := (Unitary.mem_iff.mp C.eval.2).2
  have hid : L*A*star L=B := by rw [hi,mul_assoc,hu,mul_one]
  change Realizes (1+P+1) B
  rw [←hid]
  exact (hL.mul h).mul hL.adjoint

#print axioms control_sign
end
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis.MultiplexedPhases
