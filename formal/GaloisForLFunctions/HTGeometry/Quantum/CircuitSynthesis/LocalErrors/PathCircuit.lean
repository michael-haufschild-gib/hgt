import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.Word
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.BlockCommutators

/-! # Nearest-neighbour Pauli simulation controlled by squared interaction mass -/
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ
local instance pathOverlapCStarAlgebra (N : ℕ) : CStarAlgebra (Reg N) where

open LocalPatches

/-- Each sweep uses one physical gate per path label. The squared coefficient
norm bounds the overlap error uniformly in the chain length. -/
theorem exists_path_circuit_squared_mass_error {n : ℕ} (u : PathShell n)
    (t : ℝ) (ht : 0 ≤ t) (r : ℕ) (hr : 0 < r) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit (n+2),
      C.gateCount = r*Fintype.card (PathLabel n) ∧
      ‖unitaryEvolution (pathHamiltonian u) t-c • (C.eval : Reg (n+2))‖ ≤
        t^2/(r:ℝ)*(84*‖u‖^2) := by
  classical
  let X := pathTermGenerator u
  let e := (Fintype.equivFin (PathLabel n)).symm
  let Z := List.ofFn (fun i => X (e i))
  have hmem (x) (hx : x ∈ Z) : ∃ l, x = X l := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact ⟨_,rfl⟩
  have hz x (hx : x ∈ Z) : x ∈ skewAdjoint (Reg (n+2)) := by
    obtain ⟨l,rfl⟩ := hmem x hx
    exact (pathTerm_properties u l).2.1
  have hs : Z.sum = (-Complex.I) • pathHamiltonian u := by
    change (List.ofFn (fun i => X (e i))).sum = _
    rw [List.sum_ofFn,Equiv.sum_comp e X,pathHamiltonian_eq_sum,Finset.smul_sum]
    rfl
  have hmap (f : Reg (n+2) → ℝ) : (Z.map f).sum = ∑ l : PathLabel n, f (X l) := by
    simp only [Z,List.map_ofFn,Function.comp_apply,List.sum_ofFn]
    exact Equiv.sum_comp e (fun l => f (X l))
  let h := t/(r:ℝ)
  obtain ⟨c,hc,C,hC,hprod⟩ := compile_path_word_steps Z h (by
    intro x hx
    obtain ⟨l,rfl⟩ := hmem x hx
    exact (pathTerm_properties u l).2.2 h)
  refine ⟨c^r,by simp [norm_pow,hc],C.pow r,by rw [TwoQubitCircuit.pow_gateCount,hC]; simp only [Z,List.length_ofFn],?_⟩
  have herr := lie_word_repeated_commutator_error Z hz t ht r hr
  change ‖(Z.map fun x => exp (h • x)).prod^r-exp (t • Z.sum)‖ ≤ _ at herr
  rw [hprod,smul_pow,hs] at herr
  simp_rw [hmap] at herr
  rw [TwoQubitCircuit.pow_eval_coe,norm_sub_rev]
  exact herr.trans (mul_le_mul_of_nonneg_left (LocalErrors.path_commutator_mass u) (by positivity))

#print axioms exists_path_circuit_squared_mass_error
end
end GaloisForLFunctions.HTGeometry

