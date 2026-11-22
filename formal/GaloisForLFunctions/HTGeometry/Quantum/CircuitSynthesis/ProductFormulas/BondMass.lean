import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.BondCoordinates
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.BlockCommutators
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.Word
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.RepeatedSteps

/-! # Squared coefficient mass controls one gate per physical bond per sweep -/
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BondProducts
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ
local instance (N : ℕ) : CStarAlgebra (Reg N) where
open BondCoordinates LocalPatches

/-- With r full bond sweeps, a chain with n+2 sites costs r(n+1) gates
and has error at most 84t²‖u‖²/r. The constant is independent of length. -/
theorem bond_sweep_error {n : ℕ} (u : PathShell n) (t : ℝ) (ht : 0≤t) (r : ℕ) (hr : 0<r) :
    ∃ z : ℂ, ‖z‖=1 ∧ ∃ C : TwoQubitCircuit (n+2), C.gateCount=r*(n+1) ∧
      ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖ ≤ t^2/(r:ℝ)*(84*‖u‖^2) := by
  classical
  obtain ⟨B,hB⟩ := exists_local_blocks u
  let F (e : Fin (n+1)) := twoQubitLiftMatrix e.castSucc e.succ (BondCoordinates.endpoints_ne e) (B e).val
  let X (e : Fin (n+1)) := (-Complex.I) • F e
  let Z := List.ofFn X
  have hblock (e : Fin (n+1)) : X e=∑ l ∈ Finset.univ.filter (fun l => termBond l=e), pathTermGenerator u l := by
    dsimp only [X,F]
    rw [hB,← Finset.sum_filter,Finset.smul_sum]
    rfl
  have hsk (x) (hx : x∈Z) : x∈skewAdjoint (Reg (n+2)) := by
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hx
    rw [hblock]
    exact (skewAdjoint _).sum_mem fun l _ => (pathTerm_properties u l).2.1
  have hZ : Z.sum=(-Complex.I) • pathHamiltonian u := by
    change (List.ofFn X).sum=_
    rw [List.sum_ofFn,pathHamiltonian_eq_sum,Finset.smul_sum]
    simp only [hblock,Finset.sum_filter]
    rw [Finset.sum_comm]
    simp [pathTermGenerator]
  have hmass : (∑ e, ∑ f, ‖X e*X f-X f*X e‖) ≤ 84*‖u‖^2 := by
    simp only [hblock]
    exact (LocalErrors.block_commutator_mass termBond (pathTermGenerator u)).trans
      (LocalErrors.path_commutator_mass u)
  let h := t/(r:ℝ)
  obtain ⟨z,hz,C,hC,hprod⟩ := compile_path_word_steps Z h (by
    intro x hx
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hx
    exact BondCoordinates.lifted_flow e (B e) h)
  refine ⟨z^r,by simp [norm_pow,hz],C.pow r,by rw [TwoQubitCircuit.pow_gateCount,hC,List.length_ofFn],?_⟩
  have herr := lie_word_repeated_commutator_error Z hsk t ht r hr
  change ‖(Z.map fun x => exp (h • x)).prod^r-exp (t • Z.sum)‖ ≤ _ at herr
  rw [hprod,smul_pow,hZ] at herr
  simp only [Z,List.map_ofFn,Function.comp_apply,List.sum_ofFn] at herr
  rw [TwoQubitCircuit.pow_eval_coe,norm_sub_rev]
  exact herr.trans (mul_le_mul_of_nonneg_left hmass (by positivity))

#print axioms bond_sweep_error
end
end GaloisForLFunctions.HTGeometry.BondProducts
