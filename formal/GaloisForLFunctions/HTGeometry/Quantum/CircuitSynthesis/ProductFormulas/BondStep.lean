import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.BondHamiltonians
import GaloisForLFunctions.HTGeometry.Quantum.CoefficientMassLieProduct

/-! # One physical gate per bond in a first-order path product -/
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BondProducts
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ
local instance (N : ℕ) : CStarAlgebra (Reg N) where

private theorem lifted_flow {n : ℕ} (e : Fin (n+1)) (B : selfAdjoint LocalMatrix) (t : ℝ) :
    ∃ z : ℂ, ‖z‖=1 ∧ ∃ C : TwoQubitCircuit (n+2), C.gateCount=1 ∧
      unitaryEvolution (twoQubitLiftMatrix e.castSucc e.succ (endpoints_ne e) B.val) t=z • C.eval.val := by
  let U : Matrix.unitaryGroup (Bool × Bool) ℂ := ⟨unitaryEvolution B.val t,unitaryEvolution_mem_unitary B.2 t⟩
  let a := scalarSpecialUnitaryPhase U
  let G := scalarSpecialUnitaryRepresentative U
  have hunit : star a*a=1 := scalarSpecialUnitaryPhase_unitary U
  have hnorm := congrArg norm hunit
  have hs : ‖a‖*‖a‖=1 := by simpa only [norm_mul,norm_star,norm_one] using hnorm
  have ha : ‖a‖=1 := by nlinarith only [hs,norm_nonneg a,sq_nonneg (‖a‖-1)]
  refine ⟨star a,by simpa only [norm_star] using ha,TwoQubitCircuit.singleOn _ _ (endpoints_ne e) G,rfl,?_⟩
  rw [TwoQubitCircuit.singleOn_eval,unitaryEvolution_twoQubitLiftMatrix]
  have hg : (twoQubitLift e.castSucc e.succ (endpoints_ne e) G).val =
      a • twoQubitLiftMatrix e.castSucc e.succ (endpoints_ne e) U.val := by
    change twoQubitLiftMatrix _ _ _ (G:LocalMatrix)=_
    rw [scalarSpecialUnitaryRepresentative_coe,twoQubitLiftMatrix_smul]
  rw [hg,smul_smul,hunit,one_smul]

/-- One first-order step costs exactly N−1 arbitrary two-qubit gates.
For a fixed Hamiltonian the operator error is at most A·t² at every
signed lag t. Each four-dimensional bond Hamiltonian evolves exactly. -/
theorem exists_bond_step {n : ℕ} (u : PathShell n) :
    ∃ A : ℝ, 0≤A ∧ ∀ t : ℝ, ∃ z : ℂ, ‖z‖=1 ∧ ∃ C : TwoQubitCircuit (n+2),
      C.gateCount=n+1 ∧ ‖unitaryEvolution (pathHamiltonian u) t-z • C.eval.val‖ ≤ A*t^2 := by
  obtain ⟨B,hsum⟩ := exists_bond_hamiltonians u
  let F (e : Fin (n+1)) := twoQubitLiftMatrix e.castSucc e.succ (endpoints_ne e) (B e).val
  let X (e : Fin (n+1)) := (-Complex.I) • F e
  let Z := List.ofFn X
  have he (e : Fin (n+1)) : IsSelfAdjoint (F e) := by
    apply Matrix.isHermitian_iff_isSelfAdjoint.mp
    exact ((B e).2.isHermitian.kronecker isHermitian_one).reindex _
  have hsk (x) (hx : x∈Z) : x∈skewAdjoint (Reg (n+2)) := by
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hx
    rw [skewAdjoint.mem_iff]
    simp only [X,star_smul,(he e).star_eq,star_neg,Complex.star_def,Complex.conj_I,neg_neg,neg_smul]
  have hZ : Z.sum=(-Complex.I) • pathHamiltonian u := by
    rw [hsum,Finset.smul_sum]
    exact List.sum_ofFn X
  refine ⟨(Z.map norm).sum^2,sq_nonneg _,?_⟩
  intro t
  obtain ⟨z,hz,C,hcount,hword⟩ := compile_path_word_steps Z t (fun x hx => by
    obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hx
    exact lifted_flow e (B e) t)
  have hh := list_lie_product_mass_error Z hsk t
  rw [hword,hZ,sq_abs] at hh
  exact ⟨z,hz,C,by simpa only [Z,List.length_ofFn] using hcount,(norm_sub_rev _ _).le.trans hh⟩

#print axioms exists_bond_step
end
end GaloisForLFunctions.HTGeometry.BondProducts
