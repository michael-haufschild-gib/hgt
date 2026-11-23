import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.BitMix
import GaloisForLFunctions.HTGeometry.HaferkampEntrywiseLiftDerivative

/-! # Local phase gates for binary register angles -/
open Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralSorting
noncomputable section
open DiagonalSynthesis

/-- Every unitary on a specified pair of wires is one physical gate up
to its determinant phase. -/
theorem realizes_pair {n : ℕ} (i j : Fin n) (hij : i≠j) (U : Matrix.unitaryGroup (Bool×Bool) ℂ) :
    Realizes 1 (twoQubitLiftMatrix i j hij U.val) := by
  let G := scalarSpecialUnitaryRepresentative U
  let z := scalarSpecialUnitaryPhase U
  have hz : star z*z=1 := scalarSpecialUnitaryPhase_unitary U
  have hs : ‖z‖*‖z‖=1 := by simpa only [norm_mul,norm_star,norm_one] using congrArg norm hz
  have hnorm : ‖z‖=1 := by nlinarith only [hs,norm_nonneg z,sq_nonneg (‖z‖-1)]
  refine ⟨star z,by simpa only [norm_star] using hnorm,TwoQubitCircuit.singleOn i j hij G,le_rfl,?_⟩
  rw [TwoQubitCircuit.singleOn_eval]
  change _=star z • twoQubitLiftMatrix i j hij (G:Matrix (Bool×Bool) (Bool×Bool) ℂ)
  rw [scalarSpecialUnitaryRepresentative_coe,twoQubitLiftMatrix_smul,smul_smul,hz,one_smul]

theorem realizes_pair_phase {n : ℕ} (i j : Fin n) (hij : i≠j) (f : Bool×Bool→ℂ) (hf : ∀ x, ‖f x‖=1) :
    Realizes 1 (diagonal (fun x : Fin n→Bool => f (x i,x j))) := by
  have hunit : diagonal f∈Matrix.unitaryGroup (Bool×Bool) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose,Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal,←Matrix.diagonal_one]
    congr 1
    funext y
    change f y*(star (f y))=1
    simp only [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,hf,one_pow,Complex.ofReal_one]
  let U : Matrix.unitaryGroup (Bool×Bool) ℂ := ⟨diagonal f,hunit⟩
  have h := realizes_pair i j hij U
  let e := splitTwoQubitConfig i j hij
  let R := {k : Fin n // k≠i ∧ k≠j}→Bool
  have he : twoQubitLiftMatrix i j hij U.val=diagonal (fun x : Fin n→Bool => f (x i,x j)) := by
    change (Matrix.kronecker (diagonal f) (1 : Matrix R R ℂ)).submatrix e e=_
    rw [←Matrix.diagonal_one,Matrix.kronecker,Matrix.diagonal_kronecker_diagonal,Matrix.submatrix_diagonal_equiv]
    congr 1
    funext x
    exact mul_one _
  exact he ▸ h

theorem realizes_single_phase {n : ℕ} (hn : 2 ≤ n) (i : Fin n) (f : Bool→ℂ) (hf : ∀ b, ‖f b‖=1) :
    Realizes 1 (diagonal (fun x : Fin n→Bool => f (x i))) := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j,hj⟩ := exists_ne i
  exact realizes_pair_phase i j hj.symm (fun p => f p.1) (fun p => hf p.1)

/-- Independent diagonal factors need one gate each, even when they
share wires. -/
theorem realizes_phase_product {n : ℕ} {I : Type*} (S : Finset I) (f : I→(Fin n→Bool)→ℂ)
    (hf : ∀ i∈S, Realizes 1 (diagonal (f i))) :
    Realizes S.card (diagonal (fun x => ∏ j∈S, f j x)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.card_empty,Finset.prod_empty,Matrix.diagonal_one] using Realizes.one n
  | @insert i S hi ih =>
    have hcomp := (hf i (Finset.mem_insert_self ..)).mul (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    rw [Matrix.diagonal_mul_diagonal] at hcomp
    simpa only [Finset.card_insert_of_notMem hi,Finset.prod_insert hi,Nat.add_comm 1] using hcomp

#print axioms realizes_pair_phase
end
end GaloisForLFunctions.HTGeometry.SpectralSorting
