import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.NonAbelianClawOnset
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Block

/-! # Orthogonal action of a common spin rotation on Gaussian chain coefficients -/
open Matrix Set MeasureTheory ProbabilityTheory
open scoped Kronecker
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.FreeAxis
open AccuracyScales.TenthPlateau
noncomputable section

/-- One copy of the rotation on each onsite field and its tensor square on each bond. -/
def rotateLabels (R : Matrix (Fin 3) (Fin 3) ℝ) (n : ℕ) (x : PathLabel n→ℝ) : PathLabel n→ℝ
  | .inl (i,a) => ∑ j, R a j*x (.inl (i,j))
  | .inr (e,a,b) => ∑ j, ∑ k, R a j*R b k*x (.inr (e,j,k))

private def labelMatrix (R : Matrix (Fin 3) (Fin 3) ℝ) (n : ℕ) : Matrix (PathLabel n) (PathLabel n) ℝ :=
  fromBlocks ((1 : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) ⊗ₖ R) 0 0
    ((1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) ⊗ₖ (R ⊗ₖ R))

private theorem fiber_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (A : Matrix κ κ ℝ) (x : ι×κ→ℝ) (s : ι) (i : κ) :
    (((1 : Matrix ι ι ℝ) ⊗ₖ A) *ᵥ x) (s,i) = ∑ j, A i j*x (s,j) := by
  classical
  change (∑ k : ι×κ, ((1 : Matrix ι ι ℝ) ⊗ₖ A) (s,i) k * x k) = _
  rw [Fintype.sum_prod_type,Finset.sum_eq_single s]
  · simp only [kronecker_apply,Matrix.one_apply_eq,one_mul]
  · intro t _ ht
    simp only [kronecker_apply,Matrix.one_apply_ne ht.symm,zero_mul,Finset.sum_const_zero]
  · simp

private theorem rotateLabels_eq_matrix (R : Matrix (Fin 3) (Fin 3) ℝ) (n : ℕ) (x : PathLabel n→ℝ) :
    rotateLabels R n x=labelMatrix R n *ᵥ x := by
  rw [labelMatrix,fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec,zero_add,add_zero]
  funext l
  rcases l with ⟨i,a⟩|⟨e,a,b⟩
  · simp only [Sum.elim_inl,fiber_mul,Function.comp_apply,rotateLabels]
  · simp only [Sum.elim_inr,fiber_mul,Fintype.sum_prod_type,kronecker_apply,Function.comp_apply,rotateLabels]

private theorem labelMatrix_orthogonal (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : Rᵀ*R=1) (n : ℕ) :
    (labelMatrix R n)ᵀ*labelMatrix R n=1 := by
  simp only [labelMatrix,fromBlocks_transpose,Matrix.transpose_zero,←kroneckerMap_transpose,
    Matrix.transpose_one,fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,zero_add,add_zero,
    ←mul_kronecker_mul,hR,mul_one,one_kronecker_one,fromBlocks_one]

/-- Rotations transport any measurable Gaussian box to an equally likely
measurable event. Every point of that event has a preimage in the box. -/
theorem rotate_event (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : Rᵀ*R=1) {n : ℕ}
    (E : Set (PathLabel n→ℝ)) (hE : MeasurableSet E) :
    let μ := Measure.pi fun _ : PathLabel n => gaussianReal 0 1
    ∃ F : Set (PathLabel n→ℝ), MeasurableSet F ∧ μ.real F=μ.real E ∧
      ∀ x∈F, ∃ y∈E, rotateLabels R n y=x := by
  intro μ
  let M := labelMatrix R n
  have hl : Mᵀ*M=1 := labelMatrix_orthogonal R hR n
  have hr : M*Mᵀ=1 := mul_eq_one_comm.mp hl
  have hi := measurePreserving_pi_gaussian_orthogonal Mᵀ (by simpa only [transpose_transpose] using hr)
    (by simpa only [transpose_transpose] using hl)
  let F := (fun x => Mᵀ *ᵥ x) ⁻¹' E
  refine ⟨F,hE.preimage hi.measurable,hi.measureReal_preimage hE.nullMeasurableSet,?_⟩
  intro x hx
  refine ⟨Mᵀ *ᵥ x,hx,?_⟩
  rw [rotateLabels_eq_matrix]
  change M *ᵥ Mᵀ *ᵥ x=x
  rw [mulVec_mulVec,hr,one_mulVec]

#print axioms rotate_event
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.FreeAxis
