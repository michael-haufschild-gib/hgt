import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.ProductInputs.LocalVariance
import GaloisForLFunctions.HTGeometry.TwoReplicaGlobalCliffordHallSymmetryReduction

/-! # Energy variance is uniformly small in every product basis -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.ProductInputs
noncomputable section
abbrev Bits (N : ℕ) := Fin N→Bool
abbrev Reg (N : ℕ) := Matrix (Bits N) (Bits N) ℂ

/-- The product of arbitrary one-qubit changes of basis. Its columns
range over all pure product inputs. -/
def basisUnitary {N : ℕ} (B : Fin N→Matrix.unitaryGroup Bool ℂ) : Matrix.unitaryGroup (Bits N) ℂ := by
  refine ⟨finiteLocalMatrix (fun v => (B v).val),?_⟩
  rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose,finiteLocalMatrix_conjTranspose,finiteLocalMatrix_mul]
  have h (i : Fin N) : (B i).val*(B i).valᴴ=1 := (Unitary.mem_iff.mp (B i).2).2
  simp only [h,finiteLocalMatrix_one]

/-- Uniformly over all product inputs, the energy variance is bounded
by a constant times the coefficient mass squared. -/
theorem product_basis_variance {n : ℕ} (u : PathShell n)
    (B : Fin (n+2)→Matrix.unitaryGroup Bool ℂ) (x : Bits (n+2)) :
    let V := (basisUnitary B).val
    (∑ y ∈ Finset.univ.erase x, ‖(star V*pathHamiltonian u*V) y x‖^2) ≤ 21*‖u‖^2 := by
  intro V
  let P (l : PathLabel n) := star V*finitePauliMatrix (pathWord l)*V
  have hv : V∈unitary (Reg (n+2)) := (basisUnitary B).2
  have hP (l : PathLabel n) : ‖P l‖=1 := by
    simp only [P,CStarRing.norm_mul_mem_unitary _ hv,
      CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem hv)]
    exact CStarRing.norm_of_mem_unitary (finitePauliMatrix_mem_unitary _)
  have hoff (l : PathLabel n) (v : Fin (n+2)) (hi : ¬pathIncident v l)
      (y x : Bits (n+2)) (h : y v≠x v) : P l y x=0 := by
    change ((finiteLocalMatrix fun i => (B i).val)ᴴ * finitePauliMatrix (pathWord l) *
      finiteLocalMatrix (fun i => (B i).val)) y x=0
    rw [finiteLocalMatrix_conjTranspose,finitePauliMatrix_eq_finiteLocalMatrix,
      finiteLocalMatrix_mul,finiteLocalMatrix_mul]
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    change ((B v).valᴴ*boolPauliOption (pathWord l v)*(B v).val) (y v) (x v)=0
    rw [pathWord_none_of_not_incidentSite v l hi]
    rw [show boolPauliOption none=(1 : Matrix Bool Bool ℂ) from rfl,mul_one,
      show (B v).valᴴ*(B v).val=1 from (Unitary.mem_iff.mp (B v).2).1,Matrix.one_apply_ne h]
  apply local_column_variance u P hP hoff
  rw [pathHamiltonian_eq_sum,Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by rw [Matrix.mul_smul,Matrix.smul_mul]

#print axioms product_basis_variance
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.ProductInputs
