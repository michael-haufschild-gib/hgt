import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.TangentCuts.CompressedEvolution
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.CutDeterminant
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage

/-! # Quadratic deviation of a survival amplitude from its diagonal phase -/

open Matrix Finset NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit.TangentCuts
open ProductInputs
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ
local instance columnAlgebra (N : ℕ) : CStarAlgebra (Reg N) where
variable {N : ℕ}

/-- Centering at the energy in a basis vector leaves one column whose
squared Hilbert–Schmidt norm equals the energy variance. -/
private theorem centered_column (H : selfAdjoint (Reg N)) (x : Fin N→Bool) (c : ℝ)
    (hc : H.val x x=c) :
    let X := (scalarCenteredHamiltonian H c).val
    ‖X*basisProjector x‖^2≤∑ y∈univ.erase x, ‖H.val y x‖^2 := by
  intro X
  apply (pow_le_pow_left₀ (norm_nonneg _) (l2_opNorm_le_hsNorm _) 2).trans_eq
  rw [hsNorm_sq,sum_comm]
  have hx : X x x=0 := by simp [X,scalarCenteredHamiltonian,Matrix.smul_apply,hc]
  have hy (y : Fin N→Bool) (hne : y≠x) : X y x=H.val y x := by
    simp [X,scalarCenteredHamiltonian,Matrix.smul_apply,Matrix.one_apply,hne]
  rw [sum_eq_single x]
  · simp only [basisProjector,Matrix.mul_diagonal,if_true,mul_one]
    rw [←sum_erase_add _ _ (mem_univ x),hx,norm_zero,zero_pow (by decide),add_zero]
    exact sum_congr rfl fun y hy' => by rw [hy y (ne_of_mem_erase hy')]
  · intro y _ hne
    simp only [basisProjector,Matrix.mul_diagonal,if_neg hne,mul_zero,norm_zero,zero_pow (by decide),sum_const_zero]
  · exact fun hn => (hn (mem_univ x)).elim

/-- The centered survival amplitude has zero linear term. Its distance
from the diagonal phase is bounded by time squared times the variance
of the energy in the chosen basis vector. -/
theorem diagonal_phase_quadratic (H : selfAdjoint (Reg N)) (x : Fin N→Bool) (c : ℝ)
    (hc : H.val x x=c) (t : ℝ) :
    ‖unitaryEvolution H.val t x x-phase t c‖≤t^2*(∑ y∈univ.erase x, ‖H.val y x‖^2) := by
  let X := (scalarCenteredHamiltonian H c).val
  let a := (-Complex.I) • X
  let P := basisProjector x
  have hX : IsSelfAdjoint X := (scalarCenteredHamiltonian H c).2
  have hP : IsSelfAdjoint P := by
    apply Matrix.isHermitian_iff_isSelfAdjoint.mp
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    funext i
    by_cases hi : i=x <;> simp [hi]
  have ha : a∈skewAdjoint (Reg N) := by
    rw [skewAdjoint.mem_iff]
    simp only [a,star_smul,hX.star_eq,star_neg,Complex.star_def,Complex.conj_I,neg_neg,neg_smul]
  have hx : a x x=0 := by simp [a,X,scalarCenteredHamiltonian,Matrix.smul_apply,hc]
  have hnorm : ‖P*a‖=‖a*P‖ := by
    rw [←norm_star (P*a),star_mul,(skewAdjoint.mem_iff.mp ha),hP.star_eq,neg_mul,norm_neg]
  have hvar := centered_column H x c hc
  have hgen : ‖a*P‖=‖X*P‖ := by rw [show a*P=(-Complex.I) • (X*P) from Matrix.smul_mul ..,norm_smul,norm_neg,Complex.norm_I,one_mul]
  let f := exp (t • a)
  have he := (norm_entry_le_l2_opNorm (P*f*P-P*P-t • (P*a*P)) x x).trans (compressed_remainder a P P ha t)
  rw [hnorm,hgen,←sq] at he
  simp only [P,basisProjector,Matrix.sub_apply,Matrix.smul_apply,Matrix.mul_diagonal,Matrix.diagonal_mul,
    Matrix.diagonal_apply_eq,ite_true,mul_one,one_mul,hx,smul_zero,sub_zero] at he
  rw [unitaryEvolution_eq_phase_smul_scalarCentered H c t]
  change ‖phase t c*f x x-phase t c‖≤_
  rw [←mul_sub_one,norm_mul,phase_norm,one_mul]
  apply he.trans
  exact mul_le_mul_of_nonneg_left hvar (sq_nonneg _)

/-- Uniform quadratic phase accuracy on every computational configuration
of the open Pauli chain. -/
theorem path_column_phase_quadratic {n : ℕ} (u : PathShell n) (x : Fin (n+2)→Bool) (t : ℝ) :
    ‖unitaryEvolution (pathHamiltonian u) t x x-phase t (pathDiagEnergy u x)‖≤t^2*(21*‖u‖^2) :=
  (diagonal_phase_quadratic ⟨_,isSelfAdjoint_pathHamiltonian u⟩ x _ (pathHamiltonian_diagonal_entry u x) t).trans
    (mul_le_mul_of_nonneg_left (column_variance u x) (sq_nonneg _))

#print axioms path_column_phase_quadratic
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit.TangentCuts
