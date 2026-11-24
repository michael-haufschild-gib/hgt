import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.PauliChain
import GaloisForLFunctions.HTGeometry.DecoupledEvolutionFactorization
import GaloisForLFunctions.RHTower.StaticChoiProjectiveCubicScalarReturnLaw

/-! # Exact onsite factorization of the trajectory at the rank witness -/
open Matrix
open scoped Kronecker Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

/-- The common one-spin field axis has unit length. -/
def tiltedAxis : Matrix Bool Bool ℂ := (3/5:ℂ) • finiteQubitPauli 2+(4/5:ℂ) • finiteQubitPauli 0

theorem tiltedAxis_square : tiltedAxis*tiltedAxis=1 := by
  ext i j
  cases i <;> cases j <;> norm_num [tiltedAxis,Matrix.mul_apply,Fintype.sum_bool,finiteQubitPauli,
    show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,Matrix.one_apply]

private theorem zero_bond_matrix (n : ℕ) (H : Register n) (b : ℕ) :
    onRegister n (physical H 0 ((3/5)*height b) ((4/5)*height b)) =
      reindex (snocConfig n) (snocConfig n) (kroneckerSum H (height b • tiltedAxis)) := by
  rw [onRegister_physical,map_zero,add_zero]
  ext i j
  simp only [lastPauli,coupleSnoc_apply,layerMatrixCoupling,boolPauliOption,
    Matrix.reindex_apply,Matrix.submatrix_apply,Matrix.add_apply,Matrix.smul_apply,
    smul_eq_mul,kroneckerSum,Matrix.kronecker_apply,tiltedAxis]
  ring

/-- Removing the last bond factors the evolution into the old register and a
single onsite rotation, at every real date. -/
theorem zero_bond_evolution (n : ℕ) (H : Register n) (b : ℕ) (t : ℝ) :
    unitaryEvolution (onRegister n (physical H 0 ((3/5)*height b) ((4/5)*height b))) t =
      coupleSnoc n (unitaryEvolution (height b • tiltedAxis) t) (unitaryEvolution H t) := by
  rw [zero_bond_matrix]
  have he := RHTower.unitaryEvolution_reindexAlgEquiv (snocConfig n)
    (kroneckerSum H (height b • tiltedAxis)) t
  rw [unitaryEvolution_kroneckerSum] at he
  exact he.symm

/-- Matrix entry of the complete trajectory is the product of the corresponding
entries of its independent single-spin rotations. -/
theorem product_evolution (n : ℕ) (B : Fin (n+1)→ℕ) (t : ℝ) (i j : Config (n+1)) :
    unitaryEvolution (background n B 0) t i j =
      ∏ s, unitaryEvolution (height (B s) • tiltedAxis) t (i s) (j s) := by
  induction n with
  | zero =>
    rw [background,zero_bond_evolution,Fin.prod_univ_one]
    simp [unitaryEvolution,coupleSnoc_apply,layerMatrixCoupling,snocConfig,Matrix.one_apply,
      Subsingleton.elim (fun l : Fin 0 => i l.castSucc) (fun l : Fin 0 => j l.castSucc)]
  | succ n ih =>
    simp only [background,map_zero,baseNext,Prod.fst_zero,Prod.snd_zero,zero_smul,
      zero_bond_evolution,coupleSnoc_apply,Matrix.reindex_apply,Matrix.submatrix_apply,layerMatrixCoupling]
    rw [Fin.prod_univ_castSucc,ih]
    rfl

#print axioms product_evolution
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
