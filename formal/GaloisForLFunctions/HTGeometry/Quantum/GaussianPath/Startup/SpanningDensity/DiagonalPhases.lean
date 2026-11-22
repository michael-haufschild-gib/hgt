import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.ColumnVariance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.ProductInputs.ProjectorTransport
import GaloisForLFunctions.HTGeometry.Quantum.PathPauliSpectralWidth

/-! # Survival amplitude and the classical diagonal energy before dephasing -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity
noncomputable section

/-- The diagonal propagator captures each survival amplitude up to elapsed
time times the energy standard deviation of that basis vector. -/
theorem diagonal_phase_residual {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]
    (H : Matrix d d ℂ) (hH : IsSelfAdjoint H) (E : d→ℝ) (x : d) (hx : H x x=E x) (t : ℝ) :
    ‖unitaryEvolution H t x x-Complex.exp ((-(t*E x):ℝ)*Complex.I)‖ ≤
      |t| * Real.sqrt (∑ y ∈ Finset.univ.erase x, ‖H y x‖^2) := by
  let P := ProductInputs.basisProjector x
  let K : Matrix d d ℂ := diagonal fun i => (E i:ℂ)
  have hentry := (norm_entry_le_l2_opNorm (unitaryEvolution H t*P-P*unitaryEvolution K t) x x).trans
    (ProductInputs.projector_residual H hH E x hx t)
  simpa only [P,ProductInputs.basisProjector,K,unitaryEvolution_diagonal_phase,Matrix.sub_apply,mul_diagonal,diagonal_mul,
    diagonal_apply_eq,ite_true,mul_one,one_mul] using hentry

/-- Uniform, deterministic column-phase error for a nearest-neighbor
Pauli Hamiltonian. The diagonal energies may be extensive. -/
theorem path_diagonal_phase {n : ℕ} (u : PathShell n) (x : Fin (n+2)→Bool) (t : ℝ) :
    ‖unitaryEvolution (pathHamiltonian u) t x x-Complex.exp ((-(t*pathDiagEnergy u x):ℝ)*Complex.I)‖ ≤
      |t| *(Real.sqrt 21*‖u‖) := by
  apply (diagonal_phase_residual _ (isSelfAdjoint_pathHamiltonian u) (pathDiagEnergy u)
    x (pathHamiltonian_diagonal_entry u x) t).trans
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  simpa only [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 21),Real.sqrt_sq (norm_nonneg u)] using
    Real.sqrt_le_sqrt (column_variance u x)

#print axioms path_diagonal_phase
end
end GaloisForLFunctions.HTGeometry.SpanningDensity
