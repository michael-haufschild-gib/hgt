import GaloisForLFunctions.HilbertMetric.QuantumInformation.SandwichedVariance
import GaloisForLFunctions.QuantumAlg.Util.HilbertSchmidt

/-!
# The commutator trace form of skew information

The population-coordinate variance deficit is half the squared
Hilbert--Schmidt norm of the commutator with the square-root state.
This identifies the scalar sum with the matrix inner product.
-/

open scoped BigOperators NNReal
namespace GaloisForLFunctions.HilbertMetric.QuantumInformation
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Commutator of a transition matrix with the square-root diagonal state. -/
def rootStateCommutator (p : ι → ℝ≥0) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => (Real.sqrt (p i) : ℂ)) * A -
    A * Matrix.diagonal (fun i => (Real.sqrt (p i) : ℂ))

theorem rootStateCommutator_apply (p : ι → ℝ≥0) (A : Matrix ι ι ℂ) (i j : ι) :
    rootStateCommutator p A i j =
      ((Real.sqrt (p i) - Real.sqrt (p j) : ℝ) : ℂ) * A i j := by
  simp only [rootStateCommutator, Matrix.sub_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Complex.ofReal_sub]
  ring

/-- Skew information is exactly half the commutator Hilbert--Schmidt energy. -/
theorem skewInformation_eq_half_hsInner_commutator (p : ι → ℝ≥0) (A : Matrix ι ι ℂ) :
    skewInformation p A =
      (QuantumAlg.hsInner (rootStateCommutator p A) (rootStateCommutator p A)).re / 2 := by
  have htrace : (QuantumAlg.hsInner (rootStateCommutator p A)
      (rootStateCommutator p A)).re =
      ∑ i, ∑ j, Complex.normSq (rootStateCommutator p A i j) := by
    simp only [QuantumAlg.hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Complex.re_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← starRingEnd_apply, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  rw [htrace]
  simp_rw [rootStateCommutator_apply, Complex.normSq_mul, Complex.normSq_ofReal,
    ← pow_two]
  unfold skewInformation
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The exact Born/geometric deficit is a matrix commutator energy. -/
theorem born_sub_sandwiched_eq_half_commutator_energy
    (p : ι → ℝ≥0) (A : Matrix ι ι ℂ) :
    bornQuadratic p A - sandwichedQuadratic p A =
      (QuantumAlg.hsInner (rootStateCommutator p A) (rootStateCommutator p A)).re / 2 := by
  rw [born_sub_sandwiched_eq_skewInformation, skewInformation_eq_half_hsInner_commutator]

end
end GaloisForLFunctions.HilbertMetric.QuantumInformation

#print axioms GaloisForLFunctions.HilbertMetric.QuantumInformation.rootStateCommutator_apply
#print axioms GaloisForLFunctions.HilbertMetric.QuantumInformation.skewInformation_eq_half_hsInner_commutator
#print axioms GaloisForLFunctions.HilbertMetric.QuantumInformation.born_sub_sandwiched_eq_half_commutator_energy
