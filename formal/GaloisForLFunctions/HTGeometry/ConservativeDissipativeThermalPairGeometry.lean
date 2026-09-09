import GaloisForLFunctions.HTGeometry.ConservativeDissipativeThermalContraction
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinFidelity

/-!
# Thermal contraction in the corpus's projective geometry

The conservative–dissipative energy mechanism of arXiv:2609.04530 is applied to
actual differences of normalized pure density matrices. The existing trace
Hilbert--Schmidt energy agrees exactly with the existing chordal metric before
evolution. Sharp thermal energy bounds therefore give quantitative bounds on
physical output distance. The entire output displacement is independent of bath
bias, because normalization cancels the affine stationary forcing.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
open Matrix Filter
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Existing trace energy and existing projective chordal geometry agree on actual pure density differences. -/
theorem spinChartDensity_hilbertSchmidt_chordal (z w : ℂ) :
    finiteMatrixHilbertSchmidtEnergy (spinChartDensity z - spinChartDensity w) =
      2 * _root_.Bottcher.chordalDist z w ^ 2 := by
  rw [← spinChartSpinor_projector_distance, finiteMatrixHilbertSchmidtEnergy_eq_sum_normSq,
    EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Complex.normSq_eq_norm_sq]
  rfl

/-- Difference of two independently normalized pure inputs after the same thermal channel. -/
def spinThermalPairDisplacement (a u : ℝ) (t : NNReal) (z w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (spinThermalChannel a u t).map (spinChartDensity z) - (spinThermalChannel a u t).map (spinChartDensity w)

/-- The actual output difference is the channel applied to the input difference. -/
theorem spinThermalPairDisplacement_eq (a u : ℝ) (t : NNReal) (z w : ℂ) :
    spinThermalPairDisplacement a u t z w =
      (spinThermalChannel a u t).map (spinChartDensity z - spinChartDensity w) := by
  unfold spinThermalPairDisplacement
  rw [sub_eq_add_neg (spinChartDensity z), ← neg_one_smul ℂ (spinChartDensity w),
    (spinThermalChannel a u t).map_add, (spinThermalChannel a u t).map_smul, neg_one_smul]
  rfl

/-- Constructed normalization makes every output displacement traceless. -/
theorem spinThermalPairDisplacement_trace (a u : ℝ) (t : NNReal) (z w : ℂ) :
    Matrix.trace (spinThermalPairDisplacement a u t z w) = 0 := by
  rw [spinThermalPairDisplacement_eq, (spinThermalChannel a u t).tracePreserving,
    Matrix.trace_sub, spinChartDensity_trace, spinChartDensity_trace, sub_self]

/-- The stationary forcing cancels from pair displacements, so bath bias cannot change them. -/
theorem spinThermalPairDisplacement_bath_independent (a u v : ℝ) (t : NNReal) (z w : ℂ) :
    spinThermalPairDisplacement a u t z w = spinThermalPairDisplacement a v t z w := by
  rw [spinThermalPairDisplacement_eq, spinThermalPairDisplacement_eq,
    spinThermalChannel_entries, spinThermalChannel_entries,
    Matrix.trace_sub, spinChartDensity_trace, spinChartDensity_trace, sub_self]
  simp

/-- The sharp energy enclosure transfers to actual state distances and the existing chordal metric. -/
theorem spinThermalPairDisplacement_chordal_bounds (a u : ℝ) (t : NNReal) (z w : ℂ) :
    (spinDecayMass a t) ^ 2 * (2 * _root_.Bottcher.chordalDist z w ^ 2) ≤
      finiteMatrixHilbertSchmidtEnergy (spinThermalPairDisplacement a u t z w) ∧
    finiteMatrixHilbertSchmidtEnergy (spinThermalPairDisplacement a u t z w) ≤
      spinDecayMass a t * (2 * _root_.Bottcher.chordalDist z w ^ 2) := by
  have h := spinThermalEnergy_channel_bounds a u t (spinChartDensity z - spinChartDensity w)
  have hi : spinThermalEnergy u (spinChartDensity z - spinChartDensity w) =
      2 * _root_.Bottcher.chordalDist z w ^ 2 := by
    simp only [spinThermalEnergy, spinThermalCentered, Matrix.trace_sub, spinChartDensity_trace,
      sub_self, zero_smul, sub_zero]
    exact spinChartDensity_hilbertSchmidt_chordal z w
  have ho : spinThermalEnergy u ((spinThermalChannel a u t).map (spinChartDensity z - spinChartDensity w)) =
      finiteMatrixHilbertSchmidtEnergy (spinThermalPairDisplacement a u t z w) := by
    rw [← spinThermalPairDisplacement_eq]
    simp [spinThermalEnergy, spinThermalCentered, spinThermalPairDisplacement_trace]
  rwa [hi, ho] at h

/-- Increasing physical time decreases actual pair distance in the trace-defined Hilbert--Schmidt geometry. -/
theorem spinThermalPairDisplacement_progress (a u : ℝ) (s t : NNReal) (z w : ℂ) :
    finiteMatrixHilbertSchmidtEnergy (spinThermalPairDisplacement a u (s + t) z w) ≤
      finiteMatrixHilbertSchmidtEnergy (spinThermalPairDisplacement a u t z w) := by
  have h := spinThermalEnergy_channel_progress a u s t (spinChartDensity z - spinChartDensity w)
  simp only [← spinThermalPairDisplacement_eq, spinThermalEnergy, spinThermalCentered,
    spinThermalPairDisplacement_trace, zero_smul, sub_zero] at h
  exact h

end
end GaloisForLFunctions.HTGeometry.SchafferExl
