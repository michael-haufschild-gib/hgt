import GaloisForLFunctions.HilbertMetric.QuantumInformation.ThermalSkewInformation
import GaloisForLFunctions.QuantumAlg.Util.HilbertSchmidt

/-!
# Thermal matrix robustness with quantum variance deflation

Weighted Hilbert--Schmidt Cauchy--Schwarz pairs the geometric thermal
quadratic form with its inverse. For centered Hermitian observables and
traceless Hermitian perturbations this is the order-two quantum
Hammersley--Chapman--Robbins bound. The geometric coefficient is exactly
Born noise minus skew information.
-/

open scoped BigOperators NNReal
namespace GaloisForLFunctions.HilbertMetric.QuantumInformation
open _root_.HTGeometry
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Inverse-geometric thermal quadratic form on matrix perturbations. -/
def thermalInverseQuadratic (β : ℝ) (E : ι → ℝ) (X : Matrix ι ι ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (X i j) / finiteKMSWightmanWeight β E i j

theorem thermalInverseQuadratic_nonneg (β : ℝ) (E : ι → ℝ) (X : Matrix ι ι ℂ) :
    0 ≤ thermalInverseQuadratic β E X := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    div_nonneg (Complex.normSq_nonneg _) (finiteKMSWightmanWeight_pos β E i j).le

/-- Real Hilbert--Schmidt pairing in matrix-entry coordinates. -/
theorem hsInner_re_eq_sum (A X : Matrix ι ι ℂ) :
    (QuantumAlg.hsInner A X).re =
      ∑ i, ∑ j, (A i j).re * (X i j).re + (A i j).im * (X i j).im := by
  simp only [QuantumAlg.hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add]
  rw [Finset.sum_comm]

/-- The direct geometric-mean matrix robustness bound at every temperature. -/
theorem thermal_hilbertSchmidt_robustness (β : ℝ) (E : ι → ℝ) (A X : Matrix ι ι ℂ) :
    (QuantumAlg.hsInner A X).re ^ (2 : ℕ) ≤
      sandwichedQuadratic (thermalPopulation β E) A * thermalInverseQuadratic β E X := by
  rw [hsInner_re_eq_sum, sandwichedQuadratic_thermal_eq]
  change (∑ i, ∑ j, (A i j).re * (X i j).re + (A i j).im * (X i j).im) ^ (2 : ℕ) ≤
    (∑ i, ∑ j, finiteKMSWightmanWeight β E i j * Complex.normSq (A i j)) *
      ∑ i, ∑ j, Complex.normSq (X i j) / finiteKMSWightmanWeight β E i j
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
  · intro i _
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (finiteKMSWightmanWeight_pos β E i j).le (Complex.normSq_nonneg _)
  · intro i _
    exact Finset.sum_nonneg fun j _ =>
      div_nonneg (Complex.normSq_nonneg _) (finiteKMSWightmanWeight_pos β E i j).le
  · intro i _
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    · intro j _
      exact mul_nonneg (finiteKMSWightmanWeight_pos β E i j).le (Complex.normSq_nonneg _)
    · intro j _
      exact div_nonneg (Complex.normSq_nonneg _) (finiteKMSWightmanWeight_pos β E i j).le
    · intro j _
      have hc : finiteKMSWightmanWeight β E i j * Complex.normSq (A i j) *
          (Complex.normSq (X i j) / finiteKMSWightmanWeight β E i j) =
          Complex.normSq (A i j) * Complex.normSq (X i j) := by
        field_simp [(finiteKMSWightmanWeight_pos β E i j).ne']
      rw [hc, Complex.normSq_apply, Complex.normSq_apply]
      nlinarith only [sq_nonneg ((A i j).re * (X i j).im - (A i j).im * (X i j).re)]

/-- Skew information is the exact improvement in the matrix error coefficient. -/
theorem thermal_hilbertSchmidt_robustness_deflated (β : ℝ) (E : ι → ℝ)
    (A X : Matrix ι ι ℂ) :
    (QuantumAlg.hsInner A X).re ^ (2 : ℕ) ≤
      (bornQuadratic (thermalPopulation β E) A - skewInformation (thermalPopulation β E) A) *
        thermalInverseQuadratic β E X := by
  have hid := born_sub_sandwiched_eq_skewInformation (thermalPopulation β E) A
  have heq : bornQuadratic (thermalPopulation β E) A -
      skewInformation (thermalPopulation β E) A = sandwichedQuadratic (thermalPopulation β E) A := by
    linarith only [hid]
  rw [heq]
  exact thermal_hilbertSchmidt_robustness β E A X

/-- The geometric thermal tilt is the equality direction of the quadratic bound. -/
def thermalWorstDirection (β : ℝ) (E : ι → ℝ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => (finiteKMSWightmanWeight β E i j : ℂ) * A i j

/-- The inverse metric of the equality direction is the geometric variance. -/
theorem thermalInverseQuadratic_worstDirection (β : ℝ) (E : ι → ℝ)
    (A : Matrix ι ι ℂ) :
    thermalInverseQuadratic β E (thermalWorstDirection β E A) =
      sandwichedQuadratic (thermalPopulation β E) A := by
  rw [sandwichedQuadratic_thermal_eq]
  unfold thermalInverseQuadratic thermalWorstDirection
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change Complex.normSq ((finiteKMSWightmanWeight β E i j : ℂ) * A i j) /
    finiteKMSWightmanWeight β E i j = finiteKMSWightmanWeight β E i j * Complex.normSq (A i j)
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  field_simp [(finiteKMSWightmanWeight_pos β E i j).ne']

/-- The equality direction pairs with its observable to give the same variance. -/
theorem hsInner_thermalWorstDirection (β : ℝ) (E : ι → ℝ) (A : Matrix ι ι ℂ) :
    (QuantumAlg.hsInner A (thermalWorstDirection β E A)).re =
      sandwichedQuadratic (thermalPopulation β E) A := by
  rw [hsInner_re_eq_sum, sandwichedQuadratic_thermal_eq]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [thermalWorstDirection, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero,
    finiteKMSWightmanTransitionIntensity, wightmanTransitionIntensity, Complex.normSq_apply]
  ring

/-- The quadratic robustness inequality is attained in its geometric tilt direction. -/
theorem thermal_hilbertSchmidt_robustness_attained (β : ℝ) (E : ι → ℝ)
    (A : Matrix ι ι ℂ) :
    (QuantumAlg.hsInner A (thermalWorstDirection β E A)).re ^ (2 : ℕ) =
      sandwichedQuadratic (thermalPopulation β E) A *
        thermalInverseQuadratic β E (thermalWorstDirection β E A) := by
  rw [hsInner_thermalWorstDirection, thermalInverseQuadratic_worstDirection, pow_two]

end
end GaloisForLFunctions.HilbertMetric.QuantumInformation

#print axioms GaloisForLFunctions.HilbertMetric.QuantumInformation.thermalInverseQuadratic_nonneg
#print axioms GaloisForLFunctions.HilbertMetric.QuantumInformation.hsInner_re_eq_sum
#print axioms GaloisForLFunctions.HilbertMetric.QuantumInformation.thermal_hilbertSchmidt_robustness
#print axioms GaloisForLFunctions.HilbertMetric.QuantumInformation.thermal_hilbertSchmidt_robustness_deflated
#print axioms GaloisForLFunctions.HilbertMetric.QuantumInformation.thermalInverseQuadratic_worstDirection
#print axioms GaloisForLFunctions.HilbertMetric.QuantumInformation.hsInner_thermalWorstDirection
#print axioms GaloisForLFunctions.HilbertMetric.QuantumInformation.thermal_hilbertSchmidt_robustness_attained
