import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinDensityFlow
import GaloisForLFunctions.HTGeometry.FiniteBuresKrausDataProcessingLaw

/-!
# Conditional Kraus realization of conservative–dissipative spin evolution

Application of the conservative–dissipative magnetization mechanism in Schaffer–Exl,
arXiv:2609.04530, to the corpus's finite Kraus channels. An explicit two-outcome
instrument is complete for every complex chart multiplier. Its selected branch has
an exact strictly positive probability, and conditioning that branch gives the
exact nonlinear spin density flow. This supplies a positive realization alongside
the deterministic-channel obstruction in `ConservativeDissipativeSpinChannelBarrier`.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Selected diagonal filter for arbitrary complex stereographic multiplier. -/
def spinFilterSelected (k : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (spinChartScale k : ℂ) • !![k, 0; 0, 1]

/-- Complementary outcome making the selected filter part of a normalized instrument. -/
def spinFilterComplement (k : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (spinChartScale k : ℂ) • !![1, 0; 0, k]

/-- The two explicit outcomes are exactly Kraus complete, including a zero multiplier. -/
theorem spinFilter_complete (k : ℂ) :
    (spinFilterSelected k)ᴴ * spinFilterSelected k +
      (spinFilterComplement k)ᴴ * spinFilterComplement k = 1 := by
  have hd : 1 + ‖k‖ ^ 2 ≠ 0 := by positivity
  have hs : spinChartScale k ^ 2 * (1 + ‖k‖ ^ 2) = 1 := by
    rw [spinChartScale_sq, inv_mul_cancel₀ hd]
  have hc : (spinChartScale k : ℂ) ^ 2 * (1 + conj k * k) = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    exact_mod_cast hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinFilterSelected, spinFilterComplement, Matrix.conjTranspose_apply,
      Matrix.mul_apply, Fin.sum_univ_two]
  all_goals (convert hc using 1; ring)

/-- A fully constructed physical two-outcome Kraus channel for every complex multiplier. -/
def spinFilterChannel (k : ℂ) : FiniteRectangularKrausChannel 2 2 (Fin 2) where
  operator := ![spinFilterSelected k, spinFilterComplement k]
  completeness := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using spinFilter_complete k

/-- Positive amplitude carried by the selected normalized spinor. -/
def spinFilterAmplitude (k z : ℂ) : ℝ :=
  spinChartScale k * spinChartScale z / spinChartScale (k * z)

theorem spinFilterAmplitude_pos (k z : ℂ) : 0 < spinFilterAmplitude k z := by
  unfold spinFilterAmplitude
  exact div_pos (mul_pos (spinChartScale_pos k) (spinChartScale_pos z)) (spinChartScale_pos _)

/-- The selected Kraus outcome sends the chart spinor to the multiplied chart with an exact amplitude. -/
theorem spinFilterSelected_spinor (k z : ℂ) :
    (spinFilterSelected k).mulVec (spinChartSpinor z) =
      (spinFilterAmplitude k z : ℂ) • spinChartSpinor (k * z) := by
  have hc : (spinChartScale (k * z) : ℂ) ≠ 0 := by
    exact_mod_cast (spinChartScale_pos (k * z)).ne'
  ext i
  fin_cases i <;>
    simp [spinFilterSelected, spinChartSpinor, spinFilterAmplitude,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.smul_apply]
  all_goals field_simp

/-- Actual selected-outcome probability for the normalized chart state. -/
def spinFilterProbability (k z : ℂ) : ℝ := spinFilterAmplitude k z ^ 2

theorem spinFilterProbability_pos (k z : ℂ) : 0 < spinFilterProbability k z :=
  sq_pos_of_pos (spinFilterAmplitude_pos k z)

/-- Closed success-probability formula in the original complex chart. -/
theorem spinFilterProbability_eq (k z : ℂ) :
    spinFilterProbability k z =
      (1 + ‖k * z‖ ^ 2) / ((1 + ‖k‖ ^ 2) * (1 + ‖z‖ ^ 2)) := by
  rw [spinFilterProbability, spinFilterAmplitude, div_pow, mul_pow,
    spinChartScale_sq, spinChartScale_sq, spinChartScale_sq]
  field_simp

/-- The constructed success probability is always at most one. -/
theorem spinFilterProbability_le_one (k z : ℂ) : spinFilterProbability k z ≤ 1 := by
  rw [spinFilterProbability_eq]
  have hd : 0 < (1 + ‖k‖ ^ 2) * (1 + ‖z‖ ^ 2) := by positivity
  apply (div_le_one hd).mpr
  rw [norm_mul, mul_pow]
  nlinarith [sq_nonneg ‖k‖, sq_nonneg ‖z‖]

/-- Real amplitude scaling has its exact effect on the corpus's pure projector. -/
theorem pureProjectorMatrix_real_smul (r : ℝ) (ψ : Fin 2 → ℂ) :
    pureProjectorMatrix ((r : ℂ) • ψ) = ((r ^ 2 : ℝ) : ℂ) • pureProjectorMatrix ψ := by
  ext i j
  simp [pureProjectorMatrix, Matrix.smul_apply]
  ring

/-- The selected unnormalized output is its actual probability times the desired pure density. -/
theorem spinFilterSelected_density (k z : ℂ) :
    spinFilterSelected k * spinChartDensity z * (spinFilterSelected k)ᴴ =
      (spinFilterProbability k z : ℂ) • spinChartDensity (k * z) := by
  rw [spinChartDensity_eq_pureProjector, conj_pureProjectorMatrix,
    spinFilterSelected_spinor, pureProjectorMatrix_real_smul]
  rfl

/-- Success probability is exactly the trace of the selected physical Kraus branch. -/
theorem spinFilterSelected_trace (k z : ℂ) :
    Matrix.trace (spinFilterSelected k * spinChartDensity z * (spinFilterSelected k)ᴴ) =
      (spinFilterProbability k z : ℂ) := by
  rw [spinFilterSelected_density, Matrix.trace_smul, spinChartDensity_trace, smul_eq_mul, mul_one]

/-- Conditioning the selected outcome implements the exact multiplied chart state. -/
theorem spinFilterSelected_conditioned (k z : ℂ) :
    ((spinFilterProbability k z : ℂ)⁻¹) •
      (spinFilterSelected k * spinChartDensity z * (spinFilterSelected k)ᴴ) =
        spinChartDensity (k * z) := by
  have hp : (spinFilterProbability k z : ℂ) ≠ 0 := by
    exact_mod_cast (spinFilterProbability_pos k z).ne'
  rw [spinFilterSelected_density, smul_smul, inv_mul_cancel₀ hp, one_smul]

/-- The actual complete channel contains the selected spin branch and its complementary outcome. -/
theorem spinFilterChannel_evolve (k z : ℂ) :
    (spinFilterChannel k).evolveMatrix (spinChartDensity z) =
      (spinFilterProbability k z : ℂ) • spinChartDensity (k * z) +
        spinFilterComplement k * spinChartDensity z * (spinFilterComplement k)ᴴ := by
  simp only [FiniteRectangularKrausChannel.evolveMatrix, spinFilterChannel, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, spinFilterSelected_density]

/-- Positive replacement for deterministic-channel realization: every exact spin time step is conditional. -/
theorem spinDensityFlow_conditioned_kraus (a : ℝ) (z : ℂ) (t : ℝ) :
    ((spinFilterProbability (Complex.exp (spinPlaneRate a * (t : ℂ))) z : ℂ)⁻¹) •
      (spinFilterSelected (Complex.exp (spinPlaneRate a * (t : ℂ))) * spinChartDensity z *
        (spinFilterSelected (Complex.exp (spinPlaneRate a * (t : ℂ))))ᴴ) =
          spinDensityFlow a z t :=
  spinFilterSelected_conditioned _ _

end
end GaloisForLFunctions.HTGeometry.SchafferExl
