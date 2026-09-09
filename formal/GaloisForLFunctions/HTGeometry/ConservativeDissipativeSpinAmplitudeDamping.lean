import GaloisForLFunctions.HTGeometry.ConservativeDissipativeKrausSemigroupBridge

/-!
# A Markovian amplitude-damping completion of the conditional spin flow

Application of Schaffer–Exl, arXiv:2609.04530, to the existing quantum dynamical
semigroup framework. A new physical Kraus completion transfers lost upper-level
population to the lower level. Its full channel obeys the semigroup law; its
selected no-jump branch, after conditioning by its actual positive trace, is the
same exact nonlinear spin density flow. The success probability is explicit and
satisfies a conditional-history cocycle. Time uses the existing semigroup's
nonnegative domain; the damping amplitude and initial chart coordinate are raw.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- No-jump multiplier at a time in the existing semigroup's nonnegative time domain. -/
def spinDecayFactor (a : ℝ) (t : NNReal) : ℂ :=
  Complex.exp (spinPlaneRate a * ((t : ℝ) : ℂ))

/-- Surviving upper-level population under the constructed damping. -/
def spinDecayMass (a : ℝ) (t : NNReal) : ℝ := Real.exp (-2 * a ^ 2 * (t : ℝ))

theorem spinDecayMass_pos (a : ℝ) (t : NNReal) : 0 < spinDecayMass a t := Real.exp_pos _

theorem spinDecayMass_le_one (a : ℝ) (t : NNReal) : spinDecayMass a t ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have h := mul_nonneg (sq_nonneg a) t.coe_nonneg
  linarith

theorem spinDecayFactor_norm_sq (a : ℝ) (t : NNReal) :
    ‖spinDecayFactor a t‖ ^ 2 = spinDecayMass a t := by
  simpa only [spinDecayFactor, spinDecayMass, spinPlaneFlow, mul_one, norm_one, one_pow]
    using spinPlaneFlow_norm_sq a 1 (t : ℝ)

/-- The actual no-jump operator of an amplitude-damping instrument. -/
def spinNoJump (a : ℝ) (t : NNReal) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![spinDecayFactor a t, 0; 0, 1]

/-- The complementary jump transfers lost upper population to the lower level. -/
def spinJump (a : ℝ) (t : NNReal) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 0; (Real.sqrt (1 - spinDecayMass a t) : ℂ), 0]

/-- The new two-outcome instrument is complete at every nonnegative time. -/
theorem spinAmplitude_complete (a : ℝ) (t : NNReal) :
    (spinNoJump a t)ᴴ * spinNoJump a t + (spinJump a t)ᴴ * spinJump a t = 1 := by
  have hk : conj (spinDecayFactor a t) * spinDecayFactor a t = (spinDecayMass a t : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, spinDecayFactor_norm_sq]
  have hj : (Real.sqrt (1 - spinDecayMass a t) : ℂ) ^ 2 = 1 - (spinDecayMass a t : ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr (spinDecayMass_le_one a t))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinNoJump, spinJump, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination hk + hj

/-- A fully constructed amplitude-damping Kraus channel for the spin mechanism. -/
def spinAmplitudeKraus (a : ℝ) (t : NNReal) : FiniteRectangularKrausChannel 2 2 (Fin 2) where
  operator := ![spinNoJump a t, spinJump a t]
  completeness := by
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using spinAmplitude_complete a t

/-- The amplitude-damping instrument is an actual channel in the existing semigroup framework. -/
def spinAmplitudeChannel (a : ℝ) (t : NNReal) : QuantumChannel (Fin 2) :=
  quantumChannelFromRectangularKraus (spinAmplitudeKraus a t)

/-- Exact matrix action on every input, including the transferred population. -/
theorem spinAmplitudeChannel_entries (a : ℝ) (t : NNReal) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (spinAmplitudeChannel a t).map ρ =
      !![(spinDecayMass a t : ℂ) * ρ 0 0, spinDecayFactor a t * ρ 0 1;
        conj (spinDecayFactor a t) * ρ 1 0, ρ 1 1 + (1 - (spinDecayMass a t : ℂ)) * ρ 0 0] := by
  have hk : conj (spinDecayFactor a t) * spinDecayFactor a t = (spinDecayMass a t : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, spinDecayFactor_norm_sq]
  have hj : (Real.sqrt (1 - spinDecayMass a t) : ℂ) ^ 2 = 1 - (spinDecayMass a t : ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr (spinDecayMass_le_one a t))
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinAmplitudeChannel, quantumChannelFromRectangularKraus, spinAmplitudeKraus,
      FiniteRectangularKrausChannel.evolveMatrix, Fin.sum_univ_two, spinNoJump, spinJump,
      Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · linear_combination ρ 0 0 * hk
  · ring
  · linear_combination ρ 0 0 * hj

/-- Complex no-jump amplitudes obey the exact time-composition law. -/
theorem spinDecayFactor_add (a : ℝ) (s t : NNReal) :
    spinDecayFactor a (s + t) = spinDecayFactor a s * spinDecayFactor a t := by
  simp only [spinDecayFactor, NNReal.coe_add, Complex.ofReal_add, mul_add, Complex.exp_add]

/-- Surviving populations obey the same multiplicative time law. -/
theorem spinDecayMass_add (a : ℝ) (s t : NNReal) :
    spinDecayMass a (s + t) = spinDecayMass a s * spinDecayMass a t := by
  simp only [spinDecayMass, NNReal.coe_add, mul_add, Real.exp_add]

/-- The complete amplitude-damping channel starts exactly at identity. -/
theorem spinAmplitudeChannel_zero (a : ℝ) : spinAmplitudeChannel a 0 = 1 := by
  apply QuantumChannel.ext
  funext ρ
  rw [spinAmplitudeChannel_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinDecayFactor, spinDecayMass]

/-- Unlike the earlier forgotten instrument, this full channel obeys the actual semigroup law. -/
theorem spinAmplitudeChannel_add (a : ℝ) (s t : NNReal) :
    spinAmplitudeChannel a (s + t) = spinAmplitudeChannel a s * spinAmplitudeChannel a t := by
  apply QuantumChannel.ext
  funext ρ
  change (spinAmplitudeChannel a (s + t)).map ρ =
    (spinAmplitudeChannel a s).map ((spinAmplitudeChannel a t).map ρ)
  rw [spinAmplitudeChannel_entries, spinAmplitudeChannel_entries, spinAmplitudeChannel_entries,
    spinDecayFactor_add, spinDecayMass_add]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- A genuine quantum dynamical semigroup constructed from raw damping amplitude alone. -/
def spinAmplitudeSemigroup (a : ℝ) : DynamicalSemigroup (Fin 2) where
  ch := spinAmplitudeChannel a
  ch_zero := spinAmplitudeChannel_zero a
  ch_add := spinAmplitudeChannel_add a

/-- Actual no-jump success probability for any normalized chart input. -/
def spinNoJumpProbability (a : ℝ) (t : NNReal) (z : ℂ) : ℝ :=
  (spinChartScale z / spinChartScale (spinDecayFactor a t * z)) ^ 2

theorem spinNoJumpProbability_pos (a : ℝ) (t : NNReal) (z : ℂ) :
    0 < spinNoJumpProbability a t z := by
  exact sq_pos_of_pos (div_pos (spinChartScale_pos _) (spinChartScale_pos _))

/-- The selected normalized spinor follows the same multiplied chart as the nonlinear spin evolution. -/
theorem spinNoJump_spinor (a : ℝ) (t : NNReal) (z : ℂ) :
    (spinNoJump a t).mulVec (spinChartSpinor z) =
      ((spinChartScale z / spinChartScale (spinDecayFactor a t * z) : ℝ) : ℂ) •
        spinChartSpinor (spinDecayFactor a t * z) := by
  have hc : (spinChartScale (spinDecayFactor a t * z) : ℂ) ≠ 0 := by
    exact_mod_cast (spinChartScale_pos _).ne'
  ext i
  fin_cases i <;> simp [spinNoJump, spinChartSpinor, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two] <;> field_simp

/-- The actual unnormalized no-jump branch is its success probability times the exact spin density. -/
theorem spinNoJump_density (a : ℝ) (t : NNReal) (z : ℂ) :
    spinNoJump a t * spinChartDensity z * (spinNoJump a t)ᴴ =
      (spinNoJumpProbability a t z : ℂ) • spinDensityFlow a z t := by
  rw [spinChartDensity_eq_pureProjector, conj_pureProjectorMatrix,
    spinNoJump_spinor, pureProjectorMatrix_real_smul]
  rfl

/-- A Markovian complete quantum evolution realizes the exact nonlinear spin flow after conditioning. -/
theorem spinAmplitudeSemigroup_conditioned (a : ℝ) (t : NNReal) (z : ℂ) :
    ((spinNoJumpProbability a t z : ℂ)⁻¹) •
      (spinNoJump a t * spinChartDensity z * (spinNoJump a t)ᴴ) = spinDensityFlow a z t := by
  have hp : (spinNoJumpProbability a t z : ℂ) ≠ 0 := by
    exact_mod_cast (spinNoJumpProbability_pos a t z).ne'
  rw [spinNoJump_density, smul_smul, inv_mul_cancel₀ hp, one_smul]

/-- The exact physical survival probability, expressed without normalization square roots. -/
theorem spinNoJumpProbability_eq (a : ℝ) (t : NNReal) (z : ℂ) :
    spinNoJumpProbability a t z = (1 + spinDecayMass a t * ‖z‖ ^ 2) / (1 + ‖z‖ ^ 2) := by
  rw [spinNoJumpProbability, div_pow, spinChartScale_sq, spinChartScale_sq,
    norm_mul, mul_pow, spinDecayFactor_norm_sq]
  field_simp

/-- Conditioning uses an actual probability in the unit interval. -/
theorem spinNoJumpProbability_le_one (a : ℝ) (t : NNReal) (z : ℂ) :
    spinNoJumpProbability a t z ≤ 1 := by
  rw [spinNoJumpProbability_eq]
  apply (div_le_one (by positivity : 0 < 1 + ‖z‖ ^ 2)).mpr
  have h := mul_le_mul_of_nonneg_right (spinDecayMass_le_one a t) (sq_nonneg ‖z‖)
  linarith

/-- The success probability is the literal trace of the no-jump output. -/
theorem spinNoJump_trace (a : ℝ) (t : NNReal) (z : ℂ) :
    Matrix.trace (spinNoJump a t * spinChartDensity z * (spinNoJump a t)ᴴ) =
      (spinNoJumpProbability a t z : ℂ) := by
  rw [spinNoJump_density, Matrix.trace_smul]
  change (spinNoJumpProbability a t z : ℂ) • Matrix.trace (spinChartDensity _) = _
  rw [spinChartDensity_trace, smul_eq_mul, mul_one]

/-- No-jump operators themselves compose, before either measurement or conditioning. -/
theorem spinNoJump_add (a : ℝ) (s t : NNReal) :
    spinNoJump a (s + t) = spinNoJump a s * spinNoJump a t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinNoJump, spinDecayFactor_add, Matrix.mul_apply, Fin.sum_univ_two]

/-- Selected-history probabilities obey the exact conditional-probability cocycle. -/
theorem spinNoJumpProbability_cocycle (a : ℝ) (s t : NNReal) (z : ℂ) :
    spinNoJumpProbability a (s + t) z =
      spinNoJumpProbability a t z * spinNoJumpProbability a s (spinDecayFactor a t * z) := by
  have hc : spinChartScale (spinDecayFactor a t * z) ≠ 0 := (spinChartScale_pos _).ne'
  simp only [spinNoJumpProbability, spinDecayFactor_add, mul_assoc]
  field_simp

end
end GaloisForLFunctions.HTGeometry.SchafferExl
