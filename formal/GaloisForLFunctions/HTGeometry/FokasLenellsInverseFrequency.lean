import GaloisForLFunctions.HTGeometry.FokasLenellsScatteringLipschitz
import GaloisForLFunctions.HTGeometry.FokasLenellsSquareIntegrableData

/-!
# Actual reflection data in the singular time-generator domain

Global Lipschitz continuity and zero-energy transparency imply boundedness
after division by spectral frequency. The independent global reflection bound
then supplies a reciprocal L² envelope. Consequently both actual scattering
coefficients and their prescribed time-space phases remain square integrable
after the inverse-frequency factor required by the paper's time evolution.
-/

open Complex Matrix MeasureTheory Filter Set Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- Both actual normalized reflection channels after one inverse spectral factor. -/
def regularInverseFrequencyReflection (q : SchwartzMap ℝ ℂ) (reverse : Bool) (z : ℝ) : ℂ :=
  (if reverse then regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z
    else regularReflectionCoefficient (globalSmallScatteringPotential q) z)/(z:ℂ)

/-- The zero-energy cancellation gives a global bounded inverse-frequency reflection coefficient. -/
theorem regularInverseFrequencyReflection_bound (q : SchwartzMap ℝ ℂ) (reverse : Bool) (z : ℝ) :
    ‖regularInverseFrequencyReflection q reverse z‖ ≤ regularReflectionFrequencyBudget q := by
  by_cases hz : z = 0
  · subst z
    simpa only [regularInverseFrequencyReflection,Complex.ofReal_zero,div_zero,norm_zero] using
      regularReflectionFrequencyBudget_nonneg q
  have hab : 0 < |z| := abs_pos.mpr hz
  cases reverse
  · change ‖regularReflectionCoefficient (globalSmallScatteringPotential q) z/(z:ℂ)‖ ≤ _
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs]
    exact (div_le_iff₀ hab).mpr (globalSmall_regularReflection_zero_rate q z).1
  · change ‖regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z/(z:ℂ)‖ ≤ _
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs]
    exact (div_le_iff₀ hab).mpr (globalSmall_regularReflection_zero_rate q z).2

/-- Restoring the spectral weight retains the paper's uniform small-reflection bound. -/
theorem regularInverseFrequencyReflection_weighted_bound (q : SchwartzMap ℝ ℂ) (reverse : Bool) (z : ℝ) :
    |z| *‖regularInverseFrequencyReflection q reverse z‖ ≤ 1/3 := by
  by_cases hz : z = 0
  · subst z
    simp only [abs_zero,zero_mul]
    positivity
  have hab := (abs_pos.mpr hz).ne'
  cases reverse
  · change |z| *‖regularReflectionCoefficient (globalSmallScatteringPotential q) z/(z:ℂ)‖ ≤ _
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ = ‖regularReflectionCoefficient (globalSmallScatteringPotential q) z‖ := by field_simp [hab]
      _ ≤ _ := (globalSmall_regularReflection_bounds q z).1
  · change |z| *‖regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z/(z:ℂ)‖ ≤ _
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ = ‖regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z‖ := by field_simp [hab]
      _ ≤ _ := (globalSmall_regularReflection_bounds q z).2

/-- The origin cancellation and the independent global bound combine into one reciprocal envelope. -/
theorem regularInverseFrequencyReflection_reciprocal_bound (q : SchwartzMap ℝ ℂ) (reverse : Bool) (z : ℝ) :
    ‖regularInverseFrequencyReflection q reverse z‖ ≤ (regularReflectionFrequencyBudget q+1/3)/(1+|z|) := by
  apply (le_div_iff₀ (by positivity : (0:ℝ) < 1+|z|)).mpr
  have h0 := regularInverseFrequencyReflection_bound q reverse z
  have h1 := regularInverseFrequencyReflection_weighted_bound q reverse z
  nlinarith

theorem regularInverseFrequencyReflection_measurable (q : SchwartzMap ℝ ℂ) (reverse : Bool) :
    Measurable (regularInverseFrequencyReflection q reverse) := by
  cases reverse
  · exact (continuous_globalSmall_regularReflection q).1.measurable.div Complex.continuous_ofReal.measurable
  · exact (continuous_globalSmall_regularReflection q).2.measurable.div Complex.continuous_ofReal.measurable

/-- The genuine direct-scattering data lie in the L² domain of the singular inverse-frequency time multiplier. -/
theorem regularInverseFrequencyReflection_memLp (q : SchwartzMap ℝ ℂ) (reverse : Bool) :
    MemLp (regularInverseFrequencyReflection q reverse) 2 volume :=
  (reciprocalEnvelope_memLp (regularReflectionFrequencyBudget q+1/3)).mono'
    (regularInverseFrequencyReflection_measurable q reverse).aestronglyMeasurable
    (Eventually.of_forall (regularInverseFrequencyReflection_reciprocal_bound q reverse))

/-- The actual oscillatory jump channel after one inverse frequency. -/
def regularInverseFrequencyJump (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) : ℂ :=
  (if reverse then regularJumpReverseReflection (globalSmallScatteringPotential q) t x z
    else regularJumpReflection (globalSmallScatteringPotential q) t x z)/(z:ℂ)

/-- The time and space phases preserve exactly the inverse-frequency channel norm. -/
theorem regularInverseFrequencyJump_norm (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    ‖regularInverseFrequencyJump q t x reverse z‖ = ‖regularInverseFrequencyReflection q reverse z‖ := by
  cases reverse
  · simp only [regularInverseFrequencyJump,regularInverseFrequencyReflection,Bool.false_eq_true,↓reduceIte,norm_div,
      (regularJumpReflection_norms (globalSmallScatteringPotential q) t x z).1]
  · simp only [regularInverseFrequencyJump,regularInverseFrequencyReflection,↓reduceIte,norm_div,
      (regularJumpReflection_norms (globalSmallScatteringPotential q) t x z).2]

theorem regularInverseFrequencyJump_measurable (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    Measurable (regularInverseFrequencyJump q t x reverse) := by
  cases reverse
  · exact (measurable_globalSmall_regularJump q t x).1.div Complex.continuous_ofReal.measurable
  · exact (measurable_globalSmall_regularJump q t x).2.div Complex.continuous_ofReal.measurable

/-- The singular generator-domain estimate is preserved for every time and position. -/
theorem regularInverseFrequencyJump_memLp (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) :
    MemLp (regularInverseFrequencyJump q t x reverse) 2 volume :=
  (regularInverseFrequencyReflection_memLp q reverse).congr_norm
    (regularInverseFrequencyJump_measurable q t x reverse).aestronglyMeasurable
    (Eventually.of_forall fun z => (regularInverseFrequencyJump_norm q t x reverse z).symm)

/-- The differentiated time symbol has one uniform bound over the whole physical plane. -/
theorem regularInverseFrequencyJump_bound (q : SchwartzMap ℝ ℂ) (t x : ℝ) (reverse : Bool) (z : ℝ) :
    ‖regularInverseFrequencyJump q t x reverse z‖ ≤ regularReflectionFrequencyBudget q := by
  rw [regularInverseFrequencyJump_norm]
  exact regularInverseFrequencyReflection_bound q reverse z

end
end GaloisForLFunctions.HTGeometry.FokasLenells
