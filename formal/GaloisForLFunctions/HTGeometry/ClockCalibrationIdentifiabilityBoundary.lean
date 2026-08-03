import GaloisForLFunctions.HTGeometry.ClockCalibrationFailureModes

/-!
# The exact identifiability boundary of two-mass self-calibration

Two distinct calibrated masses and a nonvanishing endpoint calibration recover both the calibration
product and the undressed metric principal symbol. This file proves each of those two hypotheses
necessary, so the identifiability statement is an exact boundary.

* **One species is degenerate.** The single-species datum is the calibrated symbol `κ g⁻¹`, which is
  invariant under `κ ↦ cκ`, `g⁻¹ ↦ c⁻¹g⁻¹`. It therefore determines neither factor.
* **Equal masses are one species.** With `μ₁ = μ₂` the zeroth-order channel vanishes identically, so
  the two-mass datum inherits exactly the same rescaling degeneracy.
* **Vanishing calibration hides the metric.** With `κ = 0` both channels vanish for every metric
  symbol, so nothing about the geometry is observable.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

section Boundary

variable {K : Type u} [Field K]

/-- The single-species datum: the calibrated principal symbol. -/
def singleSpeciesSymbol (calibration metricSymbol : K) : K :=
  calibration * metricSymbol

/-- **Exact rescaling degeneracy of one species under unknown gain.** -/
theorem singleSpeciesSymbol_rescaling {c : K} (hc : c ≠ 0) (calibration metricSymbol : K) :
    singleSpeciesSymbol (c * calibration) (c⁻¹ * metricSymbol) =
      singleSpeciesSymbol calibration metricSymbol := by
  simp only [singleSpeciesSymbol]
  field_simp

/-- The rescaled state is genuinely different whenever the gain factor is not one and the
calibration does not vanish. -/
theorem rescaled_state_ne {c : K} (hc : c ≠ 1) {calibration : K} (hcal : calibration ≠ 0)
    (metricSymbol : K) :
    ((c * calibration, c⁻¹ * metricSymbol) : K × K) ≠ (calibration, metricSymbol) := by
  intro hEq
  have h := congrArg Prod.fst hEq
  simp only at h
  have h' : c * calibration = 1 * calibration := by rw [one_mul]; exact h
  exact hc (mul_right_cancel₀ hcal h')

/-- **One species determines neither calibration nor metric symbol.** -/
theorem exists_ne_with_eq_singleSpeciesSymbol {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    {calibration : K} (hcal : calibration ≠ 0) (metricSymbol : K) :
    ∃ state : K × K,
      state ≠ (calibration, metricSymbol) ∧
        singleSpeciesSymbol state.1 state.2 = singleSpeciesSymbol calibration metricSymbol :=
  ⟨(c * calibration, c⁻¹ * metricSymbol), rescaled_state_ne hc1 hcal metricSymbol,
    singleSpeciesSymbol_rescaling hc0 calibration metricSymbol⟩

/-- **Equal masses carry no more than one species.** The zeroth-order channel vanishes, so the
two-mass datum inherits the rescaling degeneracy exactly. -/
theorem twoMassCalibrationMetricData_eq_of_rescaling_of_eq_mass (massSq : K) {c : K} (hc : c ≠ 0)
    (calibration metricSymbol : K) :
    twoMassCalibrationMetricData massSq massSq (c * calibration) (c⁻¹ * metricSymbol) =
      twoMassCalibrationMetricData massSq massSq calibration metricSymbol := by
  simp only [twoMassCalibrationMetricData, sub_self, zero_mul]
  refine Prod.ext rfl ?_
  simpa [singleSpeciesSymbol] using singleSpeciesSymbol_rescaling hc calibration metricSymbol

/-- **Distinct masses are necessary for identifiability.** -/
theorem exists_ne_with_eq_twoMassCalibrationMetricData_of_eq_mass (massSq : K) {c : K}
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) {calibration : K} (hcal : calibration ≠ 0) (metricSymbol : K) :
    ∃ state : K × K,
      state ≠ (calibration, metricSymbol) ∧
        twoMassCalibrationMetricData massSq massSq state.1 state.2 =
          twoMassCalibrationMetricData massSq massSq calibration metricSymbol :=
  ⟨(c * calibration, c⁻¹ * metricSymbol), rescaled_state_ne hc1 hcal metricSymbol,
    twoMassCalibrationMetricData_eq_of_rescaling_of_eq_mass massSq hc0 calibration metricSymbol⟩

/-- **Vanishing endpoint calibration hides the metric completely.** Both measured channels vanish
for every metric symbol. -/
theorem twoMassCalibrationMetricData_zero_calibration (massSq₁ massSq₂ metricSymbol : K) :
    twoMassCalibrationMetricData massSq₁ massSq₂ (0 : K) metricSymbol = (0, 0) := by
  simp [twoMassCalibrationMetricData]

/-- **Nonvanishing calibration is necessary for identifiability.** -/
theorem exists_ne_with_eq_twoMassCalibrationMetricData_of_zero_calibration
    (massSq₁ massSq₂ : K) {metricSymbol₁ metricSymbol₂ : K} (hne : metricSymbol₁ ≠ metricSymbol₂) :
    ((0 : K), metricSymbol₁) ≠ ((0 : K), metricSymbol₂) ∧
      twoMassCalibrationMetricData massSq₁ massSq₂ 0 metricSymbol₁ =
        twoMassCalibrationMetricData massSq₁ massSq₂ 0 metricSymbol₂ := by
  refine ⟨?_, ?_⟩
  · intro hEq
    exact hne (congrArg Prod.snd hEq)
  · rw [twoMassCalibrationMetricData_zero_calibration,
      twoMassCalibrationMetricData_zero_calibration]

end Boundary

/-- Both necessity witnesses are inhabited over the reals. -/
theorem exists_real_rescaling_degeneracy :
    ∃ state : ℝ × ℝ,
      state ≠ ((1 : ℝ), (1 : ℝ)) ∧
        singleSpeciesSymbol state.1 state.2 = singleSpeciesSymbol (1 : ℝ) (1 : ℝ) :=
  exists_ne_with_eq_singleSpeciesSymbol (c := (2 : ℝ)) (by norm_num) (by norm_num)
    (by norm_num) 1

end GaloisForLFunctions.HTGeometry
