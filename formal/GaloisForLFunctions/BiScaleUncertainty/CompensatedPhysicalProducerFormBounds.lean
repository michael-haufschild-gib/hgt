import GaloisForLFunctions.BiScaleUncertainty.CompensatedPhysicalProducerConvergence

/-!
# Exact compact-form bounds for physical producers

The source trace coefficient and graph resistance control their combined form
on every physical velocity. Substitution gives explicit producer and affine
commutator costs, and each approximation-error form vanishes separately.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology CompactlySupported ENNReal NNReal
namespace GaloisForLFunctions.BiScaleUncertainty.PathCongestion
open SobolevShear
set_option autoImplicit false

/-- The combined compact source and graph form has its exact constructed coefficient. -/
theorem compact_formEnergy_le_traceCoefficient_add_resistance
    (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0) (u : Velocity) :
    sourceMass ψ u 0 + jumpEnergy (compactMixture ψ weights) u ≤
      (ENNReal.ofReal (sourceTraceCoefficient ψ) + resistanceMass ψ weights) *
        ENNReal.ofReal (‖u‖ ^ 2) := by
  calc
    _ ≤ ENNReal.ofReal (sourceTraceCoefficient ψ * ‖u‖ ^ 2) +
        resistanceMass ψ weights * ENNReal.ofReal (‖u‖ ^ 2) :=
      add_le_add (sourceMass_le_traceCoefficient ψ u) (compact_jumpEnergy_le_norm_sq ψ weights u)
    _ = _ := by rw [ENNReal.ofReal_mul (sourceTraceCoefficient_nonneg ψ), add_mul]

/-- The full error bound retains all three explicit physical approximation costs. -/
theorem compact_formError_smoothedCompensatedVelocity_le_explicit
    (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0) (n : ℕ) (q : Velocity) :
    sourceMass ψ (smoothedCompensatedVelocity n q - q) 0 +
        jumpEnergy (compactMixture ψ weights) (smoothedCompensatedVelocity n q - q) ≤
      (ENNReal.ofReal (sourceTraceCoefficient ψ) + resistanceMass ψ weights) *
        ENNReal.ofReal ((‖truncatedVelocity n q - positivePhysicalVelocity q‖ +
          Real.exp (-producerScale n / 2) * ‖q‖ +
          ‖physicalBoxAverage (-2 * producerScale n) (positivePhysicalVelocity q) -
            positivePhysicalVelocity q‖) ^ 2) := by
  rw [sourceMass_sub_eq_sub_positivePhysicalVelocity,
    PathCongestionBridge.jumpEnergy_sub_eq_sub_positivePhysicalVelocity]
  apply (compact_formEnergy_le_traceCoefficient_add_resistance ψ weights _).trans
  apply mul_le_mul_right
  apply ENNReal.ofReal_le_ofReal
  have hb := norm_smoothedCompensatedVelocity_sub_positive_le n q
  have hn : 0 ≤ ‖truncatedVelocity n q - positivePhysicalVelocity q‖ +
      Real.exp (-producerScale n / 2) * ‖q‖ +
      ‖physicalBoxAverage (-2 * producerScale n) (positivePhysicalVelocity q) -
        positivePhysicalVelocity q‖ := by positivity
  nlinarith only [hb, hn, norm_nonneg (smoothedCompensatedVelocity n q - positivePhysicalVelocity q)]

/-- The whole compact graph form inherits the exact affine commutator energy ceiling. -/
theorem compact_formEnergy_affine_smoothedCompensatedVelocity_le
    (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0) (a b : ℝ) (n : ℕ) (q : Velocity) :
    sourceMass ψ (physicalAffineCommutator a b (smoothedCompensatedVelocity n q)) 0 +
        jumpEnergy (compactMixture ψ weights)
          (physicalAffineCommutator a b (smoothedCompensatedVelocity n q)) ≤
      (ENNReal.ofReal (sourceTraceCoefficient ψ) + resistanceMass ψ weights) *
        ENNReal.ofReal (4 * |a| * (min 1 (|b * (a - 1)| / producerStep n)) ^ 2 *
          (1 + Real.exp (-producerScale n)) * ‖q‖ ^ 2) :=
  (compact_formEnergy_le_traceCoefficient_add_resistance ψ weights _).trans
    (mul_le_mul_right (ENNReal.ofReal_le_ofReal
      (smoothedCompensatedVelocity_affine_energy_le a b n q)) _)

/-- Source-mass and graph approximation errors vanish individually. -/
theorem compact_formError_components_smoothedCompensatedVelocity_tendsto
    (ψ : C_c(ℝ, ℝ)) (weights : ℕ → ℝ≥0) (q : Velocity) :
    Tendsto (fun n => sourceMass ψ (smoothedCompensatedVelocity n q - q) 0) atTop (𝓝 0) ∧
      Tendsto (fun n => jumpEnergy (compactMixture ψ weights)
        (smoothedCompensatedVelocity n q - q)) atTop (𝓝 0) := by
  constructor
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (compact_formError_smoothedCompensatedVelocity_tendsto ψ weights q)
      (fun _ => zero_le) (fun _ => le_add_of_nonneg_right zero_le)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (compact_formError_smoothedCompensatedVelocity_tendsto ψ weights q)
      (fun _ => zero_le) (fun _ => le_add_of_nonneg_left zero_le)

end GaloisForLFunctions.BiScaleUncertainty.PathCongestion
