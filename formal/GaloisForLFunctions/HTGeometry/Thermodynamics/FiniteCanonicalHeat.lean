import GaloisForLFunctions.HTGeometry.TraceDynamicsThermalGeometry
import GaloisForLFunctions.HTGeometry.FiniteGibbsDifferentialBoundary

/-!
# Canonical heat capacity, partition curvature and spectral gaps

Equation (5.12) of arXiv:2611.16364 connects heat capacity to energy
fluctuations. Here the physical-temperature derivative is evaluated for
every finite corpus Gibbs system. The existing two-copy spectral moment
then gives a second, independent expression for the same response.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.Thermodynamics
open _root_.HTGeometry TraceDynamics
variable {A : Type*} [Fintype A] [Nonempty A]

theorem energy_covariance_eq_variance (β : ℝ) (E : A → ℝ) :
    gibbsCovariance β E E E = finiteGibbsEnergyVariance β E := by
  rw [gibbsCovariance_moment]
  simp only [gibbsMean, finiteGibbsEnergyVariance, finiteGibbsEnergyMean, pow_two]

theorem energyMean_hasDerivAt (β : ℝ) (E : A → ℝ) :
    HasDerivAt (fun b => finiteGibbsEnergyMean b E) (-finiteGibbsEnergyVariance β E) β := by
  change HasDerivAt (fun b => gibbsMean b E E) (-finiteGibbsEnergyVariance β E) β
  apply (hasDerivAt_gibbsMean_temperature E E β).congr_deriv
  rw [energy_covariance_eq_variance]

/-- Literal second derivative of the logarithmic partition function. -/
theorem logPartition_second_derivative (β : ℝ) (E : A → ℝ) :
    deriv (deriv (fun b => Real.log (finiteGibbsPartition b E))) β =
      finiteGibbsEnergyVariance β E := by
  have hfun : deriv (fun b => Real.log (finiteGibbsPartition b E)) =
      fun b => -finiteGibbsEnergyMean b E := by
    funext b
    exact (hasDerivAt_log_finiteGibbsPartition E b).deriv
  rw [hfun]
  have hd : HasDerivAt (fun b => -finiteGibbsEnergyMean b E)
      (finiteGibbsEnergyVariance β E) β := by
    apply (energyMean_hasDerivAt β E).neg.congr_deriv
    ring
  exact hd.deriv

/-- Heat capacity is defined by differentiating mean energy in physical temperature. -/
def canonicalHeatCapacity (E : A → ℝ) (T : ℝ) : ℝ :=
  deriv (fun t => finiteGibbsEnergyMean t⁻¹ E) T

theorem canonicalMean_temperature_hasDerivAt (u : ℝ) (E : A → ℝ) :
    HasDerivAt (fun t => finiteGibbsEnergyMean t⁻¹ E)
      (finiteGibbsEnergyVariance (Real.exp u)⁻¹ E / Real.exp u ^ 2) (Real.exp u) := by
  apply ((energyMean_hasDerivAt (Real.exp u)⁻¹ E).comp (Real.exp u)
    ((hasDerivAt_id (Real.exp u)).inv (Real.exp_ne_zero u))).congr_deriv
  dsimp
  ring

/-- The temperature-squared fluctuation law holds for every finite Hamiltonian. -/
theorem canonicalHeatCapacity_eq_variance (u : ℝ) (E : A → ℝ) :
    canonicalHeatCapacity E (Real.exp u) =
      finiteGibbsEnergyVariance (Real.exp u)⁻¹ E / Real.exp u ^ 2 :=
  (canonicalMean_temperature_hasDerivAt u E).deriv

theorem canonicalHeatCapacity_nonneg (u : ℝ) (E : A → ℝ) :
    0 ≤ canonicalHeatCapacity E (Real.exp u) := by
  rw [canonicalHeatCapacity_eq_variance, ← energy_covariance_eq_variance]
  exact div_nonneg (gibbsCovariance_self_nonneg _ _ _) (sq_nonneg _)

/-- A vanishing heat capacity means every energy level equals the thermal mean. -/
theorem canonicalHeatCapacity_zero_iff (u : ℝ) (E : A → ℝ) :
    canonicalHeatCapacity E (Real.exp u) = 0 ↔
      ∀ a, E a = finiteGibbsEnergyMean (Real.exp u)⁻¹ E := by
  rw [canonicalHeatCapacity_eq_variance, div_eq_zero_iff]
  simp only [pow_ne_zero 2 (Real.exp_ne_zero u), or_false]
  rw [← energy_covariance_eq_variance, gibbsCovariance_self_eq_zero_iff]
  rfl

/-- The two-copy Liouvillian gap moment measures canonical heat capacity exactly. -/
theorem thermalGapMoment_eq_heatCapacity (u : ℝ) (E : A → ℝ) :
    thermalGapMoment (finiteGibbsProductGapIntensity (Real.exp u)⁻¹ E) E 2 =
      2 * Real.exp u ^ 2 * canonicalHeatCapacity E (Real.exp u) := by
  rw [thermalGapMoment_finiteGibbsProduct_two_eq_two_mul_energyVariance,
    canonicalHeatCapacity_eq_variance]
  field_simp

/-- Heat capacity determines the slope of the existing finite heat-trace spectral dimension. -/
theorem heatSpectralDimension_slope_heatCapacity (u : ℝ) (E : A → ℝ) :
    Real.exp u * deriv (finiteHeatSpectralDimension E) (Real.exp u)⁻¹ =
      2 * Real.exp u * finiteGibbsEnergyMean (Real.exp u)⁻¹ E -
        2 * Real.exp u ^ 2 * canonicalHeatCapacity E (Real.exp u) := by
  rw [(hasDerivAt_finiteHeatSpectralDimension E (Real.exp u)⁻¹).deriv,
    energy_covariance_eq_variance, canonicalHeatCapacity_eq_variance]
  change Real.exp u * (2 * finiteGibbsEnergyMean (Real.exp u)⁻¹ E -
      2 * (Real.exp u)⁻¹ * finiteGibbsEnergyVariance (Real.exp u)⁻¹ E) = _
  field_simp

#print axioms logPartition_second_derivative
#print axioms canonicalHeatCapacity_zero_iff
#print axioms thermalGapMoment_eq_heatCapacity
#print axioms heatSpectralDimension_slope_heatCapacity

end GaloisForLFunctions.HTGeometry.Thermodynamics
