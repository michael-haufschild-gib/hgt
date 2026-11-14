import GaloisForLFunctions.HTGeometry.Thermodynamics.FiniteCanonicalHeat
import GaloisForLFunctions.HTGeometry.Thermodynamics.EndpointSourceSwitch
import GaloisForLFunctions.HTGeometry.InformationCapacityReserve
import GaloisForLFunctions.HTGeometry.Thermofield.EntropyApplications

/-!
# Source coexistence for finite Gibbs theories

The generalized Clapeyron identity of arXiv:2611.16364 applies to the
actual finite Gibbs free energies. Its entropy is the corpus Shannon
entropy, and its slope also measures the difference in information
reserves after accounting for the two state-space dimensions.

The source transition concerns classical minimization between the two
theory free energies. It does not identify that minimum with a statistical
sum over the theories.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.Thermodynamics
open _root_.HTGeometry TraceDynamics
variable {n m : ℕ}

def finiteThermalFreeEnergy (E : Fin (n + 1) → ℝ) (T : ℝ) : ℝ :=
  -(T * Real.log (finiteGibbsPartition T⁻¹ E))

/-- Differentiating the finite trace gives minus the existing Shannon entropy. -/
theorem finiteThermalFreeEnergy_hasDerivAt (u : ℝ) (E : Fin (n + 1) → ℝ) :
    HasDerivAt (finiteThermalFreeEnergy E)
      (-entropy (finiteGibbsStateWeight (Real.exp u)⁻¹ E)) (Real.exp u) := by
  rw [gibbsEntropy_partition_identity]
  have hlog := (hasDerivAt_log_finiteGibbsPartition E (Real.exp u)⁻¹).comp (Real.exp u)
    ((hasDerivAt_id (Real.exp u)).inv (Real.exp_ne_zero u))
  apply (((hasDerivAt_id (Real.exp u)).mul hlog).neg).congr_deriv
  change -(1 * Real.log (finiteGibbsPartition (Real.exp u)⁻¹ E) +
    Real.exp u * (-finiteGibbsEnergyMean (Real.exp u)⁻¹ E * (-(1 : ℝ) / Real.exp u ^ 2))) = _
  field_simp

def finiteThermalSource (E₀ : Fin (n + 1) → ℝ) (E₁ : Fin (m + 1) → ℝ) (k T : ℝ) : ℝ :=
  coexistenceSource (finiteThermalFreeEnergy E₀ T) (finiteThermalFreeEnergy E₁ T) k

/-- Entropy differences determine the source needed to maintain equality of free energies. -/
theorem finiteThermalSource_hasDerivAt (u k : ℝ)
    (E₀ : Fin (n + 1) → ℝ) (E₁ : Fin (m + 1) → ℝ) :
    HasDerivAt (finiteThermalSource E₀ E₁ k)
      (-(entropy (finiteGibbsStateWeight (Real.exp u)⁻¹ E₁) -
          entropy (finiteGibbsStateWeight (Real.exp u)⁻¹ E₀)) / Real.exp k) (Real.exp u) := by
  apply (((finiteThermalFreeEnergy_hasDerivAt u E₁).sub
    (finiteThermalFreeEnergy_hasDerivAt u E₀)).div_const (Real.exp k)).congr_deriv
  ring

theorem finiteTheory_clapeyron (u k : ℝ)
    (E₀ : Fin (n + 1) → ℝ) (E₁ : Fin (m + 1) → ℝ) :
    deriv (finiteThermalSource E₀ E₁ k) (Real.exp u) =
      -(entropy (finiteGibbsStateWeight (Real.exp u)⁻¹ E₁) -
        entropy (finiteGibbsStateWeight (Real.exp u)⁻¹ E₀)) / Real.exp k :=
  (finiteThermalSource_hasDerivAt u k E₀ E₁).deriv

/-- The across-theory energy balance includes the external coupling work. -/
theorem finiteTheory_latent_energy_balance (u k : ℝ)
    (E₀ : Fin (n + 1) → ℝ) (E₁ : Fin (m + 1) → ℝ) :
    finiteGibbsEnergyMean (Real.exp u)⁻¹ E₁ - finiteGibbsEnergyMean (Real.exp u)⁻¹ E₀ =
      Real.exp u * (entropy (finiteGibbsStateWeight (Real.exp u)⁻¹ E₁) -
        entropy (finiteGibbsStateWeight (Real.exp u)⁻¹ E₀)) +
        Real.exp k * finiteThermalSource E₀ E₁ k (Real.exp u) := by
  rw [gibbsEntropy_partition_identity, gibbsEntropy_partition_identity]
  unfold finiteThermalSource coexistenceSource finiteThermalFreeEnergy
  field_simp
  ring

/-- The slope separates state-count capacity from the information reserve of each theory. -/
theorem finiteTheory_clapeyron_information_reserve (u k : ℝ)
    (E₀ : Fin (n + 1) → ℝ) (E₁ : Fin (m + 1) → ℝ) :
    deriv (finiteThermalSource E₀ E₁ k) (Real.exp u) =
      (gibbsInformationReserve (Real.exp u)⁻¹ E₁ - gibbsInformationReserve (Real.exp u)⁻¹ E₀ -
        Real.log (m + 1 : ℝ) + Real.log (n + 1 : ℝ)) / Real.exp k := by
  rw [finiteTheory_clapeyron]
  unfold gibbsInformationReserve
  ring

/-- The same slope is an actual thermofield entanglement-entropy difference. -/
theorem finiteTheory_clapeyron_entanglement (u k : ℝ)
    (E₀ : Fin (n + 1) → ℝ) (E₁ : Fin (m + 1) → ℝ) :
    deriv (finiteThermalSource E₀ E₁ k) (Real.exp u) =
      -(Thermofield.entanglementEntropy (Real.exp u)⁻¹ E₁ -
        Thermofield.entanglementEntropy (Real.exp u)⁻¹ E₀) / Real.exp k := by
  rw [Thermofield.entanglementEntropy_eq_gibbs, Thermofield.entanglementEntropy_eq_gibbs]
  exact finiteTheory_clapeyron u k E₀ E₁

/-- Heating the finite thermofield state changes entanglement at the heat-capacity rate divided by temperature. -/
theorem thermofieldEntanglement_temperature_hasDerivAt (u : ℝ) (E : Fin (n + 1) → ℝ) :
    HasDerivAt (fun T => Thermofield.entanglementEntropy T⁻¹ E)
      (canonicalHeatCapacity E (Real.exp u) / Real.exp u) (Real.exp u) := by
  have hf : (fun T : ℝ => Thermofield.entanglementEntropy T⁻¹ E) =
      fun T => Real.log (finiteGibbsPartition T⁻¹ E) + T⁻¹ * finiteGibbsEnergyMean T⁻¹ E := by
    funext T
    exact Thermofield.entanglementEntropy_partition T⁻¹ E
  rw [hf]
  have hinv := (hasDerivAt_id (Real.exp u)).inv (Real.exp_ne_zero u)
  have hlog := (hasDerivAt_log_finiteGibbsPartition E (Real.exp u)⁻¹).comp (Real.exp u) hinv
  apply (hlog.add (hinv.mul (canonicalMean_temperature_hasDerivAt u E))).congr_deriv
  rw [canonicalHeatCapacity_eq_variance]
  change (-finiteGibbsEnergyMean (Real.exp u)⁻¹ E) * (-(1 : ℝ) / Real.exp u ^ 2) +
      ((-(1 : ℝ) / Real.exp u ^ 2) * finiteGibbsEnergyMean (Real.exp u)⁻¹ E +
        (Real.exp u)⁻¹ * (finiteGibbsEnergyVariance (Real.exp u)⁻¹ E / Real.exp u ^ 2)) = _
  field_simp

theorem thermofieldEntanglement_temperature_derivative_nonneg (u : ℝ) (E : Fin (n + 1) → ℝ) :
    0 ≤ deriv (fun T => Thermofield.entanglementEntropy T⁻¹ E) (Real.exp u) := by
  rw [(thermofieldEntanglement_temperature_hasDerivAt u E).deriv]
  exact div_nonneg (canonicalHeatCapacity_nonneg u E) (Real.exp_pos u).le

theorem finiteTheory_source_transition (u a k : ℝ)
    (E₀ : Fin (n + 1) → ℝ) (E₁ : Fin (m + 1) → ℝ) :
    ¬ DifferentiableAt ℝ
      (endpointPotential (finiteThermalFreeEnergy E₀ (Real.exp u))
        (finiteThermalFreeEnergy E₁ (Real.exp u)) a k)
      (finiteThermalSource E₀ E₁ k (Real.exp u)) :=
  endpointPotential_not_differentiable _ _ _ _

#print axioms finiteTheory_clapeyron
#print axioms finiteTheory_latent_energy_balance
#print axioms finiteTheory_clapeyron_information_reserve
#print axioms finiteTheory_clapeyron_entanglement
#print axioms thermofieldEntanglement_temperature_hasDerivAt
#print axioms finiteTheory_source_transition

end GaloisForLFunctions.HTGeometry.Thermodynamics
