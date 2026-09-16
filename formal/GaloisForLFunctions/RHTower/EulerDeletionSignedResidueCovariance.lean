import GaloisForLFunctions.RHTower.EulerDeletionWeightedResidueProjection
import GaloisForLFunctions.RHTower.EulerDeletionResidueMartingalePhysicalBridge
import GaloisForLFunctions.RHTower.EulerDeletionStretchedEnergy
import GaloisForLFunctions.RHTower.EulerDeletionMobiusPrimitiveEnergy

noncomputable section
set_option autoImplicit false
open Finset Filter Topology
open scoped BigOperators
namespace RHTower.DeletionSignedResidueCovariance

/-- The exact finite signed covariance exposed by chronological Euler deletion. -/
def energy (N : ℕ) : ℝ :=
  ∑ r ∈ range (DeletionResidueMartingale.clock N),
    DeletionResidueMartingale.cellMeasure.real
      (DeletionResidueMartingale.historyFibre N r) *
      (∑ i ∈ range N, ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
        DeletionResidueMartingale.weightedResidueQuotient (i + 1) i
          (r % DeletionResidueMartingale.clock i)) ^ 2

theorem energy_eq_predictableDrift_norm_sq (N : ℕ) :
    energy N = ‖DeletionResidueMartingale.predictableDrift N‖ ^ 2 := by
  symm
  exact DeletionResidueMartingale.predictableDrift_norm_sq_eq_signedResidueCovariance N

/-- The exact signed covariance is within the cutoff-independent innovation
budget of the full modular source energy. -/
theorem energy_le_two_modular_norm_sq_add_four (N : ℕ) :
    energy N ≤ 2 * ‖bdMobiusModularApproximantVec N‖ ^ 2 + 4 := by
  have hgap := DeletionResidueMartingalePhysical.modular_norm_drift_gap N
  rw [sq_abs] at hgap
  rw [energy_eq_predictableDrift_norm_sq]
  nlinarith [sq_nonneg
    (‖DeletionResidueMartingale.predictableDrift N‖ -
      2 * ‖bdMobiusModularApproximantVec N‖)]

/-- The existing unconditional stretched-exponential source ceiling transfers
without loss of source fidelity to the exact signed covariance obstruction. -/
theorem stretched_rate : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
    energy N ≤ C * (N : ℝ) * DeletionStretchedEnergy.saving N + 4 := by
  obtain ⟨C, hC, hsource⟩ := DeletionStretchedEnergy.modular_norm_sq_rate
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hsource] with N hN
  calc
    _ ≤ 2 * ‖bdMobiusModularApproximantVec N‖ ^ 2 + 4 :=
      energy_le_two_modular_norm_sq_add_four N
    _ ≤ 2 * (C * (N : ℝ) * DeletionStretchedEnergy.saving N) + 4 := by
      gcongr
    _ = _ := by ring

/-- The modular source energy is controlled by the exact signed residue covariance,
up to the cutoff-independent innovation budget. -/
theorem modular_norm_sq_le_two_energy_add_four (N : ℕ) :
    ‖bdMobiusModularApproximantVec N‖ ^ 2 ≤ 2 * energy N + 4 := by
  have hgap := DeletionResidueMartingalePhysical.modular_norm_drift_gap N
  rw [sq_abs] at hgap
  rw [energy_eq_predictableDrift_norm_sq]
  nlinarith [sq_nonneg
    (‖bdMobiusModularApproximantVec N‖ -
      2 * ‖DeletionResidueMartingale.predictableDrift N‖)]

/-- A cofinal polylogarithmic bound for the exact signed covariance closes the
EDQ route by forcing every nontrivial zeta zero onto the critical line. -/
theorem riemannHypothesis_of_cofinally_log_bounded_energy
    (henergy : ∃ q : ℕ, ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      energy N ≤ B * Real.log (N : ℝ) ^ q) : RiemannHypothesis := by
  apply DeletionMobiusPrimitive.riemannHypothesis_of_cofinally_log_bounded_modular_norm
  obtain ⟨q, B, hB⟩ := henergy
  refine ⟨q, 2 * B + 4, fun K => ?_⟩
  obtain ⟨N, hKN, hN⟩ := hB (max K 3)
  refine ⟨N, (le_max_left _ _).trans hKN, ?_⟩
  have hN3 : 3 ≤ N := (le_max_right _ _).trans hKN
  have hNpos : 0 < (N : ℝ) := by positivity
  have hlog : 1 ≤ Real.log (N : ℝ) :=
    (Real.le_log_iff_exp_le hNpos).mpr <|
      Real.exp_one_lt_three.le.trans (by exact_mod_cast hN3)
  have hlogpow : 1 ≤ Real.log (N : ℝ) ^ q := one_le_pow₀ hlog
  calc
    ‖bdMobiusModularApproximantVec N‖ ^ 2 ≤ 2 * energy N + 4 :=
      modular_norm_sq_le_two_energy_add_four N
    _ ≤ 2 * (B * Real.log (N : ℝ) ^ q) + 4 := by gcongr
    _ ≤ (2 * B + 4) * Real.log (N : ℝ) ^ q := by nlinarith

end RHTower.DeletionSignedResidueCovariance
