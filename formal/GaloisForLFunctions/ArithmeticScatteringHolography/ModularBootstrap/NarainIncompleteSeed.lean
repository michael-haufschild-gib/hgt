import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainModularity
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPartitionRegularity
import GaloisForLFunctions.HTGeometry.ModularStripLIntegralUnfolding

/-!
# The truncated Narain seed

Modularity gives translation invariance of the actual height-truncated seed.
Nonnegative primitive-row unfolding retains the exact two-sign multiplicity.
-/

open Complex RHTower UpperHalfPlane ModularGroup Set Filter MeasureTheory
open scoped MatrixGroups ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The height-truncated Narain seed for incomplete Eisenstein unfolding. -/
def narainIncompleteSeed (ρ σ : D4BMUpperHalfPlaneCoordinate) (s : ℂ) (T : ℝ)
    (τ : UpperHalfPlane) : ℂ :=
  if τ.im ≤ T then (τ.im : ℂ) ^ s * narainPartitionOnUpperHalfPlane ρ σ τ else 0

/-- Integer translations preserve both the source and its height cutoff. -/
theorem narainIncompleteSeed_periodic (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (s : ℂ) (T : ℝ) (n : ℤ) (τ : UpperHalfPlane) :
    narainIncompleteSeed ρ σ s T (ModularGroup.T ^ n • τ) = narainIncompleteSeed ρ σ s T τ := by
  simp only [narainIncompleteSeed, ModularGroup.im_T_zpow_smul,
    narainPartitionOnUpperHalfPlane_modular]

/-- The actual truncated seed is measurable on the upper half-plane. -/
theorem measurable_narainIncompleteSeed (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (s : ℂ) (T : ℝ) : Measurable (narainIncompleteSeed ρ σ s T) := by
  have hp : Measurable (narainPartitionOnUpperHalfPlane ρ σ) :=
    (measurable_narainPartition ρ σ).comp
      (UpperHalfPlane.continuous_re.measurable.prodMk UpperHalfPlane.continuous_im.measurable)
  unfold narainIncompleteSeed
  apply Measurable.ite (measurableSet_le UpperHalfPlane.continuous_im.measurable measurable_const)
  · exact (by fun_prop : Measurable (fun τ : UpperHalfPlane => (τ.im : ℂ) ^ s)).mul hp
  · exact measurable_const

/-- Nonnegative unfolding retains the exact factor from the two primitive-row signs. -/
theorem narainIncompleteSeed_norm_unfold (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (s : ℂ) (T : ℝ) :
    (∑' p : EisensteinSeries.gammaSet 1 1 0, ∫⁻ τ in fd,
      ENNReal.ofReal ‖narainIncompleteSeed ρ σ s T (gammaSetMatrix p • τ)‖) =
        2 * ∫⁻ τ in modularStrip, ENNReal.ofReal ‖narainIncompleteSeed ρ σ s T τ‖ := by
  apply tsum_lintegral_fd_eq_two_mul_lintegral_strip
    (g := fun τ => ENNReal.ofReal ‖narainIncompleteSeed ρ σ s T τ‖)
  intro n τ
  rw [narainIncompleteSeed_periodic]

#print axioms measurable_narainIncompleteSeed
#print axioms narainIncompleteSeed_norm_unfold
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
