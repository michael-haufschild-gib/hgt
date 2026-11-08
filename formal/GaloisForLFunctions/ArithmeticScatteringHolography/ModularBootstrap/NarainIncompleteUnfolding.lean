import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPartitionStripBounds
import GaloisForLFunctions.RHTower.EisensteinTruncatedRowSum
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

/-!
# Unfolding the actual incomplete Narain overlap

Absolute strip convergence controls the translated norm integrals.
Modularity identifies the translated seed series, and Bochner unfolding
retains the exact factor two from primitive-row signs.
-/

open Complex RHTower UpperHalfPlane ModularGroup EisensteinSeries Set Filter MeasureTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Modularity identifies the translated seed sum with the truncated row overlap. -/
theorem narainIncompleteSeed_rowSum (ρ σ : D4BMUpperHalfPlaneCoordinate)
    (s : ℂ) (T : ℝ) (τ : UpperHalfPlane) :
    (∑' v : gammaSet 1 1 0, narainIncompleteSeed ρ σ s T (gammaSetMatrix v • τ)) =
      truncatedRowSum s T τ * narainPartitionOnUpperHalfPlane ρ σ τ := by
  have hv (v : gammaSet 1 1 0) :
      narainIncompleteSeed ρ σ s T (gammaSetMatrix v • τ) =
        (if rowHeight v τ ≤ T then (rowHeight v τ : ℂ) ^ s else 0) *
          narainPartitionOnUpperHalfPlane ρ σ τ := by
    simp only [narainIncompleteSeed, rowHeight, narainPartitionOnUpperHalfPlane_modular]
    split_ifs <;> simp only [zero_mul]
  simp_rw [hv]
  exact tsum_mul_right

/-- Absolute strip convergence supplies summability of all translated integral norms. -/
theorem narainIncompleteSeed_translated_norm_summable
    (ρ σ : D4BMUpperHalfPlaneCoordinate) {s : ℂ} (hs : 1 < s.re) (T : ℝ) :
    Summable (fun v : gammaSet 1 1 0 => ∫ τ in fd,
      ‖narainIncompleteSeed ρ σ s T (gammaSetMatrix v • τ)‖) := by
  have hi := integrableOn_narainIncompleteSeed ρ σ hs T
  have hn := summable_fdUnfoldTerm
    (φ := fun τ => ((‖narainIncompleteSeed ρ σ s T τ‖ : ℝ) : ℂ))
    (fun n τ => by rw [narainIncompleteSeed_periodic]) hi.norm.ofReal
  have he : fdUnfoldTerm (fun τ => ((‖narainIncompleteSeed ρ σ s T τ‖ : ℝ) : ℂ)) =
      fun v => ((∫ τ in fd, ‖narainIncompleteSeed ρ σ s T (gammaSetMatrix v • τ)‖ : ℝ) : ℂ) := by
    funext v
    rw [fdUnfoldTerm]
    exact integral_ofReal
  rw [he] at hn
  exact Complex.summable_ofReal.mp hn

/-- The truncated primitive-row overlap unfolds with its exact sign multiplicity. -/
theorem narainPartition_truncatedRowSum_unfold
    (ρ σ : D4BMUpperHalfPlaneCoordinate) {s : ℂ} (hs : 1 < s.re) (T : ℝ) :
    (∫ τ in fd, truncatedRowSum s T τ * narainPartitionOnUpperHalfPlane ρ σ τ) =
      2 * ∫ τ in modularStrip, narainIncompleteSeed ρ σ s T τ := by
  have hi := integrableOn_narainIncompleteSeed ρ σ hs T
  have hp := narainIncompleteSeed_periodic ρ σ s T
  have he : (∫ τ in fd, ∑' v : gammaSet 1 1 0,
      narainIncompleteSeed ρ σ s T (gammaSetMatrix v • τ)) =
      ∑' v : gammaSet 1 1 0, ∫ τ in fd,
        narainIncompleteSeed ρ σ s T (gammaSetMatrix v • τ) := by
    symm
    apply integral_tsum_of_summable_integral_norm
    · intro v
      exact (integrableOn_smul_set_iff (gammaSetMatrix v) _ fd).mp
        (integrableOn_smul_fd_of_periodic hp hi _)
    · exact narainIncompleteSeed_translated_norm_summable ρ σ hs T
  simp_rw [narainIncompleteSeed_rowSum] at he
  rw [he, tsum_setIntegral_fd_eq_two_mul_setIntegral_modularStrip _ hp hi]

/-- The incomplete overlap itself is integrable on the fundamental domain. -/
theorem integrableOn_narainPartition_truncatedRowSum
    (ρ σ : D4BMUpperHalfPlaneCoordinate) {s : ℂ} (hs : 1 < s.re) (T : ℝ) :
    IntegrableOn (fun τ => truncatedRowSum s T τ * narainPartitionOnUpperHalfPlane ρ σ τ) fd := by
  have hi := integrableOn_narainIncompleteSeed ρ σ hs T
  have hp := narainIncompleteSeed_periodic ρ σ s T
  have h := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (fun v : gammaSet 1 1 0 => (integrableOn_smul_set_iff (gammaSetMatrix v) _ fd).mp
      (integrableOn_smul_fd_of_periodic hp hi _))
    (narainIncompleteSeed_translated_norm_summable ρ σ hs T)
  simpa only [IntegrableOn, narainIncompleteSeed_rowSum] using h

#print axioms narainIncompleteSeed_translated_norm_summable
#print axioms narainPartition_truncatedRowSum_unfold
#print axioms integrableOn_narainPartition_truncatedRowSum
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
