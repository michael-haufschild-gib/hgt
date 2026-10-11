import GaloisForLFunctions.RHTower.WeilLogShiftRawPotential
import GaloisForLFunctions.RHTower.WeilLogShiftRawCouplingIntegrability

/-! Exact raw transport cost, with an attaining coupling and an attaining Lipschitz potential. -/

open MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

theorem finiteWeilCanonicalRawLipschitzDual_eq_gap (r k : ℕ) :
    finiteWeilCanonicalRawLipschitzDual r k = finiteWeilCanonicalRawFluctuationGap r k := by
  apply le_antisymm (finiteWeilCanonicalRawLipschitzDual_le_gap r k)
  have h := le_ciSup (finiteWeilCanonicalRawLipschitzDual_bddAbove r k)
    (⟨finiteWeilCanonicalRawPotential r k, finiteWeilCanonicalRawPotential_lipschitz r k⟩ :
      {f : ℝ → ℝ // LipschitzWith 1 f})
  change (∫ x, finiteWeilCanonicalRawPotential r k x ∂(finiteWeilCanonicalRawIndexLaw r k : Measure ℝ)) -
    (∫ x, finiteWeilCanonicalRawPotential r k x ∂(finiteWeilCanonicalRawCorrectionLaw r k : Measure ℝ)) ≤
      finiteWeilCanonicalRawLipschitzDual r k at h
  rw [finiteWeilCanonicalRawPotential_integral_gap] at h
  exact h

theorem finiteWeilCanonicalRawWasserstein_eq_gap (r k : ℕ) :
    finiteWeilCanonicalRawWasserstein r k = finiteWeilCanonicalRawFluctuationGap r k := by
  apply le_antisymm (finiteWeilCanonicalRawWasserstein_le_gap r k)
  rw [← finiteWeilCanonicalRawLipschitzDual_eq_gap]
  exact finiteWeilCanonicalRawLipschitzDual_le_wasserstein r k

theorem finiteWeilCanonicalRawWasserstein_eq_lipschitzDual (r k : ℕ) :
    finiteWeilCanonicalRawWasserstein r k = finiteWeilCanonicalRawLipschitzDual r k := by
  rw [finiteWeilCanonicalRawWasserstein_eq_gap, finiteWeilCanonicalRawLipschitzDual_eq_gap]

theorem finiteWeilCanonicalRawCoupling_optimal (r k : ℕ) :
    (∫ p, dist p.1 p.2 ∂(finiteWeilCanonicalRawCoupling r k : Measure (ℝ × ℝ))) =
      finiteWeilCanonicalRawWasserstein r k := by
  rw [finiteWeilCanonicalRawCoupling_cost, finiteWeilCanonicalRawWasserstein_eq_gap]

theorem finiteWeilCanonicalRawPotential_attains_dual (r k : ℕ) :
    (∫ x, finiteWeilCanonicalRawPotential r k x ∂(finiteWeilCanonicalRawIndexLaw r k : Measure ℝ)) -
      (∫ x, finiteWeilCanonicalRawPotential r k x ∂(finiteWeilCanonicalRawCorrectionLaw r k : Measure ℝ)) =
        finiteWeilCanonicalRawLipschitzDual r k := by
  rw [finiteWeilCanonicalRawPotential_integral_gap, finiteWeilCanonicalRawLipschitzDual_eq_gap]

theorem finiteWeilCanonicalRawGap_le_coupling_cost (r k : ℕ)
    (π : finiteWeilCanonicalRawCouplingSpace r k) :
    finiteWeilCanonicalRawFluctuationGap r k ≤ ∫ p, dist p.1 p.2 ∂π.val := by
  rw [← finiteWeilCanonicalRawLipschitzDual_eq_gap]
  exact finiteWeilCanonicalRawLipschitzDual_le_coupling_cost r k π

end RHTower
