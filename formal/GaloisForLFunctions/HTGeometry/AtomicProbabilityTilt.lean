import GaloisForLFunctions.HTGeometry.PaperFourierLawMeasure
import Mathlib.MeasureTheory.Measure.Tilted

/-! # Exact tilting and support preservation for finite atomic laws -/

namespace GaloisForLFunctions.HTGeometry.FourierLLogL.Law

open MeasureTheory
open scoped BigOperators ENNReal

variable {α β : Type*} [Fintype α] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem atomicProbability_singleton_of_injective (P : Law α) (φ : α → β)
    (hφ : Function.Injective φ) (i : α) :
    (P.atomicProbability φ : Measure β) {φ i} = ENNReal.ofReal (P i) := by
  classical
  change (∑ j, ENNReal.ofReal (P j) • Measure.dirac (φ j)) {φ i} = _
  rw [Measure.finsetSum_apply, Finset.sum_eq_single i]
  · simp [Measure.smul_apply]
  · intro j _ hji
    have hne : φ j ≠ φ i := fun h => hji (hφ h)
    simp [Measure.smul_apply, hne]
  · simp

/-- Matching the weighted exponential at every atom realizes the target law. -/
theorem atomicProbability_tilted_eq_of_weight_exp (P Q : Law α) (φ : α → β)
    (f : β → ℝ) (hweight : ∀ i, P i * Real.exp (f (φ i)) = Q i) :
    (P.atomicProbability φ : Measure β).tilted f = (Q.atomicProbability φ : Measure β) := by
  have hZ : (∫ x, Real.exp (f x) ∂(P.atomicProbability φ : Measure β)) = 1 := by
    rw [integral_atomicProbability, Ex]
    simpa only [hweight] using Q.total
  rw [Measure.tilted, hZ]
  change (∑ i, ENNReal.ofReal (P i) • Measure.dirac (φ i)).withDensity
      (fun x => ENNReal.ofReal (Real.exp (f x) / 1)) =
    ∑ i, ENNReal.ofReal (Q i) • Measure.dirac (φ i)
  simp only [div_one, ← Measure.sum_fintype, withDensity_sum,
    withDensity_smul_measure, dirac_withDensity, smul_smul]
  congr 1
  funext i
  rw [← ENNReal.ofReal_mul (P.nonneg i), hweight i]

/-- A real exponential tilt of positive distinct atoms cannot erase a target atom. -/
theorem pos_of_atomicProbability_tilted_eq (P Q : Law α) (φ : α → β)
    (hφ : Function.Injective φ) (hP : ∀ i, 0 < P i) (f : β → ℝ)
    (heq : (P.atomicProbability φ : Measure β).tilted f =
      (Q.atomicProbability φ : Measure β)) :
    ∀ i, 0 < Q i := by
  have hac : (P.atomicProbability φ : Measure β) ≪ (Q.atomicProbability φ : Measure β) := by
    rw [← heq]
    exact absolutelyContinuous_tilted
      (integrable_atomicProbability P φ (fun x => Real.exp (f x)))
  intro i
  by_contra hpos
  have hzero : Q i = 0 := le_antisymm (le_of_not_gt hpos) (Q.nonneg i)
  have htarget : (Q.atomicProbability φ : Measure β) {φ i} = 0 := by
    rw [atomicProbability_singleton_of_injective Q φ hφ i, hzero, ENNReal.ofReal_zero]
  have hsource := hac htarget
  rw [atomicProbability_singleton_of_injective P φ hφ i] at hsource
  exact (ENNReal.ofReal_pos.mpr (hP i)).ne' hsource

end GaloisForLFunctions.HTGeometry.FourierLLogL.Law
