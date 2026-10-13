import GaloisForLFunctions.RHTower.PaperPrimeArchAbsoluteCurrent

/-! # Opposite source orders with identical observations and ideal cost

The actual absolute current and its negative are explicitly distinguished by
positivity, while every full physical-hull norm observation and ideal cost agree.
-/

namespace RHTower.PaperPrimeArch
noncomputable section
open GaloisForLFunctions.HTGeometry
open scoped ENNReal

theorem negativeAbsoluteOperator_observation (a : Height) (x : Space) :
    l2PhysicalObservation (-absoluteOperator a) x = l2PhysicalObservation (absoluteOperator a) x := by
  simp only [l2PhysicalObservation, neg_apply, norm_neg]

theorem negativeAbsoluteOperator_not_positive (a : Height) : ¬ (-absoluteOperator a).IsPositive := by
  intro h
  have hp : 0 ≤ absoluteOperator a :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr (absoluteOperator_positive a)
  have hn : absoluteOperator a ≤ 0 :=
    neg_nonneg.mp ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr h)
  exact absoluteOperator_ne_zero a (le_antisymm hn hp)

theorem negativeAbsoluteOperator_not_compact (a : Height) : ¬ IsCompactOperator (-absoluteOperator a) := by
  intro h
  apply absoluteOperator_not_compact a
  have hn : IsCompactOperator (fun x : Space => -((-absoluteOperator a) x)) := h.neg
  simpa only [neg_apply, neg_neg] using hn

theorem negativeAbsoluteOperator_traceCost (a : Height) :
    compactOperatorTraceCost Space (-absoluteOperator a) = ∞ := by
  rw [compactOperatorTraceCost_eq, if_neg (negativeAbsoluteOperator_not_compact a)]

theorem positive_negative_same_observations (a : Height) :
    (absoluteOperator a).IsPositive ∧ ¬ (-absoluteOperator a).IsPositive ∧
    (∀ x, l2PhysicalObservation (absoluteOperator a) x = l2PhysicalObservation (-absoluteOperator a) x) ∧
    compactOperatorTraceCost Space (absoluteOperator a) = ∞ ∧
    compactOperatorTraceCost Space (-absoluteOperator a) = ∞ :=
  ⟨absoluteOperator_positive a, negativeAbsoluteOperator_not_positive a,
    fun x => (negativeAbsoluteOperator_observation a x).symm,
    absoluteOperator_traceCost a, negativeAbsoluteOperator_traceCost a⟩

end
end RHTower.PaperPrimeArch
