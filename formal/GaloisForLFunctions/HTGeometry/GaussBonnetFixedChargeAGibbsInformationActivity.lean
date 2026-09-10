import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsEntropyExpansion

/-!
# Shared zero and positivity classes for Gibbs information observables

The existing global collision/information inequalities identify exactly when
relative entropy and squared Hellinger distance vanish or remain positive.
These identities retain the immediately erased Gibbs inputs in the limit theory.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Squared Hellinger distance and collision excess have exactly the same zero set. -/
theorem egbFixedChargeAGibbsHellingerSquared_zero_iff_collision (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    egbFixedChargeAGibbsHellingerSquared n m β E = 0 ↔
      egbFixedChargeAGibbsCollisionExcess n m β E = 0 := by
  have hc := egbFixedChargeAGibbsCollisionExcess_nonneg n m β E
  have hh : 0 ≤ egbFixedChargeAGibbsHellingerSquared n m β E := by
    unfold egbFixedChargeAGibbsHellingerSquared
    exact sq_nonneg _
  have hl : egbFixedChargeAGibbsCollisionExcess n m β E ≤
      4 * egbFixedChargeAGibbsHellingerSquared n m β E :=
    egbFixedChargeAGibbsCollisionExcess_hellinger_lower n m β E
  have hu : egbFixedChargeAGibbsHellingerSquared n m β E ≤
      egbFixedChargeAGibbsEntropyDeficit n m β E :=
    egbFixedChargeAGibbsEntropyDeficit_hellinger_lower n m β E
  have hd := egbFixedChargeAGibbsEntropyDeficit_collision_upper n m β E
  constructor
  · intro h
    rw [h, mul_zero] at hl
    exact le_antisymm hl hc
  · intro h
    rw [h, mul_zero] at hd
    exact le_antisymm (hu.trans hd) hh

/-- Positive Hellinger distinguishability is equivalent to positive collision excess. -/
theorem egbFixedChargeAGibbsHellingerSquared_pos_iff_collision (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    0 < egbFixedChargeAGibbsHellingerSquared n m β E ↔
      0 < egbFixedChargeAGibbsCollisionExcess n m β E := by
  have hc := egbFixedChargeAGibbsCollisionExcess_nonneg n m β E
  have hl : egbFixedChargeAGibbsCollisionExcess n m β E ≤
      4 * egbFixedChargeAGibbsHellingerSquared n m β E :=
    egbFixedChargeAGibbsCollisionExcess_hellinger_lower n m β E
  constructor
  · intro h
    have hz : egbFixedChargeAGibbsCollisionExcess n m β E ≠ 0 := by
      intro h0
      have hh0 := (egbFixedChargeAGibbsHellingerSquared_zero_iff_collision n m β E).mpr h0
      linarith
    exact lt_of_le_of_ne hc (by intro he; exact hz he.symm)
  · intro h
    linarith

/-- Positive relative information is equivalent to positive collision excess. -/
theorem egbFixedChargeAGibbsEntropyDeficit_pos_iff_collision (n m : ℕ) (β : ℝ)
    (E : Fin (2 ^ (n + 3)) → ℝ) :
    0 < egbFixedChargeAGibbsEntropyDeficit n m β E ↔
      0 < egbFixedChargeAGibbsCollisionExcess n m β E := by
  have hc := egbFixedChargeAGibbsCollisionExcess_nonneg n m β E
  have hd := egbFixedChargeAGibbsEntropyDeficit_nonneg n m β E
  have hl := egbFixedChargeAGibbsEntropyDeficit_collision_lower n m β E
  have hu := egbFixedChargeAGibbsEntropyDeficit_collision_upper n m β E
  constructor
  · intro h
    have hz : egbFixedChargeAGibbsCollisionExcess n m β E ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hu
      linarith
    exact lt_of_le_of_ne hc (by intro he; exact hz he.symm)
  · intro h
    linarith

end
end GaloisForLFunctions.HTGeometry
