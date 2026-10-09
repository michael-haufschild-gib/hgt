import GaloisForLFunctions.HTGeometry.PaperNativeInvariantLocalization
import GaloisForLFunctions.HTGeometry.PaperStabilizedPolynomialClock

/-!
# Which rational extensions preserve the stabilized clock?

For the literal source polynomial, the native quotient-rule clock on a
principal localization is locally nilpotent exactly when its denominator
is a clock invariant. This includes every complementary coordinate and
excludes the complement of every scalar level of the clock coordinate.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate MvPolynomial

noncomputable section

/-- The existing native quotient-rule extension of the actual stabilized clock. -/
def paperStabilizedLocalizedClock (a : R 5) :
    Derivation ℂ (Localization.Away a) (Localization.Away a) :=
  paperNativeLocalization (Submonoid.powers a) paperStabilizedClock

/-- No extra denominator or nilpotence assumptions: this is an exact classification. -/
theorem paperStabilizedLocalizedClock_iff (a : R 5) :
    IsLocallyNilpotent (paperStabilizedLocalizedClock a) ↔ paperStabilizedClock a = 0 :=
  paperNativeAway_locallyNilpotent_iff paperStabilizedClock
    paperStabilizedClock_locallyNilpotent a

/-- Multiplicative cancellation cannot produce a nonzero invariant. -/
theorem paperStabilizedClock_product_iff (a b : R 5) :
    paperStabilizedClock (a * b) = 0 ↔
      a = 0 ∨ b = 0 ∨ paperStabilizedClock a = 0 ∧ paperStabilizedClock b = 0 := by
  constructor
  · intro hab
    by_cases ha : a = 0
    · exact Or.inl ha
    by_cases hb : b = 0
    · exact Or.inr (Or.inl hb)
    exact Or.inr (Or.inr (lnd_factorial_closure paperStabilizedClock
      paperStabilizedClock_locallyNilpotent ha hb hab))
  · rintro (rfl | rfl | ⟨ha, hb⟩)
    · simp
    · simp
    · simp [Derivation.leibniz, ha, hb]

/-- The same boundary for any product denominator, including zero factors. -/
theorem paperStabilizedLocalizedClock_product_iff (a b : R 5) :
    IsLocallyNilpotent (paperStabilizedLocalizedClock (a * b)) ↔
      a = 0 ∨ b = 0 ∨ paperStabilizedClock a = 0 ∧ paperStabilizedClock b = 0 := by
  rw [paperStabilizedLocalizedClock_iff, paperStabilizedClock_product_iff]

/-- Inverting any complementary coordinate preserves local nilpotence. -/
theorem paperStabilizedLocalizedClock_complement (i : Fin 4) :
    IsLocallyNilpotent (paperStabilizedLocalizedClock
      (paperStabilizedCoordinateEquiv.symm (X i.succ))) :=
  (paperStabilizedLocalizedClock_iff _).mpr (paperStabilizedClock_complementary_constant i)

/-- Deleting any scalar clock level destroys local nilpotence of its extension. -/
theorem paperStabilizedLocalizedClock_level_not_nilpotent (t : ℂ) :
    ¬ IsLocallyNilpotent (paperStabilizedLocalizedClock (stabilize f - C t)) := by
  rw [paperStabilizedLocalizedClock_iff]
  have ht : paperStabilizedClock (C t : R 5) = 0 :=
    paperStabilizedClock.map_algebraMap t
  rw [map_sub, paperStabilizedClock_slice, ht, sub_zero]
  exact one_ne_zero

/-- In particular, inversion of the clock coordinate itself destroys local nilpotence. -/
theorem paperStabilizedLocalizedClock_slice_not_nilpotent :
    ¬ IsLocallyNilpotent (paperStabilizedLocalizedClock (stabilize f)) := by
  rw [paperStabilizedLocalizedClock_iff, paperStabilizedClock_slice]
  exact one_ne_zero

/-- Explicit nontermination exists on the complement of every scalar level. -/
theorem paperStabilizedLocalizedClock_level_nonterminating (t : ℂ) :
    ∃ a : Localization.Away (stabilize f - C t), ∀ n : ℕ,
      ((paperStabilizedLocalizedClock (stabilize f - C t))^[n]) a ≠ 0 := by
  have h := paperStabilizedLocalizedClock_level_not_nilpotent t
  unfold IsLocallyNilpotent at h
  push Not at h
  exact h

end

end GaloisForLFunctions.HTGeometry
