import GaloisForLFunctions.HTGeometry.ClockPeriodCommensurabilityBoundary

/-!
# Realizations of the clock-period interfaces

Rational multiples of one nonzero direction are rationally commensurable, and the pair `1, i` has a
nonreal ratio.  The two interfaces are therefore both realized, on families that the commensurability
boundary separates.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Rational multiples of a nonzero direction are commensurable. -/
theorem rationallyCommensurablePeriods_ratMul {ι : Type*} (q : ι → ℚ) {Ω : ℂ} (hΩ : Ω ≠ 0) :
    RationallyCommensurablePeriods (fun i => (q i : ℂ) * Ω) :=
  ⟨Ω, hΩ, fun i => ⟨q i, rfl⟩⟩

/-- The pair `1, i` has a nonreal period ratio. -/
theorem hasNonrealPeriodRatio_one_I :
    HasNonrealPeriodRatio (![1, Complex.I] : Fin 2 → ℂ) := by
  refine ⟨0, 1, ?_, ?_⟩
  · simp
  · simp

end GaloisForLFunctions.HTGeometry
