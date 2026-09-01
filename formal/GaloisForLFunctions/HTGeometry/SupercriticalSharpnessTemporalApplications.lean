import GaloisForLFunctions.HTGeometry.SupercriticalSharpnessMechanisms
import GaloisForLFunctions.HTGeometry.ObserverTemporalDimensionCascadeLaw

/-!
# Supercritical-sharpness mechanisms for observer-time dimension

Closed sequential-touch alternatives from arXiv:2603.03257 for spectral-jet resolution.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Across `t` new spectral-jet orders, observer-time dimension either gains at least `t` or one
order exposes no new rational temporal direction. -/
theorem temporalDimension_grows_or_exists_stall
    {I : Type*} [Fintype I] (jet : ℕ → I → ℂ) (N t : ℕ) :
    temporalDimension jet N + t ≤ temporalDimension jet (N + t) ∨
      ∃ i < t, temporalDimension jet (N + (i + 1)) = temporalDimension jet (N + i) := by
  have hmono : Monotone (fun i ↦ temporalDimension jet (N + i)) := by
    intro i j hij
    exact temporalDimension_mono jet (Nat.add_le_add_left hij N)
  simpa [Nat.add_assoc] using
    (accumulates_touches_or_exists_stall (fun i ↦ temporalDimension jet (N + i)) t hmono)

/-- A nonempty finite spectrum necessarily has a derivative order below its cardinality that
exposes no new temporal direction. -/
theorem exists_temporalDimension_stall_before_card
    {I : Type*} [Fintype I] [Nonempty I] (jet : ℕ → I → ℂ) :
    ∃ i < Fintype.card I, temporalDimension jet (i + 1) = temporalDimension jet i := by
  rcases temporalDimension_grows_or_exists_stall jet 0 (Fintype.card I) with hgrow | hstall
  · have hupper := temporalDimension_le_card_sub_one jet (Fintype.card I)
    have hcard : 0 < Fintype.card I := Fintype.card_pos
    rw [temporalDimension_zero] at hgrow
    simp only [zero_add] at hgrow
    omega
  · simpa using hstall

/-- At the forced temporal-dimension stall, persistent rational-relation rank also stays fixed.
Thus the nonproductive derivative order has an exact algebraic certificate. -/
theorem exists_constraintFinrank_stall_before_card
    {I : Type*} [Fintype I] [Nonempty I] (jet : ℕ → I → ℂ) :
    ∃ i < Fintype.card I,
      Module.finrank ℚ (rationalSpectralConstraintSpace jet (i + 1)) =
        Module.finrank ℚ (rationalSpectralConstraintSpace jet i) := by
  obtain ⟨i, hi, hstall⟩ := exists_temporalDimension_stall_before_card jet
  refine ⟨i, hi, ?_⟩
  have hcurrent := temporalDimension_add_constraintFinrank jet i
  have hnext := temporalDimension_add_constraintFinrank jet (i + 1)
  omega

end GaloisForLFunctions.HTGeometry
