import GaloisForLFunctions.HTGeometry.ClockNullFrameReduction

/-!
# The null frame is surjective

The characteristic-probe and equivalence laws are conditioned on the null coordinates of an event
landing in a given region.  The corpus already produces, for each null point, an event whose two
null coordinates are its two components; assembling those into a function equality makes the null
frame surjective, so **every region containing a point is reached**.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The null frame is surjective.** -/
theorem nullFrame_surjective : Function.Surjective nullFrame := by
  intro p
  obtain ⟨x, h0, h1⟩ := exists_event_of_nullPoint p
  refine ⟨x, ?_⟩
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-- Hence every region containing a null point is reached by an event. -/
theorem exists_nullFrame_mem {W : Set (Fin (1 + 1) → ℝ)} {p : Fin (1 + 1) → ℝ} (hp : p ∈ W) :
    ∃ x : Fin (1 + 1) → ℝ, nullFrame x ∈ W := by
  obtain ⟨x, hx⟩ := nullFrame_surjective p
  exact ⟨x, by rw [hx]; exact hp⟩

/-- The null frame reaches every nonempty region. -/
theorem exists_nullFrame_mem_of_nonempty {W : Set (Fin (1 + 1) → ℝ)} (hW : W.Nonempty) :
    ∃ x : Fin (1 + 1) → ℝ, nullFrame x ∈ W := by
  obtain ⟨p, hp⟩ := hW
  exact exists_nullFrame_mem hp

end GaloisForLFunctions.HTGeometry
