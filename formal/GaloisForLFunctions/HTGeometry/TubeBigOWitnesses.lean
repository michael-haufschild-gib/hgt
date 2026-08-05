import GaloisForLFunctions.HTGeometry.RatApproxDatum

/-!
# Tube decay data exist

Tube decay asks for a power bound on a vertical strip beyond some height.  The zero function has it
at every order with constant zero, and every globally bounded function has it at order zero — so
the rational-approximation datum is not vacuous, and its content is the positive order.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The zero function decays in every tube at every order. -/
theorem isTubeBigO_zero (M : ℝ) (N : ℕ) : IsTubeBigO M N (fun _ => 0) := by
  refine ⟨0, 0, fun σ t _ _ _ => ?_⟩
  simp

/-- **A globally bounded function has tube decay at order zero.** -/
theorem isTubeBigO_of_bounded {M C : ℝ} {f : ℂ → ℂ} (hC : ∀ z, ‖f z‖ ≤ C) :
    IsTubeBigO M 0 f := by
  refine ⟨C, 0, fun σ t _ _ _ => ?_⟩
  rw [pow_zero, div_one]
  exact hC _

end GaloisForLFunctions.HTGeometry
