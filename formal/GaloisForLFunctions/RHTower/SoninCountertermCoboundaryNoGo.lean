import GaloisForLFunctions.RHTower.SoninBurnolCountertermCoboundary

/-!
# Inert counterterms are exactly the coboundaries

A counterterm assigned to aperture steps is invisible to the curvature combination precisely when
it is a difference of a potential at the two apertures.  The Burnol counterterm is of that shape,
and so is every other additive aperture assignment.

Consequently no such counterterm can restore a lower floor to the curvature channel: the channel is
unbounded below and the counterterm contributes exactly zero to it.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap

/-- A potential difference has vanishing aperture curvature. -/
theorem coboundary_apertureCurvature_eq_zero (f : ℝ → ℝ) (a b c : ℝ) :
    (f c - f a) - (f b - f a) - (f c - f b) = 0 := by ring

/-- **Classification.**  A counterterm with vanishing aperture curvature is a coboundary: it is the
difference of one fixed potential at the two apertures. -/
theorem apertureCocycle_eq_coboundary {K : ℝ → ℝ → ℝ}
    (hK : ∀ a b c : ℝ, K a c - K a b - K b c = 0) (x₀ : ℝ) (a b : ℝ) :
    K a b = K x₀ b - K x₀ a := by
  have h := hK x₀ a b
  linarith

/-- **No coboundary restores the floor.**  Adding any potential-difference counterterm to the
curvature trace leaves the packet channel unbounded below. -/
theorem not_exists_lower_bound_soninAperturePacketCurvature_add_coboundary
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) (f : ℝ → ℝ) :
    ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ (opTrace (soninAperturePacketCurvature s a b c (soninCrossingClock a c)
            (one_lt_soninCrossingClock a c) (fun _ => 1))).re +
          ((f c - f a) - (f b - f a) - (f c - f b)) := by
  rw [coboundary_apertureCurvature_eq_zero f a b c]
  simpa using
    not_exists_lower_bound_soninAperturePacketCurvature_re_opTrace a b c ha hb hab hbc q haq hqb

/-- **No inert counterterm restores the floor.**  Any counterterm whose own aperture curvature
vanishes contributes nothing, so the channel stays unbounded below. -/
theorem not_exists_lower_bound_soninAperturePacketCurvature_add_inert
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) {K : ℝ → ℝ → ℝ}
    (hK : ∀ x y z : ℝ, K x z - K x y - K y z = 0) :
    ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ (opTrace (soninAperturePacketCurvature s a b c (soninCrossingClock a c)
            (one_lt_soninCrossingClock a c) (fun _ => 1))).re +
          (K a c - K a b - K b c) := by
  rw [hK a b c]
  simpa using
    not_exists_lower_bound_soninAperturePacketCurvature_re_opTrace a b c ha hb hab hbc q haq hqb

end RHTower
