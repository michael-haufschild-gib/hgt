import GaloisForLFunctions.RHTower.SoninBurnolApertureCancellation
import GaloisForLFunctions.RHTower.SoninNoAperturePacketFloor

/-!
# The Burnol counterterm is an aperture coboundary

The counterterm is a difference of logarithms of the two apertures, so it telescopes: its own
aperture curvature is exactly zero.  Subtracting it therefore leaves the curvature channel
untouched, and in particular cannot repair the absence of a lower floor there.

Any coercivity has to come from somewhere other than this subtraction.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap

/-- **The counterterm telescopes.**  Its aperture curvature vanishes identically. -/
theorem soninBurnolApertureCounterterm_curvature_eq_zero
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    soninBurnolApertureCounterterm a c - soninBurnolApertureCounterterm a b -
      soninBurnolApertureCounterterm b c = 0 := by
  rw [soninBurnolApertureCounterterm_eq_sub ha hc,
    soninBurnolApertureCounterterm_eq_sub ha hb,
    soninBurnolApertureCounterterm_eq_sub hb hc]
  push_cast
  ring

/-- **The subtraction cannot reach the curvature channel.**  Removing the counterterm from each
aperture step leaves the curvature trace of a source packet exactly as it was, so the channel is
still unbounded below. -/
theorem not_exists_lower_bound_soninAperturePacketCurvature_sub_counterterm
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) :
    ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ (opTrace (soninAperturePacketCurvature s a b c (soninCrossingClock a c)
            (one_lt_soninCrossingClock a c) (fun _ => 1))).re +
          (soninBurnolApertureCounterterm a c - soninBurnolApertureCounterterm a b -
            soninBurnolApertureCounterterm b c).re := by
  have hc : 0 < c := hb.trans hbc
  rw [soninBurnolApertureCounterterm_curvature_eq_zero ha hb hc]
  simpa using
    not_exists_lower_bound_soninAperturePacketCurvature_re_opTrace a b c ha hb hab hbc q haq hqb

end RHTower
