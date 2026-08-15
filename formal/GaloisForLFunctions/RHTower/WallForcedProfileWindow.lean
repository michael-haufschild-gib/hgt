import GaloisForLFunctions.RHTower.WallForcedProfileRay

/-!
# The forced profile on the window, and the three-region composition

On the frequency window the profile splits into the propagated datum and the window part, and neither
carries a threshold factor beyond the single power of the window length that the window estimate
charges.  Together with the two outward rays this closes the frequency line: the complement of an
open window is the union of two closed rays, which carry the same mass as the open ones, so a bound
on each of the three regions is a bound on the line.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

omit [Nontrivial X] in
theorem sq_add_two_le (u v : ℝ≥0∞) : (u + v) ^ 2 ≤ 4 * (u ^ 2 + v ^ 2) := by
  have h1 : u + v ≤ 2 * max u v :=
    (add_le_add (le_max_left u v) (le_max_right u v)).trans (by rw [two_mul])
  have h2 : max u v ^ 2 ≤ u ^ 2 + v ^ 2 := by
    rcases max_choice u v with h | h <;> rw [h]
    · exact le_self_add
    · exact le_add_self
  calc (u + v) ^ 2 ≤ (2 * max u v) ^ 2 := pow_le_pow_left' h1 2
    _ = 4 * max u v ^ 2 := by ring
    _ ≤ 4 * (u ^ 2 + v ^ 2) := mul_le_mul' le_rfl h2

omit [Nontrivial X] in
/-- **The forced profile on the frequency window.**  Both the propagated datum and the window part
are controlled without any threshold factor beyond the one power of the window length. -/
theorem lintegral_sq_forcedProfile_window_le
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {b : ℝ → X} {Y : ℝ} (c : X) :
    (∫⁻ x in Ioo (-Y) Y, ‖forcedProfile E T b c σ x‖ₑ ^ 2)
      ≤ 4 * ((∫⁻ x in Ioo (-Y) Y, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖ₑ ^ 2)
          + ∫⁻ x in Ioo (-Y) Y, ‖forcedWindowPart E T b σ x‖ₑ ^ 2) := by
  have hpt : ∀ x ∈ Ioo (-Y) Y, ‖forcedProfile E T b c σ x‖ₑ ^ 2
      ≤ 4 * (‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖ₑ ^ 2
          + ‖forcedWindowPart E T b σ x‖ₑ ^ 2) := by
    intro x _
    rw [forcedProfile]
    exact le_trans (pow_le_pow_left' (enorm_add_le _ _) 2) (sq_add_two_le _ _)
  have hmeasA : AEMeasurable (fun x : ℝ =>
      ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I) c‖ₑ ^ 2)
      (volume.restrict (Ioo (-Y) Y)) := by
    have hcont := continuous_stripPropagator_line (T := T) hEdiff hE hEne hσ0 hσ1
    exact ((hcont.aestronglyMeasurable).apply_continuousLinearMap _).enorm.pow_const 2
  refine le_trans (setLIntegral_mono' measurableSet_Ioo hpt) ?_
  rw [lintegral_const_mul' _ _ (by simp : (4 : ℝ≥0∞) ≠ ⊤)]
  refine mul_le_mul' le_rfl (le_of_eq ?_)
  rw [lintegral_add_left' hmeasA]

omit [InnerProductSpace ℂ X] [CompleteSpace X] [Nontrivial X] in
/-- **The three regions compose.**  A bound on the window and one on each outward ray give the bound
on the whole frequency line. -/
theorem lintegral_sq_of_window_and_rays {f : ℝ → X} {Y : ℝ} {A B C : ℝ≥0∞}
    (hwin : (∫⁻ x in Ioo (-Y) Y, ‖f x‖ₑ ^ 2) ≤ A)
    (hneg : (∫⁻ x in Iio (-Y), ‖f x‖ₑ ^ 2) ≤ B)
    (hpos : (∫⁻ x in Ioi Y, ‖f x‖ₑ ^ 2) ≤ C) :
    (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2) ≤ A + B + C := by
  refine lintegral_sq_le_of_window_and_tails hwin ?_ ?_
  · rw [lintegral_sq_Iic_eq_Iio]
    exact hneg
  · rw [lintegral_sq_Ici_eq_Ioi]
    exact hpos

end GaloisForLFunctions.RHTower
