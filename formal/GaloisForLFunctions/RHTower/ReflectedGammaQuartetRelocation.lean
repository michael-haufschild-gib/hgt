/-
Reflected-Gamma times Cosh-quartet divisor relocation.

This is the analytic/divisor core of the transverse-relocation witness.  A
fixed reflected reciprocal-Gamma carrier supplies the shared central divisor;
multiplication by a Cosh quartet moves precisely the off-central component
while preserving the complete support of zero ordinates.
-/
import GaloisForLFunctions.RHTower.ReflectedGammaCarrier
import GaloisForLFunctions.RHTower.CoshQuartetEnvelopeOrdinates

open Complex

namespace RHTower

noncomputable section

/-- The centered reflected-Gamma carrier decorated by a Cosh quartet envelope. -/
def reflectedGammaQuartetCarrier (beta a : ℝ) (z : ℂ) : ℂ :=
  reflectedGammaCarrier beta z * coshQuartetEnvelope a z

/-- Every reflected-Gamma quartet carrier is entire. -/
theorem reflectedGammaQuartetCarrier_analyticOnNhd (beta a : ℝ) :
    AnalyticOnNhd ℂ (reflectedGammaQuartetCarrier beta a) Set.univ := by
  intro z _
  exact (reflectedGammaCarrier_analyticOnNhd beta z (by simp)).mul
    (coshQuartetEnvelope_analyticAt a z)

/-- The decorated carrier retains centered even symmetry. -/
theorem reflectedGammaQuartetCarrier_neg (beta a : ℝ) (z : ℂ) :
    reflectedGammaQuartetCarrier beta a (-z) = reflectedGammaQuartetCarrier beta a z := by
  unfold reflectedGammaQuartetCarrier
  rw [reflectedGammaCarrier_neg, coshQuartetEnvelope_neg]

/-- The decorated carrier retains Schwarz reality. -/
theorem reflectedGammaQuartetCarrier_conj (beta a : ℝ) (z : ℂ) :
    reflectedGammaQuartetCarrier beta a (starRingEnd ℂ z) =
      starRingEnd ℂ (reflectedGammaQuartetCarrier beta a z) := by
  unfold reflectedGammaQuartetCarrier
  rw [reflectedGammaCarrier_conj, coshQuartetEnvelope_conj, map_mul]

/-- The undisplaced Cosh quartet has only central-axis zeros. -/
theorem coshQuartetEnvelope_zero_re_eq_zero_of_eq_zero
    {z : ℂ} (hz : coshQuartetEnvelope 0 z = 0) : z.re = 0 := by
  rcases coshQuartetEnvelope_eq_zero_iff.mp hz with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk]
    simp
  · rw [hk]
    simp

/-- Every zero of the undisplaced reflected-Gamma quartet carrier is central. -/
theorem reflectedGammaQuartetCarrier_zero_re_eq_zero
    {beta : ℝ} {z : ℂ} (hz : reflectedGammaQuartetCarrier beta 0 z = 0) :
    z.re = 0 := by
  unfold reflectedGammaQuartetCarrier at hz
  rcases mul_eq_zero.mp hz with hgamma | hcosh
  · exact reflectedGammaCarrier_zero_re_eq_zero hgamma
  · exact coshQuartetEnvelope_zero_re_eq_zero_of_eq_zero hcosh

/-- Away from the central axis, the quartet carrier has exactly the Cosh-envelope zeros. -/
theorem reflectedGammaQuartetCarrier_offCentral_zero_iff
    {beta a : ℝ} {z : ℂ} (hz : z.re ≠ 0) :
    reflectedGammaQuartetCarrier beta a z = 0 ↔ coshQuartetEnvelope a z = 0 := by
  unfold reflectedGammaQuartetCarrier
  rw [mul_eq_zero]
  constructor
  · rintro (hgamma | hcosh)
    · exact (hz (reflectedGammaCarrier_zero_re_eq_zero hgamma)).elim
    · exact hcosh
  · intro hcosh
    exact Or.inr hcosh

/-- Each noncentral Cosh zero is an off-central zero of the full carrier. -/
theorem reflectedGammaQuartetCarrier_offCentral_cosh_zero
    {beta a : ℝ} (ha : a ≠ 0) {z : ℂ} (hz : coshQuartetEnvelope a z = 0) :
    reflectedGammaQuartetCarrier beta a z = 0 ∧ z.re ≠ 0 := by
  constructor
  · unfold reflectedGammaQuartetCarrier
    rw [mul_eq_zero]
    exact Or.inr hz
  · exact coshQuartetEnvelope_zero_re_ne_zero ha hz

/-- Horizontal quartet displacements preserve the full support of zero ordinates. -/
theorem reflectedGammaQuartetCarrier_zero_im_iff_zero_im
    (beta a b y : ℝ) :
    (∃ z : ℂ, reflectedGammaQuartetCarrier beta a z = 0 ∧ z.im = y) ↔
      ∃ z : ℂ, reflectedGammaQuartetCarrier beta b z = 0 ∧ z.im = y := by
  constructor
  · rintro ⟨z, hz, him⟩
    unfold reflectedGammaQuartetCarrier at hz
    rcases mul_eq_zero.mp hz with hgamma | hcosh
    · refine ⟨z, ?_, him⟩
      unfold reflectedGammaQuartetCarrier
      rw [mul_eq_zero]
      exact Or.inl hgamma
    · obtain ⟨w, hw, hwim⟩ :=
        (coshQuartetEnvelope_zero_im_iff_zero_im a b y).mp ⟨z, hcosh, him⟩
      refine ⟨w, ?_, hwim⟩
      unfold reflectedGammaQuartetCarrier
      rw [mul_eq_zero]
      exact Or.inr hw
  · rintro ⟨z, hz, him⟩
    unfold reflectedGammaQuartetCarrier at hz
    rcases mul_eq_zero.mp hz with hgamma | hcosh
    · refine ⟨z, ?_, him⟩
      unfold reflectedGammaQuartetCarrier
      rw [mul_eq_zero]
      exact Or.inl hgamma
    · obtain ⟨w, hw, hwim⟩ :=
        (coshQuartetEnvelope_zero_im_iff_zero_im b a y).mp ⟨z, hcosh, him⟩
      refine ⟨w, ?_, hwim⟩
      unfold reflectedGammaQuartetCarrier
      rw [mul_eq_zero]
      exact Or.inr hw

end

end RHTower
