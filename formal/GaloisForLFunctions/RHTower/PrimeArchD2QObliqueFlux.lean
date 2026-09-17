import GaloisForLFunctions.RHTower.PrimeArchReciprocalSquareSectorGate

/-!
# D2--Q oblique completed-flux decomposition

Route D2 controls a real projection of the continued completed prime--Gamma flux, whereas
Route Q asks for a reciprocal-square sector sign.  In centered coordinates the Q observable is
the positive scalar multiple of one *oblique* flux projection.  Thus a D2 real lower bound cannot
by itself supply Q passivity: the transverse imaginary component is indispensable.

This identifies the shared source object without conflating the two open producers.
-/

open Complex

namespace RHTower

noncomputable section

/-- Exact centered-coordinate decomposition of the Route-Q sector observable through the
continued completed prime--Gamma flux. -/
theorem d2q_sector_oblique_completedFlux (z : ℂ) :
    z.re * (continuedPrimeArchReciprocalSquareTrace z).im =
      z.re *
        (z.re * (completedPrimeGammaFlux (1 / 2 + z * I)).re +
          z.im * (completedPrimeGammaFlux (1 / 2 + z * I)).im) /
        normSq z := by
  simp only [continuedPrimeArchReciprocalSquareTrace,
    continuedPrimeArchSourceRelativeTrace, completedPrimeGammaFlux,
    Complex.mul_im, Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.div_im, Complex.I_re, Complex.I_im, sub_re, sub_im]
  ring

/-- At positive centered frequency, Route Q is exactly nonnegativity of the oblique completed
flux projection.  The real component alone is not the required source law. -/
theorem d2q_sector_nonneg_iff_oblique_completedFlux
    {z : ℂ} (hzre : 0 < z.re) :
    0 ≤ z.re * (continuedPrimeArchReciprocalSquareTrace z).im ↔
      0 ≤ z.re * (completedPrimeGammaFlux (1 / 2 + z * I)).re +
        z.im * (completedPrimeGammaFlux (1 / 2 + z * I)).im := by
  rw [d2q_sector_oblique_completedFlux]
  have hz : z ≠ 0 := by
    intro h
    have hRe := congrArg Complex.re h
    simp at hRe
    linarith
  have hnorm : 0 < normSq z := normSq_pos.mpr hz
  have hfactor : 0 < z.re / normSq z := div_pos hzre hnorm
  have hrearrange :
      z.re *
          (z.re * (completedPrimeGammaFlux (1 / 2 + z * I)).re +
            z.im * (completedPrimeGammaFlux (1 / 2 + z * I)).im) /
          normSq z =
        (z.re / normSq z) *
          (z.re * (completedPrimeGammaFlux (1 / 2 + z * I)).re +
            z.im * (completedPrimeGammaFlux (1 / 2 + z * I)).im) := by
    ring
  rw [hrearrange]
  exact mul_nonneg_iff_of_pos_left hfactor

/-- No pointwise real lower bound can logically replace the oblique Route-Q condition: the
transverse flux can reverse its sign even in the positive centered quadrant. -/
theorem real_floor_does_not_force_oblique_sector :
    ∃ z F : ℂ, 0 < z.re ∧ 0 < z.im ∧ 0 ≤ F.re ∧
      z.re * (z.re * F.re + z.im * F.im) / normSq z < 0 := by
  refine ⟨1 + I, -I, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num [normSq_apply]

end

end RHTower
