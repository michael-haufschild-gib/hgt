import GaloisForLFunctions.RHTower.ThetaWignerEisensteinSymbol

/-!
# The positive dual of the Wigner--Eisenstein cross-energy obstruction

The Wigner--Eisenstein current is a mixed energy rather than a squared norm.
The strictly positive archimedean symbol nevertheless gives an exact completed
square.  Thus every scalar cross channel has a lower floor once both the
symbol-weighted channel and its reciprocal-symbol dual channel are controlled.

This is the constructive statement left by the failure of bulk coercivity to
choose the Xi orientation.  It does not assert that the required dual channel
is bounded for the arithmetic Wigner current and it makes no RH claim.
-/

open Complex

namespace RHTower

noncomputable section

/-- Exact complex completed square for a positive scalar symbol. -/
theorem complexCrossEnergy_completeSquare
    {p : ℝ} (hp : 0 < p) (z w : ℂ) :
    p * Complex.normSq z +
        2 * ((starRingEnd ℂ) z * w).re +
        Complex.normSq w / p =
      Complex.normSq ((p : ℂ) * z + w) / p := by
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, ofReal_re, ofReal_im, zero_mul,
    sub_zero]
  field_simp [ne_of_gt hp]
  ring

/-- A positive scalar symbol converts a mixed complex channel into a lower
bound paid by the primal and reciprocal-symbol energies. -/
theorem complexCrossEnergy_lowerBound
    {p : ℝ} (hp : 0 < p) (z w : ℂ) :
    -(p * Complex.normSq z + Complex.normSq w / p) / 2 ≤
      ((starRingEnd ℂ) z * w).re := by
  have hnonneg : 0 ≤ Complex.normSq ((p : ℂ) * z + w) / p :=
    div_nonneg (Complex.normSq_nonneg _) hp.le
  rw [← complexCrossEnergy_completeSquare hp] at hnonneg
  linarith

/-- **Positive Wigner dual floor.**  At every Eisenstein height and dilation
frequency, the coercive symbol gives the exact Young-type lower bound for a
mixed channel.  The reciprocal-symbol term is the boundary/scattering datum
which bulk coercivity alone does not control. -/
theorem thetaWignerEisenstein_crossEnergy_lowerBound
    (b τ : ℝ) (z w : ℂ) :
    -(thetaWignerEisensteinSymbol b τ * Complex.normSq z +
        Complex.normSq w / thetaWignerEisensteinSymbol b τ) / 2 ≤
      ((starRingEnd ℂ) z * w).re := by
  exact complexCrossEnergy_lowerBound
    (thetaWignerEisensteinSymbol_pos b τ) z w

end

end RHTower
