import GaloisForLFunctions.RHTower.BernsteinAffineRowIndexConcentration

/-!
# Exact geometry of Bernstein index occupation

Amplitude and index occupation recover the real coordinate and squared imaginary coordinate.
On a fixed amplitude ellipse, conjugation is the exact ambiguity.
-/

open Complex
open scoped Real unitInterval ComplexConjugate

namespace RHTower

noncomputable section

theorem bernsteinAffineOccupation_conj (u : ℂ) :
    bernsteinAffineOccupation (conj u) = bernsteinAffineOccupation u := by
  apply Subtype.ext
  change ‖conj u‖ / (‖conj u‖ + ‖1 - conj u‖) = ‖u‖ / (‖u‖ + ‖1 - u‖)
  rw [show 1 - conj u = conj (1 - u) by simp, norm_conj, norm_conj]

theorem bernsteinAffineRowHalfOrderConstant_conj (u : ℂ) :
    bernsteinAffineRowHalfOrderConstant (conj u) = bernsteinAffineRowHalfOrderConstant u := by
  unfold bernsteinAffineRowHalfOrderConstant
  rw [show 1 - conj u = conj (1 - u) by simp, norm_conj, norm_conj]

theorem re_eq_bernsteinAffineOccupation (u : ℂ) :
    u.re = (1 + (‖u‖ + ‖1 - u‖) ^ 2 *
      (2 * (bernsteinAffineOccupation u : ℝ) - 1)) / 2 := by
  have hdiff : ‖u‖ ^ 2 - ‖1 - u‖ ^ 2 = 2 * u.re - 1 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    ring
  calc
    u.re = (1 + ‖u‖ ^ 2 - ‖1 - u‖ ^ 2) / 2 := by linarith
    _ = _ := by
      change _ = (1 + (‖u‖ + ‖1 - u‖) ^ 2 *
        (2 * (‖u‖ / (‖u‖ + ‖1 - u‖)) - 1)) / 2
      field_simp [ne_of_gt (bernsteinAffineAmplitude_pos u)]
      ring

theorem im_sq_eq_bernsteinAffineOccupation (u : ℂ) :
    u.im ^ 2 = (‖u‖ + ‖1 - u‖) ^ 2 * (bernsteinAffineOccupation u : ℝ) ^ 2 - u.re ^ 2 := by
  have hn : ‖u‖ = (‖u‖ + ‖1 - u‖) * (bernsteinAffineOccupation u : ℝ) := by
    change ‖u‖ = (‖u‖ + ‖1 - u‖) * (‖u‖ / (‖u‖ + ‖1 - u‖))
    field_simp [ne_of_gt (bernsteinAffineAmplitude_pos u)]
  have h := Complex.sq_norm_sub_sq_re u
  rw [hn, mul_pow] at h
  exact h.symm

/-- On one amplitude ellipse, index occupation forgets exactly complex conjugation. -/
theorem bernsteinAffineOccupation_eq_iff_of_amplitude_eq {u v : ℂ}
    (hamp : ‖u‖ + ‖1 - u‖ = ‖v‖ + ‖1 - v‖) :
    bernsteinAffineOccupation u = bernsteinAffineOccupation v ↔ u = v ∨ u = conj v := by
  constructor
  · intro hp
    have hre : u.re = v.re := by
      rw [re_eq_bernsteinAffineOccupation u, re_eq_bernsteinAffineOccupation v, hamp, hp]
    have him : u.im ^ 2 = v.im ^ 2 := by
      rw [im_sq_eq_bernsteinAffineOccupation u, im_sq_eq_bernsteinAffineOccupation v,
        hamp, hp, hre]
    rcases eq_or_eq_neg_of_sq_eq_sq u.im v.im him with h | h
    · exact Or.inl (Complex.ext hre h)
    · exact Or.inr (Complex.ext (by simpa using hre) (by simpa using h))
  · rintro (rfl | rfl)
    · rfl
    · exact bernsteinAffineOccupation_conj v

end
end RHTower
