import GaloisForLFunctions.RHTower.SquaredXiRadialJetXiSpecialization
import GaloisForLFunctions.RHTower.ScrewCurvatureSumOfSquares

/-!
# The completed source jet as a Riemann-hypothesis discriminator

Unconditionally the squared centered spectral node has positive real part, and the sector bound
carries its reciprocal powers only through order nineteen.  Under the Riemann hypothesis the node
is a *positive real*: every centered spectral point is real, so the squared node has vanishing
imaginary part.  Then every shifted reciprocal power is a positive real at every order, the
squared-coordinate field is completely monotone without an order restriction, and the completed
source polynomial is strictly positive at every order and every positive radius.

Contrapositively, a single strictly negative completed source jet disproves the Riemann
hypothesis.  This is the exact discriminator the reverse-Bessel source reduction aims at.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Under the Riemann hypothesis the squared centered spectral node is real. -/
theorem xiSquaredNode_im_eq_zero_of_riemannHypothesis (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    (xiSquaredNode q).im = 0 := by
  have h := xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH q
  rw [xiSquaredNode, pow_two, Complex.mul_im, h]
  ring

/-- Under the Riemann hypothesis every shifted reciprocal power of a spectral node is a strictly
positive real, at every order. -/
theorem re_xiShiftedReciprocalSquare_pow_pos_of_riemannHypothesis (hRH : RiemannHypothesis)
    {y : ℝ} (hy : 0 ≤ y) (q : XiZeroCopy) (k : ℕ) :
    0 < (xiShiftedReciprocalSquare y q ^ k).re := by
  set r : ℝ := (xiSquaredNode q).re with hr
  have hrpos : 0 < r := xiSquaredNode_re_pos q
  have him : (xiSquaredNode q).im = 0 := xiSquaredNode_im_eq_zero_of_riemannHypothesis hRH q
  have hnode : xiSquaredNode q = (r : ℂ) := by
    apply Complex.ext
    · simp [hr]
    · simpa using him
  have hpos : 0 < y + r := by linarith
  have hcast : (y : ℂ) + xiSquaredNode q = ((y + r : ℝ) : ℂ) := by
    rw [hnode]
    push_cast
    ring
  rw [xiShiftedReciprocalSquare_eq_inv hy q, hcast, ← Complex.ofReal_inv, ← Complex.ofReal_pow,
    Complex.ofReal_re]
  exact pow_pos (inv_pos.mpr hpos) k

/-- Under the Riemann hypothesis the shifted reciprocal moment is strictly positive at every
order, with no sector restriction. -/
theorem re_xiShiftedReciprocalMoment_pos_of_riemannHypothesis (hRH : RiemannHypothesis)
    {y : ℝ} (hy : 0 < y) (n : ℕ) : 0 < (xiShiftedReciprocalMoment y n).re := by
  have hsumC := summable_xiShiftedReciprocalSquare_pow hy.le n
  have hsum : Summable (fun q : XiZeroCopy =>
      (xiShiftedReciprocalSquare y q ^ (n + 1)).re) := Complex.reCLM.summable hsumC
  obtain ⟨q0⟩ := nonempty_xiZeroCopy
  rw [xiShiftedReciprocalMoment, re_tsum hsumC]
  exact hsum.tsum_pos
    (fun q =>
      (re_xiShiftedReciprocalSquare_pow_pos_of_riemannHypothesis hRH hy.le q (n + 1)).le) q0
    (re_xiShiftedReciprocalSquare_pow_pos_of_riemannHypothesis hRH hy.le q0 (n + 1))

/-- **Complete monotonicity at every order under the Riemann hypothesis.** -/
theorem alternating_iteratedDeriv_squaredXiRadialField_pos_of_riemannHypothesis
    (hRH : RiemannHypothesis) {y : ℝ} (hy : 0 < y) (n : ℕ) :
    0 < (-1 : ℝ) ^ n * iteratedDeriv n squaredXiRadialField y := by
  have hsq : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [iteratedDeriv_squaredXiRadialField n hy,
    show (-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * (n.factorial : ℝ) / 2 *
        (xiShiftedReciprocalMoment y n).re)
      = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
        ((n.factorial : ℝ) / 2 * (xiShiftedReciprocalMoment y n).re) from by ring,
    hsq, one_mul]
  exact mul_pos (by positivity)
    (re_xiShiftedReciprocalMoment_pos_of_riemannHypothesis hRH hy n)

/-- **The completed source jet is strictly positive at every order under the Riemann
hypothesis.** -/
theorem completedSourceJet_pos_of_riemannHypothesis (hRH : RiemannHypothesis) (n : ℕ)
    {w : ℝ} (hw : 0 < w) : 0 < completedSourceJet n w := by
  have hy : (0:ℝ) < w ^ (2 : ℕ) := by positivity
  have hpos := alternating_iteratedDeriv_squaredXiRadialField_pos_of_riemannHypothesis hRH hy n
  have hscale : (0:ℝ) < 2 ^ (n + 1) * w ^ (2 * n + 1) := by positivity
  rw [completedSourceJet_eq n hw,
    show (-1 : ℝ) ^ n * 2 ^ (n + 1) * w ^ (2 * n + 1) *
        iteratedDeriv n squaredXiRadialField (w ^ (2 : ℕ))
      = (2 ^ (n + 1) * w ^ (2 * n + 1)) *
        ((-1 : ℝ) ^ n * iteratedDeriv n squaredXiRadialField (w ^ (2 : ℕ))) from by ring]
  exact mul_pos hscale hpos

/-- **The discriminator.**  A single strictly negative completed source jet at a positive radius
disproves the Riemann hypothesis. -/
theorem not_riemannHypothesis_of_completedSourceJet_neg {n : ℕ} {w : ℝ} (hw : 0 < w)
    (hneg : completedSourceJet n w < 0) : ¬ RiemannHypothesis := by
  intro hRH
  exact absurd hneg (not_lt.mpr (completedSourceJet_pos_of_riemannHypothesis hRH n hw).le)

end

end RHTower
