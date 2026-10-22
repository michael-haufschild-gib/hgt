import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodSixthSourceUpperOrientation
import GaloisForLFunctions.RHTower.MobiusCriticalFisherSteinContact

open MeasureTheory Set

/-!
# Exact exponential-ray transform of the sixth likelihood score

Shifting the literal sixth score by its arithmetic edge `9` exposes a polynomial with positive
coefficients.  Translation of an exponential ray then turns its integral into a finite Taylor
operator, with no absolute-value majorant and no lost coefficient interference.

The rational envelopes at the physical seam `A > 157/50` are designed for the dominant square-gap
atom `n = 2`.  They retain the cancellation which the crude bound by `z^(6 : ℕ)` destroys.
-/

namespace RHTower

noncomputable section

def thetaLikelihoodSixthScoreShift (y : ℝ) : ℝ :=
  y ^ 6 + 39 * y ^ 5 + 605 * y ^ 4 + 4680 * y ^ 3 +
    18256 * y ^ 2 + 30446 * y + 9063

def thetaLikelihoodSixthScoreShiftDerivOne (y : ℝ) : ℝ :=
  6 * y ^ 5 + 195 * y ^ 4 + 2420 * y ^ 3 +
    14040 * y ^ 2 + 36512 * y + 30446

def thetaLikelihoodSixthScoreShiftDerivTwo (y : ℝ) : ℝ :=
  30 * y ^ 4 + 780 * y ^ 3 + 7260 * y ^ 2 + 28080 * y + 36512

def thetaLikelihoodSixthScoreShiftDerivThree (y : ℝ) : ℝ :=
  120 * y ^ 3 + 2340 * y ^ 2 + 14520 * y + 28080

def thetaLikelihoodSixthScoreShiftDerivFour (y : ℝ) : ℝ :=
  360 * y ^ 2 + 4680 * y + 14520

def thetaLikelihoodSixthScoreShiftDerivFive (y : ℝ) : ℝ :=
  720 * y + 4680

def thetaLikelihoodSixthScoreShiftDerivSix (_y : ℝ) : ℝ :=
  720

/-- Finite Taylor operator produced by integrating the shifted score against a unit exponential
ray after the rate ratio is changed to `r = A/B`. -/
def thetaLikelihoodSixthScoreRayTransformPolynomial (r y : ℝ) : ℝ :=
  thetaLikelihoodSixthScoreShift y +
    r * thetaLikelihoodSixthScoreShiftDerivOne y +
    r ^ 2 * thetaLikelihoodSixthScoreShiftDerivTwo y +
    r ^ 3 * thetaLikelihoodSixthScoreShiftDerivThree y +
    r ^ 4 * thetaLikelihoodSixthScoreShiftDerivFour y +
    r ^ 5 * thetaLikelihoodSixthScoreShiftDerivFive y +
    r ^ 6 * thetaLikelihoodSixthScoreShiftDerivSix y

/-- Coefficient-sharp dominant-ray envelope.  Retaining the exact Taylor coefficients lowers the
uniform constant from `1000000` to `950000`; this is the margin needed by the reflected
second--sixth curvature comparison. -/
theorem thetaLikelihoodSixthScoreRayTransformPolynomial_seam_envelope_sharp
    {s : ℝ} (hs : 0 ≤ s) :
    thetaLikelihoodSixthScoreRayTransformPolynomial (48 / 25) (21 / 50 + s) ≤
      950000 * Real.exp s := by
  have he := Real.sum_le_exp_of_nonneg hs 7
  have ht : 1 + s + s ^ 2 / 2 + s ^ 3 / 6 + s ^ 4 / 24 +
      s ^ 5 / 120 + s ^ 6 / 720 ≤ Real.exp s := by
    norm_num [Finset.sum_range_succ] at he ⊢
    exact he
  have hp :
      thetaLikelihoodSixthScoreRayTransformPolynomial (48 / 25) (21 / 50 + s) ≤
        950000 * (1 + s + s ^ 2 / 2 + s ^ 3 / 6 + s ^ 4 / 24 +
          s ^ 5 / 120 + s ^ 6 / 720) := by
    dsimp [thetaLikelihoodSixthScoreRayTransformPolynomial,
      thetaLikelihoodSixthScoreShift, thetaLikelihoodSixthScoreShiftDerivOne,
      thetaLikelihoodSixthScoreShiftDerivTwo,
      thetaLikelihoodSixthScoreShiftDerivThree,
      thetaLikelihoodSixthScoreShiftDerivFour,
      thetaLikelihoodSixthScoreShiftDerivFive,
      thetaLikelihoodSixthScoreShiftDerivSix]
    ring_nf
    have hs2 : 0 ≤ s ^ 2 := by positivity
    have hs3 : 0 ≤ s ^ 3 := by positivity
    have hs4 : 0 ≤ s ^ 4 := by positivity
    have hs5 : 0 ≤ s ^ 5 := by positivity
    have hs6 : 0 ≤ s ^ 6 := by positivity
    nlinarith
  exact hp.trans (mul_le_mul_of_nonneg_left ht (by norm_num))

/-- Exact positive-coefficient normal form at the arithmetic edge `9`. -/
theorem thetaLikelihoodSixthScore_eq_shiftNine (z : ℝ) :
    thetaLikelihoodSixthScore z = thetaLikelihoodSixthScoreShift (z - 9) := by
  simp [thetaLikelihoodSixthScore, thetaLikelihoodSixthScoreShift]
  ring

/-- Uniform dominant-ray envelope after the sharp physical ratio bound `A/B ≤ 48/25`. -/
theorem thetaLikelihoodSixthScoreRayTransformPolynomial_seam_envelope
    {s : ℝ} (hs : 0 ≤ s) :
    thetaLikelihoodSixthScoreRayTransformPolynomial (48 / 25) (21 / 50 + s) ≤
      1000000 * Real.exp s := by
  have he := Real.sum_le_exp_of_nonneg hs 7
  have ht : 1 + s + s ^ 2 / 2 + s ^ 3 / 6 + s ^ 4 / 24 +
      s ^ 5 / 120 + s ^ 6 / 720 ≤ Real.exp s := by
    norm_num [Finset.sum_range_succ] at he ⊢
    exact he
  have hp :
      thetaLikelihoodSixthScoreRayTransformPolynomial (48 / 25) (21 / 50 + s) ≤
        1000000 * (1 + s + s ^ 2 / 2 + s ^ 3 / 6 + s ^ 4 / 24 +
          s ^ 5 / 120 + s ^ 6 / 720) := by
    dsimp [thetaLikelihoodSixthScoreRayTransformPolynomial,
      thetaLikelihoodSixthScoreShift, thetaLikelihoodSixthScoreShiftDerivOne,
      thetaLikelihoodSixthScoreShiftDerivTwo,
      thetaLikelihoodSixthScoreShiftDerivThree,
      thetaLikelihoodSixthScoreShiftDerivFour,
      thetaLikelihoodSixthScoreShiftDerivFive,
      thetaLikelihoodSixthScoreShiftDerivSix]
    ring_nf
    have hs2 : 0 ≤ s ^ 2 := by positivity
    have hs3 : 0 ≤ s ^ 3 := by positivity
    have hs4 : 0 ≤ s ^ 4 := by positivity
    have hs5 : 0 ≤ s ^ 5 := by positivity
    have hs6 : 0 ≤ s ^ 6 := by positivity
    nlinarith
  exact hp.trans (mul_le_mul_of_nonneg_left ht (by norm_num))

/-- Matching point-mass envelope at the same arithmetic seam. -/
theorem thetaLikelihoodSixthScoreShift_seam_envelope
    {s : ℝ} (hs : 0 ≤ s) :
    thetaLikelihoodSixthScoreShift (21 / 50 + s) ≤
      50000 * Real.exp s := by
  have he := Real.sum_le_exp_of_nonneg hs 7
  have ht : 1 + s + s ^ 2 / 2 + s ^ 3 / 6 + s ^ 4 / 24 +
      s ^ 5 / 120 + s ^ 6 / 720 ≤ Real.exp s := by
    norm_num [Finset.sum_range_succ] at he ⊢
    exact he
  have hp : thetaLikelihoodSixthScoreShift (21 / 50 + s) ≤
      50000 * (1 + s + s ^ 2 / 2 + s ^ 3 / 6 + s ^ 4 / 24 +
        s ^ 5 / 120 + s ^ 6 / 720) := by
    dsimp [thetaLikelihoodSixthScoreShift]
    ring_nf
    have hs2 : 0 ≤ s ^ 2 := by positivity
    have hs3 : 0 ≤ s ^ 3 := by positivity
    have hs4 : 0 ≤ s ^ 4 := by positivity
    have hs5 : 0 ≤ s ^ 5 := by positivity
    have hs6 : 0 ≤ s ^ 6 := by positivity
    nlinarith
  exact hp.trans (mul_le_mul_of_nonneg_left ht (by norm_num))

private theorem integrableOn_pow_mul_exp_neg_rate
    (n : ℕ) {B : ℝ} (hB : 0 < B) :
    IntegrableOn (fun u : ℝ => u ^ n * Real.exp (-(B * u))) (Ioi 0) := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn : (-1 : ℝ) < (n : ℝ) := by linarith
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (n : ℝ)) (b := B) hn (by norm_num) hB
  convert h using 1
  funext u
  simp only [Real.rpow_one]
  rw [Real.rpow_natCast]
  congr 1
  ring_nf

private theorem setIntegral_Ioi_comp_add_right_sixth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (a h : ℝ) :
    (∫ y in Ioi (a - h), F (y + h)) = ∫ x in Ioi a, F x := by
  have hmp : MeasurePreserving (fun y : ℝ => y + h) volume volume :=
    measurePreserving_add_right volume h
  have hemb : MeasurableEmbedding (fun y : ℝ => y + h) :=
    measurableEmbedding_addRight h
  have hpre : (fun y : ℝ => y + h) ⁻¹' Ioi a = Ioi (a - h) := by
    ext y
    simp [Set.mem_Ioi, sub_lt_iff_lt_add]
  have h1 := hmp.setIntegral_preimage_emb hemb F (Ioi a)
  rw [hpre] at h1
  exact h1

/-- The literal score is integrable on every nonnegative positive-rate exponential ray. -/
theorem integrableOn_thetaLikelihoodSixthScore_mul_exp_neg_rate
    (A : ℝ) {d B : ℝ} (hd : 0 ≤ d) (hB : 0 < B) :
    IntegrableOn (fun t : ℝ =>
      thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t))) (Ioi d) := by
  have hmono (m : ℕ) :
      IntegrableOn (fun t : ℝ => t ^ m * Real.exp (-(B * t))) (Ioi d) := by
    exact (integrableOn_pow_mul_exp_neg_rate m hB).mono_set fun t ht => by
      exact lt_of_le_of_lt hd ht
  have h6 := (hmono 6).const_mul (A ^ 6)
  have h5 := (hmono 5).const_mul (15 * A ^ 5)
  have h4 := (hmono 4).const_mul (65 * A ^ 4)
  have h3 := (hmono 3).const_mul (90 * A ^ 3)
  have h2 := (hmono 2).const_mul (31 * A ^ 2)
  have h1 := (hmono 1).const_mul A
  change Integrable (fun t : ℝ =>
    thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t)))
      (volume.restrict (Ioi d))
  convert ((((h6.sub h5).add h4).sub h3).add h2).sub h1 using 1
  funext t
  simp only [Pi.add_apply, Pi.sub_apply]
  unfold thetaLikelihoodSixthScore
  ring

/-- Exact incomplete-Laplace transform of the literal sixth score on an arbitrary exponential
ray.  The right side is finite and retains every signed coefficient. -/
theorem integral_Ioi_thetaLikelihoodSixthScore_mul_exp_neg_rate
    (A d : ℝ) {B : ℝ} (hB : 0 < B) :
    (∫ t : ℝ in Ioi d,
      thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t))) =
      Real.exp (-(B * d)) / B *
        thetaLikelihoodSixthScoreRayTransformPolynomial (A / B) (A * d - 9) := by
  let y := A * d - 9
  let c : ℕ → ℝ := fun k =>
    match k with
    | 0 => thetaLikelihoodSixthScoreShift y
    | 1 => A * thetaLikelihoodSixthScoreShiftDerivOne y
    | 2 => A ^ 2 * thetaLikelihoodSixthScoreShiftDerivTwo y / 2
    | 3 => A ^ 3 * thetaLikelihoodSixthScoreShiftDerivThree y / 6
    | 4 => A ^ 4 * thetaLikelihoodSixthScoreShiftDerivFour y / 24
    | 5 => A ^ 5 * thetaLikelihoodSixthScoreShiftDerivFive y / 120
    | 6 => A ^ 6 * thetaLikelihoodSixthScoreShiftDerivSix y / 720
    | _ => 0
  have htrans := setIntegral_Ioi_comp_add_right_sixth
    (fun t : ℝ => thetaLikelihoodSixthScore (A * t) * Real.exp (-(B * t))) d d
  rw [sub_self] at htrans
  rw [← htrans]
  have hfun : (fun u : ℝ =>
      thetaLikelihoodSixthScore (A * (u + d)) * Real.exp (-(B * (u + d)))) =
      fun u => Real.exp (-(B * d)) *
        (∑ k ∈ Finset.range 7, c k * (u ^ k * Real.exp (-(B * u)))) := by
    funext u
    have hexp : Real.exp (-(B * (u + d))) =
        Real.exp (-(B * d)) * Real.exp (-(B * u)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [thetaLikelihoodSixthScore_eq_shiftNine, hexp]
    norm_num [Finset.sum_range_succ, c]
    dsimp [y, thetaLikelihoodSixthScoreShift,
      thetaLikelihoodSixthScoreShiftDerivOne,
      thetaLikelihoodSixthScoreShiftDerivTwo,
      thetaLikelihoodSixthScoreShiftDerivThree,
      thetaLikelihoodSixthScoreShiftDerivFour,
      thetaLikelihoodSixthScoreShiftDerivFive,
      thetaLikelihoodSixthScoreShiftDerivSix]
    ring
  rw [hfun, integral_const_mul]
  have hI0 : (∫ u : ℝ in Ioi 0, Real.exp (-(B * u))) = 1 / B := by
    simpa using integral_Ioi_pow_mul_exp_neg_rate 0 hB
  have hI1 : (∫ u : ℝ in Ioi 0, u * Real.exp (-(B * u))) = 1 / B ^ 2 := by
    simpa using integral_Ioi_pow_mul_exp_neg_rate 1 hB
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
    norm_num [Finset.sum_range_succ, c, hI0, hI1,
      integral_Ioi_pow_mul_exp_neg_rate 0 hB,
      integral_Ioi_pow_mul_exp_neg_rate 1 hB,
      integral_Ioi_pow_mul_exp_neg_rate 2 hB,
      integral_Ioi_pow_mul_exp_neg_rate 3 hB,
      integral_Ioi_pow_mul_exp_neg_rate 4 hB,
      integral_Ioi_pow_mul_exp_neg_rate 5 hB,
      integral_Ioi_pow_mul_exp_neg_rate 6 hB]
    dsimp [thetaLikelihoodSixthScoreRayTransformPolynomial, y]
    field_simp [hB.ne']
  · intro k hk
    exact (integrableOn_pow_mul_exp_neg_rate k hB).const_mul _

end

end RHTower
