import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhaseAdaptedProuhetPacket

/-!
# Fixed-half-line endpoint for the phase-adapted Prouhet packet

The ordinary two-endpoint packet leaves the full-line transform of the even completed-density
remainder in its boundary invariant.  A phase-adapted packet behaves differently: its prescribed
double root kills that full-line value and derivative vector before the fixed-half-line boundary
is separated.  Consequently the completion coefficient left beside the returned forward tail is
`(2^N * tau + 1) / 4`, rather than `(2^N * tau + 3) / 4`.

This file records the normalization-free Hermitian algebra for that corrected endpoint.  The
variables `R,R'` are the raw canonical-density value and derivative transforms, while `E,E'` are
the raw decaying-completion transforms.  Thus no hidden factor of two from the integral
normalizations enters the endpoint formula.
-/

open Complex Real Polynomial

namespace RHTower

noncomputable section

/-- The right endpoint appropriate after the double phase root has removed the full-line even
remainder.  It is expressed in raw value--derivative transform coordinates. -/
def phaseAdaptedHalfLineProuhetEndpoint
    (N : ℕ) (R R' E E' : ℂ) : ℝ :=
  (2 *
      (symmetricHermitianCrossCurrentData R R' E E' /
        (E' * (starRingEnd ℂ) E).im) - 1) /
    (2 : ℝ) ^ N

theorem symmetricHermitianCrossCurrentData_neg_add_real_smul
    (R R' E E' : ℂ) (c : ℝ) :
    symmetricHermitianCrossCurrentData
        (-R + (c : ℂ) * E) (-R' + (c : ℂ) * E') E E' =
      -symmetricHermitianCrossCurrentData R R' E E' +
        2 * c * (E' * (starRingEnd ℂ) E).im := by
  unfold symmetricHermitianCrossCurrentData
  simp only [map_add, map_neg, map_mul, Complex.conj_ofReal]
  simp [Complex.mul_im, Complex.mul_re]
  ring

theorem symmetricHermitianCrossCurrentData_add_left
    (A A' B B' E E' : ℂ) :
    symmetricHermitianCrossCurrentData (A + B) (A' + B') E E' =
      symmetricHermitianCrossCurrentData A A' E E' +
        symmetricHermitianCrossCurrentData B B' E E' := by
  unfold symmetricHermitianCrossCurrentData
  simp only [map_add]
  simp [Complex.mul_im, Complex.mul_re]
  ring

private theorem weight_completion_factor (a b e : ℝ) :
    a * (((b - 1) / 4) * e) = (1 / 4 : ℝ) * (a * (b - 1)) * e := by
  ring

private theorem one_div_four_mul (a e : ℝ) :
    (1 / 4 : ℝ) * a * e = (a / 4) * e := by
  ring

/-- At the phase-adapted endpoint, the canonical-density/completion cross is cancelled exactly
by the completion coefficient `(2^N tau + 1) / 4`. -/
theorem phaseAdaptedHalfLineProuhetEndpoint_cancels
    (N : ℕ) (R R' E E' : ℂ)
    (hE : (E' * (starRingEnd ℂ) E).im ≠ 0) :
    let tau := phaseAdaptedHalfLineProuhetEndpoint N R R' E E'
    let c : ℝ := ((2 : ℝ) ^ N * tau + 1) / 4
    symmetricHermitianCrossCurrentData
        (-R + (c : ℂ) * E) (-R' + (c : ℂ) * E') E E' = 0 := by
  dsimp only
  rw [symmetricHermitianCrossCurrentData_neg_add_real_smul]
  unfold phaseAdaptedHalfLineProuhetEndpoint
  have hpow : (2 : ℝ) ^ N ≠ 0 := by positivity
  field_simp [hpow, hE]
  ring

/-- Keeping an arbitrary returned boundary vector `B,B'` shows exactly what remains after the
endpoint cancellation: only its symmetric Hermitian cross with the completion vector. -/
theorem phaseAdaptedHalfLineProuhetEndpoint_reduces_to_returnedCross
    (N : ℕ) (R R' E E' B B' : ℂ)
    (hE : (E' * (starRingEnd ℂ) E).im ≠ 0) :
    let tau := phaseAdaptedHalfLineProuhetEndpoint N R R' E E'
    let c : ℝ := ((2 : ℝ) ^ N * tau + 1) / 4
    symmetricHermitianCrossCurrentData
        (B - R + (c : ℂ) * E) (B' - R' + (c : ℂ) * E') E E' =
      symmetricHermitianCrossCurrentData B B' E E' := by
  dsimp only
  have hcancel := phaseAdaptedHalfLineProuhetEndpoint_cancels N R R' E E' hE
  dsimp only at hcancel
  rw [show B - R +
      ((((2 : ℝ) ^ N * phaseAdaptedHalfLineProuhetEndpoint N R R' E E' + 1) / 4 : ℝ) : ℂ) * E =
        B + (-R +
          ((((2 : ℝ) ^ N * phaseAdaptedHalfLineProuhetEndpoint N R R' E E' + 1) / 4 : ℝ) : ℂ) * E) by
      ring,
    show B' - R' +
      ((((2 : ℝ) ^ N * phaseAdaptedHalfLineProuhetEndpoint N R R' E E' + 1) / 4 : ℝ) : ℂ) * E' =
        B' + (-R' +
          ((((2 : ℝ) ^ N * phaseAdaptedHalfLineProuhetEndpoint N R R' E E' + 1) / 4 : ℝ) : ℂ) * E') by
      ring,
    symmetricHermitianCrossCurrentData_add_left, hcancel, add_zero]

/-! ## Exact source packet before the half-line transform -/

/-- A coefficient packet normalized at the decaying character has an exact one-variable
rank-two residual.  The remote even-remainder rows stay coupled; the only other terms are the
single unshifted even remainder and the completion coefficient forced by the right endpoint. -/
set_option maxHeartbeats 10000 in
theorem weighted_thetaSquareIndexDyadicHaarResidual_eq_evenRows
    (P : ℝ[X]) (q r tau : ℝ) (N : ℕ) (x : ℝ)
    (hqr : 2 * q = r) (hq : P.eval q = 1) (hr : P.eval r = tau) :
    ∑ j ∈ P.support, (P.coeff j * q ^ j) *
        thetaSquareIndexDyadicHaarResidual (N + j) x =
      (∑ j ∈ P.support, (P.coeff j * q ^ j) *
        ((2 : ℝ) ^ (N + j) *
          thetaSquareIndexDyadicEvenRemainderRow (N + j) (-x))) -
        thetaCuspTailSecondEvenRemainder x +
        (((2 : ℝ) ^ N * tau - 1) / 4) * Real.exp (-x / 2) := by
  let w : ℕ → ℝ := fun j => P.coeff j * q ^ j
  let A : ℕ → ℝ := fun j => w j *
    ((2 : ℝ) ^ (N + j) *
      thetaSquareIndexDyadicEvenRemainderRow (N + j) (-x))
  let B : ℕ → ℝ := fun j =>
    w j * thetaSquareIndexDyadicEvenRemainderRow 0 x
  let C : ℕ → ℝ := fun j =>
    w j * ((((2 : ℝ) ^ (N + j) - 1) / 4) * Real.exp (-x / 2))
  have hmass :
      ∑ j ∈ P.support, P.coeff j * q ^ j = 1 := by
    rw [← hq, eval_eq_sum, Polynomial.sum]
  have hcompletion := weighted_completion_sum_eq_endpoint_difference P q r hqr N
  rw [hq, hr] at hcompletion
  have hpoint (j : ℕ) :
      w j * thetaSquareIndexDyadicHaarResidual (N + j) x =
        A j - B j + C j := by
    rw [thetaSquareIndexDyadicHaarResidual_eq_evenCoboundary]
    dsimp only [A, B, C]
    rw [mul_add, mul_sub]
  have hC :
      (∑ j ∈ P.support, C j) =
        (1 / 4 : ℝ) *
          (∑ j ∈ P.support,
            (P.coeff j * q ^ j) * ((2 : ℝ) ^ (N + j) - 1)) *
          Real.exp (-x / 2) := by
    dsimp only [C, w]
    rw [show (∑ j ∈ P.support, (P.coeff j * q ^ j) *
        ((((2 : ℝ) ^ (N + j) - 1) / 4) * Real.exp (-x / 2))) =
        ∑ j ∈ P.support,
          (1 / 4 : ℝ) *
            ((P.coeff j * q ^ j) * ((2 : ℝ) ^ (N + j) - 1)) *
            Real.exp (-x / 2) by
      apply Finset.sum_congr rfl
      intro j _hj
      exact weight_completion_factor _ _ _]
    rw [Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ j ∈ P.support, (A j - B j + C j) := by
      apply Finset.sum_congr rfl
      intro j _hj
      change w j * thetaSquareIndexDyadicHaarResidual (N + j) x = _
      exact hpoint j
    _ = (∑ j ∈ P.support, A j) -
        (∑ j ∈ P.support, B j) +
        (∑ j ∈ P.support, C j) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = _ := by
      rw [hC]
      dsimp only [A, B, w]
      rw [Finset.sum_mul, hmass, one_mul, hcompletion]
      unfold thetaSquareIndexDyadicEvenRemainderRow
      simp only [Nat.cast_zero, zero_mul, add_zero, pow_zero, Nat.cast_one,
        one_mul]
      rw [one_div_four_mul]

end

end RHTower
