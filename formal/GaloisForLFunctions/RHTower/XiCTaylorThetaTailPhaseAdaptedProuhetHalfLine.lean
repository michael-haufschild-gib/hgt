import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhaseAdaptedProuhetPacket
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteTranslationBounds

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

open Complex Real Polynomial MeasureTheory Set Filter Topology

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
  simp [Complex.mul_im]
  ring

theorem symmetricHermitianCrossCurrentData_add_left
    (A A' B B' E E' : ℂ) :
    symmetricHermitianCrossCurrentData (A + B) (A' + B') E E' =
      symmetricHermitianCrossCurrentData A A' E E' +
        symmetricHermitianCrossCurrentData B B' E E' := by
  unfold symmetricHermitianCrossCurrentData
  simp only [map_add]
  simp [Complex.mul_im]
  ring

private theorem weight_completion_factor (a b e : ℝ) :
    a * (((b - 1) / 4) * e) = (1 / 4 : ℝ) * (a * (b - 1)) * e := by
  ring

private theorem one_div_four_mul (a e : ℝ) :
    (1 / 4 : ℝ) * a * e = (a / 4) * e := by
  ring

/-- The decaying endpoint character of the dyadic packet. -/
def dyadicProuhetDecayCharacter : ℝ :=
  (2 : ℝ) ^ (-(1 / 2 : ℝ))

/-- The growing endpoint character of the dyadic packet. -/
def dyadicProuhetGrowthCharacter : ℝ :=
  (2 : ℝ) ^ (1 / 2 : ℝ)

theorem two_mul_dyadicProuhetDecayCharacter :
    2 * dyadicProuhetDecayCharacter = dyadicProuhetGrowthCharacter := by
  unfold dyadicProuhetDecayCharacter dyadicProuhetGrowthCharacter
  nth_rw 1 [← Real.rpow_one (2 : ℝ)]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- Critical amplitude multiplying the depth-`K` translate of the even remainder. -/
def dyadicEvenRemoteAmplitude (K : ℕ) : ℝ :=
  (2 : ℝ) ^ K * (((2 ^ K : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))

theorem dyadicEvenRemoteAmplitude_eq_rpow (K : ℕ) :
    dyadicEvenRemoteAmplitude K = (2 : ℝ) ^ ((K : ℝ) / 2) := by
  unfold dyadicEvenRemoteAmplitude
  have hnat : (2 : ℝ) ^ K = Real.exp ((K : ℝ) * Real.log 2) := by
    rw [← Real.rpow_natCast,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [show (((2 ^ K : ℕ) : ℝ)) = (2 : ℝ) ^ K by norm_num,
    hnat, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
  congr 1
  ring

theorem dyadicProuhetDecayCharacter_pow_mul_remoteAmplitude
    (N j : ℕ) :
    dyadicProuhetDecayCharacter ^ j * dyadicEvenRemoteAmplitude (N + j) =
      dyadicEvenRemoteAmplitude N := by
  rw [dyadicEvenRemoteAmplitude_eq_rpow,
    dyadicEvenRemoteAmplitude_eq_rpow]
  unfold dyadicProuhetDecayCharacter
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  push_cast
  ring

/-- The reflected critical row is literally one left translate of the even remainder with the
critical dyadic amplitude. -/
theorem two_pow_mul_evenRemainderRow_neg_eq_remoteTranslate
    (K : ℕ) (x : ℝ) :
    (2 : ℝ) ^ K * thetaSquareIndexDyadicEvenRemainderRow K (-x) =
      dyadicEvenRemoteAmplitude K *
        thetaCuspTailSecondEvenRemainder (x - (K : ℝ) * Real.log 2) := by
  unfold thetaSquareIndexDyadicEvenRemainderRow dyadicEvenRemoteAmplitude
  rw [show -x + (K : ℝ) * Real.log 2 =
      -(x - (K : ℝ) * Real.log 2) by ring,
    thetaCuspTailSecondEvenRemainder_neg]
  rw [mul_assoc]

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
    rw [← Finset.sum_mul, ← Finset.mul_sum]
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
      rw [← Finset.sum_mul, hmass, one_mul, hcompletion]
      unfold thetaSquareIndexDyadicEvenRemainderRow
      simp only [Nat.cast_zero, zero_mul, add_zero, pow_zero, Nat.cast_one,
        Real.one_rpow, one_mul]
      rw [one_div_four_mul]

/-- At the critical dyadic endpoint, every remote row has the same base amplitude.  The packet
therefore becomes an unweighted finite translate packet of the exactly even remainder. -/
theorem weighted_thetaSquareIndexDyadicHaarResidual_eq_evenTranslatePacket
    (P : ℝ[X]) (tau : ℝ) (N : ℕ) (x : ℝ)
    (hq : P.eval dyadicProuhetDecayCharacter = 1)
    (hr : P.eval dyadicProuhetGrowthCharacter = tau) :
    ∑ j ∈ P.support,
        (P.coeff j * dyadicProuhetDecayCharacter ^ j) *
          thetaSquareIndexDyadicHaarResidual (N + j) x =
      dyadicEvenRemoteAmplitude N *
          (∑ j ∈ P.support, P.coeff j *
            thetaCuspTailSecondEvenRemainder
              (x - ((N + j : ℕ) : ℝ) * Real.log 2)) -
        thetaCuspTailSecondEvenRemainder x +
        (((2 : ℝ) ^ N * tau - 1) / 4) * Real.exp (-x / 2) := by
  rw [weighted_thetaSquareIndexDyadicHaarResidual_eq_evenRows
    P dyadicProuhetDecayCharacter dyadicProuhetGrowthCharacter tau N x
      two_mul_dyadicProuhetDecayCharacter hq hr]
  have hremote :
      (∑ j ∈ P.support,
        (P.coeff j * dyadicProuhetDecayCharacter ^ j) *
          ((2 : ℝ) ^ (N + j) *
            thetaSquareIndexDyadicEvenRemainderRow (N + j) (-x))) =
        dyadicEvenRemoteAmplitude N *
          (∑ j ∈ P.support, P.coeff j *
            thetaCuspTailSecondEvenRemainder
              (x - ((N + j : ℕ) : ℝ) * Real.log 2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [two_pow_mul_evenRemainderRow_neg_eq_remoteTranslate]
    have hscale :=
      dyadicProuhetDecayCharacter_pow_mul_remoteAmplitude N j
    rw [show
        (P.coeff j * dyadicProuhetDecayCharacter ^ j) *
            (dyadicEvenRemoteAmplitude (N + j) *
              thetaCuspTailSecondEvenRemainder
                (x - ((N + j : ℕ) : ℝ) * Real.log 2)) =
          P.coeff j *
            (dyadicProuhetDecayCharacter ^ j *
              dyadicEvenRemoteAmplitude (N + j)) *
            thetaCuspTailSecondEvenRemainder
              (x - ((N + j : ℕ) : ℝ) * Real.log 2) by ring,
      hscale]
    ring
  rw [hremote]

/-- Source-level phase-adapted half-line decomposition.  After writing the even remainder as
`rho - exp(-x/2)/2`, the completion coefficient is exactly `(2^N tau + 1) / 4`.  This is the
coefficient used by `phaseAdaptedHalfLineProuhetEndpoint`; the older `+3` coefficient includes a
full-line term which the phase root has already annihilated. -/
theorem weighted_thetaSquareIndexDyadicHaarResidual_eq_phaseAdaptedSource
    (P : ℝ[X]) (tau : ℝ) (N : ℕ) (x : ℝ)
    (hq : P.eval dyadicProuhetDecayCharacter = 1)
    (hr : P.eval dyadicProuhetGrowthCharacter = tau) :
    ∑ j ∈ P.support,
        (P.coeff j * dyadicProuhetDecayCharacter ^ j) *
          thetaSquareIndexDyadicHaarResidual (N + j) x =
      dyadicEvenRemoteAmplitude N *
          (∑ j ∈ P.support, P.coeff j *
            thetaCuspTailSecondEvenRemainder
              (x - ((N + j : ℕ) : ℝ) * Real.log 2)) -
        thetaCuspTailSecondDensity x +
        (((2 : ℝ) ^ N * tau + 1) / 4) * Real.exp (-x / 2) := by
  rw [weighted_thetaSquareIndexDyadicHaarResidual_eq_evenTranslatePacket
    P tau N x hq hr]
  unfold thetaCuspTailSecondEvenRemainder
  ring

/-! ## Double-root removal of the full-line vector -/

/-- If a fixed-half-line translated value is written as its full-line phase translate minus a
returned forward-tail value, the phase-adapted packet removes the full-line vector exactly. -/
theorem phaseAdaptedProuhet_halfLineValue_sum_eq_neg_returned
    (F : ℂ) (B : ℕ → ℂ) (m : ℕ) (q r tau a L : ℝ) (z : ℂ) :
    let u : ℂ := spectralTranslationPhase L z
    let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau
    ∑ j ∈ P.support, (P.coeff j : ℂ) *
        (spectralTranslationPhase (a + (j : ℝ) * L) z * F - B j) =
      -∑ j ∈ P.support, (P.coeff j : ℂ) * B j := by
  dsimp only
  let u : ℂ := spectralTranslationPhase L z
  let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau
  have hfull :
      ∑ j ∈ P.support, (P.coeff j : ℂ) *
          (spectralTranslationPhase (a + (j : ℝ) * L) z * F) = 0 := by
    simpa only [P] using
      phaseAdaptedProuhet_oneSidedTranslationValue_sum_eq_zero
        F m q r tau a L z
  change ∑ j ∈ P.support, (P.coeff j : ℂ) *
      (spectralTranslationPhase (a + (j : ℝ) * L) z * F - B j) = _
  rw [show (∑ j ∈ P.support, (P.coeff j : ℂ) *
      (spectralTranslationPhase (a + (j : ℝ) * L) z * F - B j)) =
      (∑ j ∈ P.support, (P.coeff j : ℂ) *
        (spectralTranslationPhase (a + (j : ℝ) * L) z * F)) -
      ∑ j ∈ P.support, (P.coeff j : ℂ) * B j by
    simp only [mul_sub, Finset.sum_sub_distrib]]
  rw [hfull, zero_sub]

/-- Derivative companion.  The double root removes both the common derivative and the surviving
translate-index drift, so the returned derivative packet is the only term left. -/
theorem phaseAdaptedProuhet_halfLineDerivative_sum_eq_returned
    (F F' : ℂ) (B' : ℕ → ℂ) (m : ℕ)
    (q r tau a L : ℝ) (z : ℂ) :
    let u : ℂ := spectralTranslationPhase L z
    let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau
    ∑ j ∈ P.support, (P.coeff j : ℂ) *
        (spectralTranslationPhase (a + (j : ℝ) * L) z *
            (F' + (((a + (j : ℝ) * L : ℝ) : ℂ) * I) * F) + B' j) =
      ∑ j ∈ P.support, (P.coeff j : ℂ) * B' j := by
  dsimp only
  let u : ℂ := spectralTranslationPhase L z
  let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau
  have hfull :
      ∑ j ∈ P.support, (P.coeff j : ℂ) *
        (spectralTranslationPhase (a + (j : ℝ) * L) z *
          (F' + (((a + (j : ℝ) * L : ℝ) : ℂ) * I) * F)) = 0 := by
    simpa only [P] using
      phaseAdaptedProuhet_oneSidedTranslationDerivative_sum_eq_zero
        F F' m q r tau a L z
  change ∑ j ∈ P.support, (P.coeff j : ℂ) *
      (spectralTranslationPhase (a + (j : ℝ) * L) z *
        (F' + (((a + (j : ℝ) * L : ℝ) : ℂ) * I) * F) + B' j) = _
  rw [show (∑ j ∈ P.support, (P.coeff j : ℂ) *
      (spectralTranslationPhase (a + (j : ℝ) * L) z *
          (F' + (((a + (j : ℝ) * L : ℝ) : ℂ) * I) * F) + B' j)) =
      (∑ j ∈ P.support, (P.coeff j : ℂ) *
        (spectralTranslationPhase (a + (j : ℝ) * L) z *
          (F' + (((a + (j : ℝ) * L : ℝ) : ℂ) * I) * F))) +
      ∑ j ∈ P.support, (P.coeff j : ℂ) * B' j by
    simp only [mul_add, Finset.sum_add_distrib]]
  rw [hfull, zero_add]

/-- Current-level form of the fixed-half-line reduction.  The sign reversal between returned
value and returned derivative is the chain-rule sign from evaluating the forward tail at `-z`.
No full-line transform survives. -/
theorem phaseAdaptedProuhet_halfLineHermitianCross_eq_returned
    (F F' E E' : ℂ) (B B' : ℕ → ℂ) (m : ℕ)
    (q r tau a L : ℝ) (z : ℂ) :
    let u : ℂ := spectralTranslationPhase L z
    let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau
    let V := ∑ j ∈ P.support, (P.coeff j : ℂ) *
      (spectralTranslationPhase (a + (j : ℝ) * L) z * F - B j)
    let D := ∑ j ∈ P.support, (P.coeff j : ℂ) *
      (spectralTranslationPhase (a + (j : ℝ) * L) z *
          (F' + (((a + (j : ℝ) * L : ℝ) : ℂ) * I) * F) + B' j)
    symmetricHermitianCrossCurrentData V D E E' =
      symmetricHermitianCrossCurrentData
        (-∑ j ∈ P.support, (P.coeff j : ℂ) * B j)
        (∑ j ∈ P.support, (P.coeff j : ℂ) * B' j) E E' := by
  dsimp only
  rw [phaseAdaptedProuhet_halfLineValue_sum_eq_neg_returned,
    phaseAdaptedProuhet_halfLineDerivative_sum_eq_returned]

/-! ## Exact fixed-half-line phase translation -/

/-- Translating an even profile to the left across the fixed half-line gives its full-line phase
translate minus one forward tail evaluated in the opposite phase. -/
theorem integral_Ioi_evenProfile_leftTranslate_mul_phase_eq_full_sub_forward
    (g : ℝ → ℂ) (heven : ∀ x : ℝ, g (-x) = g x)
    (a : ℝ) (z : ℂ)
    (hf : Integrable (fun x : ℝ => g x * spectralTranslationPhase x z)) :
    (∫ x : ℝ in Ioi 0,
      g (x - a) * spectralTranslationPhase x z) =
      spectralTranslationPhase a z *
          (∫ y : ℝ, g y * spectralTranslationPhase y z) -
        ∫ x : ℝ in Ioi 0,
          g (x + a) * spectralTranslationPhase (-x) z := by
  let f : ℝ → ℂ := fun y => g y * spectralTranslationPhase y z
  have htranslate :
      (∫ x : ℝ in Ioi 0, f (x - a)) =
        ∫ y : ℝ in Ioi (-a), f y := by
    simpa only [sub_eq_add_neg] using
      integral_Ioi_comp_add_eq_integral_Ioi f (-a)
  have hsplit := integral_add_compl (s := Ioi (-a)) measurableSet_Ioi hf
  simp only [compl_Ioi] at hsplit
  have htail :
      spectralTranslationPhase a z * (∫ y : ℝ in Iic (-a), f y) =
        ∫ x : ℝ in Ioi 0,
          g (x + a) * spectralTranslationPhase (-x) z := by
    have href := integral_comp_neg_Ioi a f
    have hforward :=
      integral_Ioi_comp_add_eq_integral_Ioi (fun u : ℝ => f (-u)) a
    rw [← href, ← hforward, ← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    dsimp only [f]
    rw [heven]
    calc
      spectralTranslationPhase a z *
          (g (x + a) * spectralTranslationPhase (-(x + a)) z) =
        g (x + a) *
          (spectralTranslationPhase a z *
            spectralTranslationPhase (-(x + a)) z) := by ring
      _ = _ := by
        rw [show spectralTranslationPhase a z *
            spectralTranslationPhase (-(x + a)) z =
            spectralTranslationPhase (-x) z by
          rw [← spectralTranslationPhase_add]
          congr 1
          ring]
  rw [show (fun x : ℝ =>
      g (x - a) * spectralTranslationPhase x z) =
      fun x : ℝ => spectralTranslationPhase a z * f (x - a) by
    funext x
    dsimp only [f]
    rw [show spectralTranslationPhase x z =
        spectralTranslationPhase a z * spectralTranslationPhase (x - a) z by
      rw [← spectralTranslationPhase_add]
      congr 1
      ring]
    ring]
  rw [MeasureTheory.integral_const_mul, htranslate, ← hsplit, mul_add, htail]
  ring

/-- Spectral-derivative companion.  The reflected complement acquires the chain-rule sign, so
the forward-tail derivative is added while the forward-tail value was subtracted. -/
theorem integral_Ioi_evenProfile_leftTranslate_mul_phaseDerivative_eq_full_add_forward
    (g : ℝ → ℂ) (heven : ∀ x : ℝ, g (-x) = g x)
    (a : ℝ) (z : ℂ)
    (hf : Integrable (fun x : ℝ => g x * spectralTranslationPhase x z))
    (hf' : Integrable (fun x : ℝ =>
      g x * ((x : ℂ) * I * spectralTranslationPhase x z))) :
    (∫ x : ℝ in Ioi 0,
      g (x - a) * ((x : ℂ) * I * spectralTranslationPhase x z)) =
      spectralTranslationPhase a z *
          ((∫ y : ℝ,
              g y * ((y : ℂ) * I * spectralTranslationPhase y z)) +
            ((a : ℂ) * I) *
              (∫ y : ℝ, g y * spectralTranslationPhase y z)) +
        ∫ x : ℝ in Ioi 0,
          g (x + a) * ((x : ℂ) * I * spectralTranslationPhase (-x) z) := by
  let f : ℝ → ℂ := fun y => g y * spectralTranslationPhase y z
  let f' : ℝ → ℂ := fun y =>
    g y * ((y : ℂ) * I * spectralTranslationPhase y z)
  let k : ℝ → ℂ := fun y => f' y + ((a : ℂ) * I) * f y
  have hk : Integrable k := by
    exact hf'.add (hf.const_mul ((a : ℂ) * I))
  have htranslate :
      (∫ x : ℝ in Ioi 0, k (x - a)) =
        ∫ y : ℝ in Ioi (-a), k y := by
    simpa only [sub_eq_add_neg] using
      integral_Ioi_comp_add_eq_integral_Ioi k (-a)
  have hsplit := integral_add_compl (s := Ioi (-a)) measurableSet_Ioi hk
  simp only [compl_Ioi] at hsplit
  have htail :
      spectralTranslationPhase a z * (∫ y : ℝ in Iic (-a), k y) =
        -∫ x : ℝ in Ioi 0,
          g (x + a) * ((x : ℂ) * I * spectralTranslationPhase (-x) z) := by
    have href := integral_comp_neg_Ioi a k
    have hforward :=
      integral_Ioi_comp_add_eq_integral_Ioi (fun u : ℝ => k (-u)) a
    rw [← href, ← hforward, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_neg]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    dsimp only [k, f', f]
    rw [heven]
    have hphase : spectralTranslationPhase a z *
        spectralTranslationPhase (-(x + a)) z =
        spectralTranslationPhase (-x) z := by
      rw [← spectralTranslationPhase_add]
      congr 1
      ring
    rw [show spectralTranslationPhase a z *
        (g (x + a) *
            (((-(x + a) : ℝ) : ℂ) * I *
              spectralTranslationPhase (-(x + a)) z) +
          ((a : ℂ) * I) *
            (g (x + a) * spectralTranslationPhase (-(x + a)) z)) =
        g (x + a) *
          (((((-(x + a) : ℝ) : ℂ) + (a : ℂ)) * I) *
            (spectralTranslationPhase a z *
              spectralTranslationPhase (-(x + a)) z)) by ring,
      hphase]
    push_cast
    ring
  rw [show (fun x : ℝ =>
      g (x - a) * ((x : ℂ) * I * spectralTranslationPhase x z)) =
      fun x : ℝ => spectralTranslationPhase a z * k (x - a) by
    funext x
    dsimp only [k, f', f]
    rw [show spectralTranslationPhase x z =
        spectralTranslationPhase a z * spectralTranslationPhase (x - a) z by
      rw [← spectralTranslationPhase_add]
      congr 1
      ring]
    push_cast
    ring]
  have hkfull :
      (∫ y : ℝ, k y) =
        (∫ y : ℝ,
            g y * ((y : ℂ) * I * spectralTranslationPhase y z)) +
          ((a : ℂ) * I) *
            (∫ y : ℝ, g y * spectralTranslationPhase y z) := by
    unfold k f' f
    rw [MeasureTheory.integral_add hf' (hf.const_mul ((a : ℂ) * I)),
      MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_const_mul, htranslate, ← hkfull,
    ← hsplit, mul_add, htail]
  ring

/-! ## Canonical even-remainder integrability and returned-tail decay -/

/-- A convenient source-specific constant for the exact even remainder. -/
def thetaCuspTailSecondEvenRemainderExpHalfConstant : ℝ :=
  4 * thetaCuspTailDerivativeNatExpConstant 2 1 + 1 / 2

theorem thetaCuspTailDerivativeNatExpConstant_two_one_nonneg :
    0 ≤ thetaCuspTailDerivativeNatExpConstant 2 1 := by
  have h := abs_thetaCuspTailDerivative_le_nat_exp_neg 2 1
    (x := 0) (by norm_num : (0 : ℝ) ≤ 0)
  norm_num at h
  exact (abs_nonneg (thetaCuspTailDerivative 2 0)).trans h

theorem thetaCuspTailSecondEvenRemainderExpHalfConstant_nonneg :
    0 ≤ thetaCuspTailSecondEvenRemainderExpHalfConstant := by
  unfold thetaCuspTailSecondEvenRemainderExpHalfConstant
  positivity [thetaCuspTailDerivativeNatExpConstant_two_one_nonneg]

theorem continuous_thetaCuspTailSecondEvenRemainder :
    Continuous thetaCuspTailSecondEvenRemainder := by
  unfold thetaCuspTailSecondEvenRemainder thetaCuspTailSecondDensity
  exact (continuous_const.mul
      (differentiable_thetaCuspTailDerivative 2).continuous).sub
    (continuous_const.mul (by fun_prop))

private theorem norm_spectralTranslationPhase_neg_eq_exp_mul_im
    (x : ℝ) (z : ℂ) :
    ‖spectralTranslationPhase (-x) z‖ = Real.exp (x * z.im) := by
  unfold spectralTranslationPhase
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- On the positive half-line the exact even remainder has the sharp elementary decay rate
needed for the opposite phase.  The raw density itself is absorbed at the stronger rate `1`. -/
theorem abs_thetaCuspTailSecondEvenRemainder_le_exp_neg_half
    {x : ℝ} (hx : 0 ≤ x) :
    |thetaCuspTailSecondEvenRemainder x| ≤
      thetaCuspTailSecondEvenRemainderExpHalfConstant * Real.exp (-x / 2) := by
  have htail := abs_thetaCuspTailDerivative_le_nat_exp_neg 2 1 hx
  norm_num at htail
  have hexp : Real.exp (-x) ≤ Real.exp (-x / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  unfold thetaCuspTailSecondEvenRemainder thetaCuspTailSecondDensity
    thetaCuspTailSecondEvenRemainderExpHalfConstant
  calc
    |4 * thetaCuspTailDerivative 2 x - (1 / 2 : ℝ) * Real.exp (-x / 2)| ≤
        |4 * thetaCuspTailDerivative 2 x| +
          |(1 / 2 : ℝ) * Real.exp (-x / 2)| := abs_sub _ _
    _ = 4 * |thetaCuspTailDerivative 2 x| +
          (1 / 2 : ℝ) * Real.exp (-x / 2) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
        abs_of_pos (Real.exp_pos _)]
    _ ≤ 4 * (thetaCuspTailDerivativeNatExpConstant 2 1 * Real.exp (-x)) +
          (1 / 2 : ℝ) * Real.exp (-x / 2) := by
      gcongr
    _ ≤ 4 * (thetaCuspTailDerivativeNatExpConstant 2 1 * Real.exp (-x / 2)) +
          (1 / 2 : ℝ) * Real.exp (-x / 2) := by
      gcongr
      exact thetaCuspTailDerivativeNatExpConstant_two_one_nonneg
    _ = (4 * thetaCuspTailDerivativeNatExpConstant 2 1 + 1 / 2) *
          Real.exp (-x / 2) := by ring

theorem thetaCuspTailSecondEvenRemainder_tendsto_atTop_zero :
    Tendsto thetaCuspTailSecondEvenRemainder atTop (nhds 0) := by
  have htail : Tendsto (fun x : ℝ => 4 * thetaCuspTailDerivative 2 x)
      atTop (nhds 0) := by
    simpa using (thetaCuspTailDerivative_tendsto_atTop_zero 2).const_mul 4
  have hlin : Tendsto (fun x : ℝ => -x / 2) atTop atBot := by
    have h := tendsto_id.const_mul_atTop_of_neg
      (by norm_num : (-1 / 2 : ℝ) < 0)
    convert h using 1
    funext x
    simp only [id_eq]
    ring
  have hexp : Tendsto (fun x : ℝ => (1 / 2 : ℝ) * Real.exp (-x / 2))
      atTop (nhds 0) := by
    simpa using
      (Real.tendsto_exp_atBot.comp hlin).const_mul (1 / 2 : ℝ)
  simpa only [thetaCuspTailSecondEvenRemainder, thetaCuspTailSecondDensity,
    sub_zero] using htail.sub hexp

/-- Polynomial moments against an arbitrary strictly decaying real exponential are integrable
on the positive half-line. -/
theorem integrableOn_pow_mul_exp_neg_real (k : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-c * x)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (k : ℝ)) (p := (1 : ℝ)) (b := c)
    (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    (by norm_num) hc
  apply h.congr_fun
  · intro x hx
    have hx0 : 0 < x := mem_Ioi.mp hx
    change x ^ (k : ℝ) * Real.exp (-c * x ^ (1 : ℝ)) =
      x ^ k * Real.exp (-c * x)
    rw [Real.rpow_natCast, Real.rpow_one]
  · exact measurableSet_Ioi

/-- The positive-half-line opposite-phase transform of the exact even remainder is integrable
throughout the strict half-strip `Im z < 1/2`. -/
theorem integrableOn_thetaCuspTailSecondEvenRemainder_mul_negPhase
    {z : ℂ} (hz : z.im < 1 / 2) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondEvenRemainder x : ℂ) *
        spectralTranslationPhase (-x) z) (Ioi 0) := by
  let C := thetaCuspTailSecondEvenRemainderExpHalfConstant
  let c := (1 / 2 : ℝ) - z.im
  have hc : 0 < c := by dsimp only [c]; linarith
  have hmajorReal : IntegrableOn (fun x : ℝ => C * Real.exp (-c * x)) (Ioi 0) :=
    by
      simpa only [pow_zero, one_mul] using
        (integrableOn_pow_mul_exp_neg_real 0 hc).const_mul C
  change Integrable (fun x : ℝ =>
    (thetaCuspTailSecondEvenRemainder x : ℂ) *
      spectralTranslationPhase (-x) z) (volume.restrict (Ioi 0))
  apply Integrable.mono hmajorReal
  · exact ((Complex.continuous_ofReal.comp
      continuous_thetaCuspTailSecondEvenRemainder).mul
      (by unfold spectralTranslationPhase; fun_prop)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have hg := abs_thetaCuspTailSecondEvenRemainder_le_exp_neg_half hx0
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_spectralTranslationPhase_neg_eq_exp_mul_im]
    dsimp only [C, c]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      thetaCuspTailSecondEvenRemainderExpHalfConstant_nonneg (Real.exp_pos _).le)]
    calc
      |thetaCuspTailSecondEvenRemainder x| * Real.exp (x * z.im) ≤
          (thetaCuspTailSecondEvenRemainderExpHalfConstant * Real.exp (-x / 2)) *
            Real.exp (x * z.im) := by gcongr
      _ = thetaCuspTailSecondEvenRemainderExpHalfConstant *
          (Real.exp (-x / 2) * Real.exp (x * z.im)) := by ring
      _ = thetaCuspTailSecondEvenRemainderExpHalfConstant *
          Real.exp (-((1 / 2 : ℝ) - z.im) * x) := by
        rw [← Real.exp_add]
        congr 2
        ring

/-- Derivative companion of the opposite-phase integrability theorem. -/
theorem integrableOn_thetaCuspTailSecondEvenRemainder_mul_negPhaseDerivative
    {z : ℂ} (hz : z.im < 1 / 2) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondEvenRemainder x : ℂ) *
        ((x : ℂ) * I * spectralTranslationPhase (-x) z)) (Ioi 0) := by
  let C := thetaCuspTailSecondEvenRemainderExpHalfConstant
  let c := (1 / 2 : ℝ) - z.im
  have hc : 0 < c := by dsimp only [c]; linarith
  have hmajorReal : IntegrableOn
      (fun x : ℝ => C * (x ^ 1 * Real.exp (-c * x))) (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg_real 1 hc).const_mul C
  change Integrable (fun x : ℝ =>
    (thetaCuspTailSecondEvenRemainder x : ℂ) *
      ((x : ℂ) * I * spectralTranslationPhase (-x) z))
        (volume.restrict (Ioi 0))
  apply Integrable.mono hmajorReal
  · exact ((Complex.continuous_ofReal.comp
      continuous_thetaCuspTailSecondEvenRemainder).mul
      (by unfold spectralTranslationPhase; fun_prop)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have hg := abs_thetaCuspTailSecondEvenRemainder_le_exp_neg_half hx0
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_I, mul_one, norm_spectralTranslationPhase_neg_eq_exp_mul_im]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    dsimp only [C, c]
    rw [abs_of_nonneg (mul_nonneg
      thetaCuspTailSecondEvenRemainderExpHalfConstant_nonneg
      (mul_nonneg (pow_nonneg hx0 _) (Real.exp_pos _).le))]
    calc
      |thetaCuspTailSecondEvenRemainder x| *
          (x * Real.exp (x * z.im)) ≤
          (thetaCuspTailSecondEvenRemainderExpHalfConstant * Real.exp (-x / 2)) *
            (x * Real.exp (x * z.im)) := by gcongr
      _ = thetaCuspTailSecondEvenRemainderExpHalfConstant *
          (x ^ 1 * (Real.exp (-x / 2) * Real.exp (x * z.im))) := by
        simp only [pow_one]
        ring
      _ = thetaCuspTailSecondEvenRemainderExpHalfConstant *
          (x ^ 1 * Real.exp (-((1 / 2 : ℝ) - z.im) * x)) := by
        rw [← Real.exp_add]
        congr 3
        ring

/-- In the closed upper half-plane the ordinary phase is obtained from the opposite-phase theorem
by replacing `z` with `-z`. -/
theorem integrableOn_thetaCuspTailSecondEvenRemainder_mul_phase
    {z : ℂ} (hz : 0 ≤ z.im) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondEvenRemainder x : ℂ) *
        spectralTranslationPhase x z) (Ioi 0) := by
  have h := integrableOn_thetaCuspTailSecondEvenRemainder_mul_negPhase
    (z := -z) (by simp only [neg_im]; linarith)
  apply h.congr_fun
  · intro x _hx
    have hphase : spectralTranslationPhase (-x) (-z) =
        spectralTranslationPhase x z := by
      unfold spectralTranslationPhase
      congr 1
      push_cast
      ring
    change (thetaCuspTailSecondEvenRemainder x : ℂ) *
        spectralTranslationPhase (-x) (-z) =
      (thetaCuspTailSecondEvenRemainder x : ℂ) * spectralTranslationPhase x z
    rw [hphase]
  · exact measurableSet_Ioi

theorem integrableOn_thetaCuspTailSecondEvenRemainder_mul_phaseDerivative
    {z : ℂ} (hz : 0 ≤ z.im) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondEvenRemainder x : ℂ) *
        ((x : ℂ) * I * spectralTranslationPhase x z)) (Ioi 0) := by
  have h := integrableOn_thetaCuspTailSecondEvenRemainder_mul_negPhaseDerivative
    (z := -z) (by simp only [neg_im]; linarith)
  apply h.congr_fun
  · intro x _hx
    have hphase : spectralTranslationPhase (-x) (-z) =
        spectralTranslationPhase x z := by
      unfold spectralTranslationPhase
      congr 1
      push_cast
      ring
    change (thetaCuspTailSecondEvenRemainder x : ℂ) *
        ((x : ℂ) * I * spectralTranslationPhase (-x) (-z)) =
      (thetaCuspTailSecondEvenRemainder x : ℂ) *
        ((x : ℂ) * I * spectralTranslationPhase x z)
    rw [hphase]
  · exact measurableSet_Ioi

set_option maxHeartbeats 800000 in
/-- Full-line phase integrability of the exact even remainder in the upper critical half-strip. -/
theorem integrable_thetaCuspTailSecondEvenRemainder_mul_phase
    {z : ℂ} (hz0 : 0 ≤ z.im) (hz : z.im < 1 / 2) :
    Integrable (fun x : ℝ =>
      (thetaCuspTailSecondEvenRemainder x : ℂ) *
        spectralTranslationPhase x z) := by
  let f : ℝ → ℂ := fun x =>
    (thetaCuspTailSecondEvenRemainder x : ℂ) * spectralTranslationPhase x z
  let fopp : ℝ → ℂ := fun x =>
    (thetaCuspTailSecondEvenRemainder x : ℂ) * spectralTranslationPhase (-x) z
  have hpos : IntegrableOn f (Ioi 0) := by
    simpa only [f] using
      integrableOn_thetaCuspTailSecondEvenRemainder_mul_phase hz0
  have hopp : IntegrableOn fopp (Ioi 0) := by
    simpa only [fopp] using
      integrableOn_thetaCuspTailSecondEvenRemainder_mul_negPhase hz
  have hoppClosed : IntegrableOn fopp (Ici 0) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hopp
  have hoppClosed' : IntegrableOn fopp (Ici (-0)) := by
    simpa only [neg_zero] using hoppClosed
  have hnegRaw : IntegrableOn (fun x : ℝ => fopp (-x)) (Iic 0) :=
    hoppClosed'.comp_neg_Iic
  have hneg : IntegrableOn f (Iic 0) := by
    apply hnegRaw.congr_fun
    · intro x _hx
      simp only [fopp, f, neg_neg, thetaCuspTailSecondEvenRemainder_neg]
    · exact measurableSet_Iic
  change Integrable f
  simpa only [Ioi_union_Iic, IntegrableOn, Measure.restrict_univ] using
    hpos.union hneg

set_option maxHeartbeats 800000 in
/-- Full-line derivative integrability companion. -/
theorem integrable_thetaCuspTailSecondEvenRemainder_mul_phaseDerivative
    {z : ℂ} (hz0 : 0 ≤ z.im) (hz : z.im < 1 / 2) :
    Integrable (fun x : ℝ =>
      (thetaCuspTailSecondEvenRemainder x : ℂ) *
        ((x : ℂ) * I * spectralTranslationPhase x z)) := by
  let f : ℝ → ℂ := fun x =>
    (thetaCuspTailSecondEvenRemainder x : ℂ) *
      ((x : ℂ) * I * spectralTranslationPhase x z)
  let fopp : ℝ → ℂ := fun x =>
    (thetaCuspTailSecondEvenRemainder x : ℂ) *
      ((x : ℂ) * I * spectralTranslationPhase (-x) z)
  have hpos : IntegrableOn f (Ioi 0) := by
    simpa only [f] using
      integrableOn_thetaCuspTailSecondEvenRemainder_mul_phaseDerivative hz0
  have hopp : IntegrableOn fopp (Ioi 0) := by
    simpa only [fopp] using
      integrableOn_thetaCuspTailSecondEvenRemainder_mul_negPhaseDerivative hz
  have hoppClosed : IntegrableOn fopp (Ici 0) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hopp
  have hoppClosed' : IntegrableOn fopp (Ici (-0)) := by
    simpa only [neg_zero] using hoppClosed
  have hnegRaw : IntegrableOn (fun x : ℝ => fopp (-x)) (Iic 0) :=
    hoppClosed'.comp_neg_Iic
  have hneg : IntegrableOn f (Iic 0) := by
    have hnegRaw' := hnegRaw.neg
    apply hnegRaw'.congr_fun
    · intro x _hx
      dsimp only [fopp, f]
      simp only [neg_neg, thetaCuspTailSecondEvenRemainder_neg]
      simp only [Pi.neg_apply]
      push_cast
      ring
    · exact measurableSet_Iic
  change Integrable f
  simpa only [Ioi_union_Iic, IntegrableOn, Measure.restrict_univ] using
    hpos.union hneg

/-! ## Returned forward tails -/

/-- The boundary value returned when a left translate crosses the fixed positive half-line. -/
def thetaCuspTailSecondEvenRemainderReturnedValue (a : ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondEvenRemainder (x + a) : ℂ) *
      spectralTranslationPhase (-x) z

/-- Spectral derivative of the returned boundary value. -/
def thetaCuspTailSecondEvenRemainderReturnedDerivative (a : ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondEvenRemainder (x + a) : ℂ) *
      ((x : ℂ) * I * spectralTranslationPhase (-x) z)

/-- The returned boundary value vanishes as the translation depth tends to infinity. -/
theorem thetaCuspTailSecondEvenRemainderReturnedValue_tendsto_atTop_zero
    {z : ℂ} (hz : z.im < 1 / 2) :
    Tendsto (fun a : ℝ =>
      thetaCuspTailSecondEvenRemainderReturnedValue a z) atTop (nhds 0) := by
  let C := thetaCuspTailSecondEvenRemainderExpHalfConstant
  let c := (1 / 2 : ℝ) - z.im
  let F : ℝ → ℝ → ℂ := fun a x =>
    (thetaCuspTailSecondEvenRemainder (x + a) : ℂ) *
      spectralTranslationPhase (-x) z
  let bound : ℝ → ℝ := fun x => C * Real.exp (-c * x)
  have hc : 0 < c := by dsimp only [c]; linarith
  have hboundInt : Integrable bound (volume.restrict (Ioi 0)) := by
    change IntegrableOn (fun x : ℝ => C * Real.exp (-c * x)) (Ioi 0)
    simpa only [pow_zero, one_mul] using
      (integrableOn_pow_mul_exp_neg_real 0 hc).const_mul C
  have hFmeas : ∀ᶠ a : ℝ in atTop,
      AEStronglyMeasurable (F a) (volume.restrict (Ioi 0)) := by
    exact Eventually.of_forall fun a => by
      have hg : Continuous (fun x : ℝ =>
          thetaCuspTailSecondEvenRemainder (x + a)) :=
        continuous_thetaCuspTailSecondEvenRemainder.comp
          (continuous_id.add continuous_const)
      have hp : Continuous (fun x : ℝ => spectralTranslationPhase (-x) z) := by
        unfold spectralTranslationPhase
        fun_prop
      exact ((Complex.continuous_ofReal.comp hg).mul hp).aestronglyMeasurable.restrict
  have hbound : ∀ᶠ a : ℝ in atTop,
      ∀ᵐ x : ℝ ∂(volume.restrict (Ioi 0)), ‖F a x‖ ≤ bound x := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have hxa : 0 ≤ x + a := add_nonneg hx0 ha
    have hg := abs_thetaCuspTailSecondEvenRemainder_le_exp_neg_half hxa
    have hexpShift : Real.exp (-(x + a) / 2) ≤ Real.exp (-x / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    dsimp only [F, bound, C, c]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_spectralTranslationPhase_neg_eq_exp_mul_im]
    calc
      |thetaCuspTailSecondEvenRemainder (x + a)| * Real.exp (x * z.im) ≤
          (thetaCuspTailSecondEvenRemainderExpHalfConstant *
            Real.exp (-(x + a) / 2)) * Real.exp (x * z.im) := by gcongr
      _ ≤ (thetaCuspTailSecondEvenRemainderExpHalfConstant *
            Real.exp (-x / 2)) * Real.exp (x * z.im) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexpShift
            thetaCuspTailSecondEvenRemainderExpHalfConstant_nonneg)
          (Real.exp_pos _).le
      _ = thetaCuspTailSecondEvenRemainderExpHalfConstant *
          Real.exp (-((1 / 2 : ℝ) - z.im) * x) := by
        rw [show (thetaCuspTailSecondEvenRemainderExpHalfConstant *
              Real.exp (-x / 2)) * Real.exp (x * z.im) =
            thetaCuspTailSecondEvenRemainderExpHalfConstant *
              (Real.exp (-x / 2) * Real.exp (x * z.im)) by ring,
          ← Real.exp_add]
        congr 2
        ring
  have hlim : ∀ᵐ x : ℝ ∂(volume.restrict (Ioi 0)),
      Tendsto (fun a : ℝ => F a x) atTop (nhds (0 : ℂ)) := by
    filter_upwards with x
    have hshift : Tendsto (fun a : ℝ => x + a) atTop atTop :=
      tendsto_const_nhds.add_atTop tendsto_id
    have hgReal : Tendsto (fun a : ℝ =>
        thetaCuspTailSecondEvenRemainder (x + a)) atTop (nhds 0) :=
      thetaCuspTailSecondEvenRemainder_tendsto_atTop_zero.comp hshift
    have hg : Tendsto (fun a : ℝ =>
        (thetaCuspTailSecondEvenRemainder (x + a) : ℂ)) atTop (nhds 0) := by
      simpa using Complex.continuous_ofReal.continuousAt.tendsto.comp hgReal
    simpa only [F, zero_mul] using
      hg.mul_const (spectralTranslationPhase (-x) z)
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    bound hFmeas hbound hboundInt hlim
  simpa only [thetaCuspTailSecondEvenRemainderReturnedValue, F,
    MeasureTheory.integral_zero] using hDCT

/-- The returned spectral derivative also vanishes; the extra factor `x` remains integrable
because the strict strip gap is positive. -/
theorem thetaCuspTailSecondEvenRemainderReturnedDerivative_tendsto_atTop_zero
    {z : ℂ} (hz : z.im < 1 / 2) :
    Tendsto (fun a : ℝ =>
      thetaCuspTailSecondEvenRemainderReturnedDerivative a z) atTop (nhds 0) := by
  let C := thetaCuspTailSecondEvenRemainderExpHalfConstant
  let c := (1 / 2 : ℝ) - z.im
  let F : ℝ → ℝ → ℂ := fun a x =>
    (thetaCuspTailSecondEvenRemainder (x + a) : ℂ) *
      ((x : ℂ) * I * spectralTranslationPhase (-x) z)
  let bound : ℝ → ℝ := fun x => C * (x ^ 1 * Real.exp (-c * x))
  have hc : 0 < c := by dsimp only [c]; linarith
  have hboundInt : Integrable bound (volume.restrict (Ioi 0)) := by
    change IntegrableOn
      (fun x : ℝ => C * (x ^ 1 * Real.exp (-c * x))) (Ioi 0)
    exact (integrableOn_pow_mul_exp_neg_real 1 hc).const_mul C
  have hFmeas : ∀ᶠ a : ℝ in atTop,
      AEStronglyMeasurable (F a) (volume.restrict (Ioi 0)) := by
    exact Eventually.of_forall fun a => by
      have hg : Continuous (fun x : ℝ =>
          thetaCuspTailSecondEvenRemainder (x + a)) :=
        continuous_thetaCuspTailSecondEvenRemainder.comp
          (continuous_id.add continuous_const)
      have hp : Continuous (fun x : ℝ =>
          (x : ℂ) * I * spectralTranslationPhase (-x) z) := by
        unfold spectralTranslationPhase
        fun_prop
      exact ((Complex.continuous_ofReal.comp hg).mul hp).aestronglyMeasurable.restrict
  have hbound : ∀ᶠ a : ℝ in atTop,
      ∀ᵐ x : ℝ ∂(volume.restrict (Ioi 0)), ‖F a x‖ ≤ bound x := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have hxa : 0 ≤ x + a := add_nonneg hx0 ha
    have hg := abs_thetaCuspTailSecondEvenRemainder_le_exp_neg_half hxa
    have hexpShift : Real.exp (-(x + a) / 2) ≤ Real.exp (-x / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    dsimp only [F, bound, C, c]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_I, mul_one, norm_spectralTranslationPhase_neg_eq_exp_mul_im]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0, pow_one]
    calc
      |thetaCuspTailSecondEvenRemainder (x + a)| *
          (x * Real.exp (x * z.im)) ≤
          (thetaCuspTailSecondEvenRemainderExpHalfConstant *
            Real.exp (-(x + a) / 2)) * (x * Real.exp (x * z.im)) := by gcongr
      _ ≤ (thetaCuspTailSecondEvenRemainderExpHalfConstant *
            Real.exp (-x / 2)) * (x * Real.exp (x * z.im)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexpShift
            thetaCuspTailSecondEvenRemainderExpHalfConstant_nonneg)
          (mul_nonneg hx0 (Real.exp_pos _).le)
      _ = thetaCuspTailSecondEvenRemainderExpHalfConstant *
          (x * Real.exp (-((1 / 2 : ℝ) - z.im) * x)) := by
        rw [show (thetaCuspTailSecondEvenRemainderExpHalfConstant *
              Real.exp (-x / 2)) * (x * Real.exp (x * z.im)) =
            thetaCuspTailSecondEvenRemainderExpHalfConstant *
              (x * (Real.exp (-x / 2) * Real.exp (x * z.im))) by ring,
          ← Real.exp_add]
        congr 3
        ring
  have hlim : ∀ᵐ x : ℝ ∂(volume.restrict (Ioi 0)),
      Tendsto (fun a : ℝ => F a x) atTop (nhds (0 : ℂ)) := by
    filter_upwards with x
    have hshift : Tendsto (fun a : ℝ => x + a) atTop atTop :=
      tendsto_const_nhds.add_atTop tendsto_id
    have hgReal : Tendsto (fun a : ℝ =>
        thetaCuspTailSecondEvenRemainder (x + a)) atTop (nhds 0) :=
      thetaCuspTailSecondEvenRemainder_tendsto_atTop_zero.comp hshift
    have hg : Tendsto (fun a : ℝ =>
        (thetaCuspTailSecondEvenRemainder (x + a) : ℂ)) atTop (nhds 0) := by
      simpa using Complex.continuous_ofReal.continuousAt.tendsto.comp hgReal
    simpa only [F, zero_mul] using
      hg.mul_const (((x : ℂ) * I) * spectralTranslationPhase (-x) z)
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    bound hFmeas hbound hboundInt hlim
  simpa only [thetaCuspTailSecondEvenRemainderReturnedDerivative, F,
    MeasureTheory.integral_zero] using hDCT

/-! ## Exact canonical instantiation of the fixed-half-line translation formulas -/

theorem integral_Ioi_thetaCuspTailSecondEvenRemainder_leftTranslate_mul_phase
    (a : ℝ) {z : ℂ} (hz0 : 0 ≤ z.im) (hz : z.im < 1 / 2) :
    (∫ x : ℝ in Ioi 0,
      (thetaCuspTailSecondEvenRemainder (x - a) : ℂ) *
        spectralTranslationPhase x z) =
      spectralTranslationPhase a z *
          (∫ y : ℝ,
            (thetaCuspTailSecondEvenRemainder y : ℂ) *
              spectralTranslationPhase y z) -
        thetaCuspTailSecondEvenRemainderReturnedValue a z := by
  have heven : ∀ x : ℝ,
      (thetaCuspTailSecondEvenRemainder (-x) : ℂ) =
        (thetaCuspTailSecondEvenRemainder x : ℂ) := by
    intro x
    rw [thetaCuspTailSecondEvenRemainder_neg]
  simpa only [thetaCuspTailSecondEvenRemainderReturnedValue] using
    integral_Ioi_evenProfile_leftTranslate_mul_phase_eq_full_sub_forward
      (g := fun x : ℝ => (thetaCuspTailSecondEvenRemainder x : ℂ))
      heven a z
      (integrable_thetaCuspTailSecondEvenRemainder_mul_phase hz0 hz)

theorem integral_Ioi_thetaCuspTailSecondEvenRemainder_leftTranslate_mul_phaseDerivative
    (a : ℝ) {z : ℂ} (hz0 : 0 ≤ z.im) (hz : z.im < 1 / 2) :
    (∫ x : ℝ in Ioi 0,
      (thetaCuspTailSecondEvenRemainder (x - a) : ℂ) *
        ((x : ℂ) * I * spectralTranslationPhase x z)) =
      spectralTranslationPhase a z *
          ((∫ y : ℝ,
              (thetaCuspTailSecondEvenRemainder y : ℂ) *
                ((y : ℂ) * I * spectralTranslationPhase y z)) +
            ((a : ℂ) * I) *
              (∫ y : ℝ,
                (thetaCuspTailSecondEvenRemainder y : ℂ) *
                  spectralTranslationPhase y z)) +
        thetaCuspTailSecondEvenRemainderReturnedDerivative a z := by
  have heven : ∀ x : ℝ,
      (thetaCuspTailSecondEvenRemainder (-x) : ℂ) =
        (thetaCuspTailSecondEvenRemainder x : ℂ) := by
    intro x
    rw [thetaCuspTailSecondEvenRemainder_neg]
  simpa only [thetaCuspTailSecondEvenRemainderReturnedDerivative] using
    integral_Ioi_evenProfile_leftTranslate_mul_phaseDerivative_eq_full_add_forward
      (g := fun x : ℝ => (thetaCuspTailSecondEvenRemainder x : ℂ))
      heven a z
      (integrable_thetaCuspTailSecondEvenRemainder_mul_phase hz0 hz)
      (integrable_thetaCuspTailSecondEvenRemainder_mul_phaseDerivative hz0 hz)

/-- The actual translated theta remainder packet has no full-line value component: the prescribed
phase root leaves exactly the negative finite packet of returned forward tails. -/
theorem phaseAdaptedProuhet_evenRemainderHalfLineValue_sum_eq_neg_returned
    (m N : ℕ) (q r tau L : ℝ) {z : ℂ}
    (hz0 : 0 ≤ z.im) (hz : z.im < 1 / 2) :
    let u : ℂ := spectralTranslationPhase L z
    let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau
    ∑ j ∈ P.support, (P.coeff j : ℂ) *
        (∫ x : ℝ in Ioi 0,
          (thetaCuspTailSecondEvenRemainder
            (x - ((N + j : ℕ) : ℝ) * L) : ℂ) *
              spectralTranslationPhase x z) =
      -∑ j ∈ P.support, (P.coeff j : ℂ) *
        thetaCuspTailSecondEvenRemainderReturnedValue
          (((N + j : ℕ) : ℝ) * L) z := by
  dsimp only
  let F : ℂ := ∫ y : ℝ,
    (thetaCuspTailSecondEvenRemainder y : ℂ) * spectralTranslationPhase y z
  let B : ℕ → ℂ := fun j =>
    thetaCuspTailSecondEvenRemainderReturnedValue
      (((N + j : ℕ) : ℝ) * L) z
  have habstract := phaseAdaptedProuhet_halfLineValue_sum_eq_neg_returned
    F B m q r tau ((N : ℝ) * L) L z
  dsimp only at habstract
  rw [← habstract]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [integral_Ioi_thetaCuspTailSecondEvenRemainder_leftTranslate_mul_phase
    (((N + j : ℕ) : ℝ) * L) hz0 hz]
  dsimp only [F, B]
  rw [show (((N + j : ℕ) : ℝ) * L) =
      (N : ℝ) * L + (j : ℝ) * L by push_cast; ring]

/-- Derivative companion: the double root removes both the common derivative and the translate
drift, leaving exactly the positive finite packet of returned derivative tails. -/
theorem phaseAdaptedProuhet_evenRemainderHalfLineDerivative_sum_eq_returned
    (m N : ℕ) (q r tau L : ℝ) {z : ℂ}
    (hz0 : 0 ≤ z.im) (hz : z.im < 1 / 2) :
    let u : ℂ := spectralTranslationPhase L z
    let P := phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau
    ∑ j ∈ P.support, (P.coeff j : ℂ) *
        (∫ x : ℝ in Ioi 0,
          (thetaCuspTailSecondEvenRemainder
            (x - ((N + j : ℕ) : ℝ) * L) : ℂ) *
              ((x : ℂ) * I * spectralTranslationPhase x z)) =
      ∑ j ∈ P.support, (P.coeff j : ℂ) *
        thetaCuspTailSecondEvenRemainderReturnedDerivative
          (((N + j : ℕ) : ℝ) * L) z := by
  dsimp only
  let F : ℂ := ∫ y : ℝ,
    (thetaCuspTailSecondEvenRemainder y : ℂ) * spectralTranslationPhase y z
  let F' : ℂ := ∫ y : ℝ,
    (thetaCuspTailSecondEvenRemainder y : ℂ) *
      ((y : ℂ) * I * spectralTranslationPhase y z)
  let B' : ℕ → ℂ := fun j =>
    thetaCuspTailSecondEvenRemainderReturnedDerivative
      (((N + j : ℕ) : ℝ) * L) z
  have habstract := phaseAdaptedProuhet_halfLineDerivative_sum_eq_returned
    F F' B' m q r tau ((N : ℝ) * L) L z
  dsimp only at habstract
  rw [← habstract]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [integral_Ioi_thetaCuspTailSecondEvenRemainder_leftTranslate_mul_phaseDerivative
    (((N + j : ℕ) : ℝ) * L) hz0 hz]
  dsimp only [F, F', B']
  rw [show (((N + j : ℕ) : ℝ) * L) =
      (N : ℝ) * L + (j : ℝ) * L by push_cast; ring]

/-! ## Cofinal decay with the moving right endpoint -/

/-- The polynomial multiplying the moving right-endpoint parameter. -/
def phaseAdaptedTwoEndpointProuhetEndpointSlope
    (m : ℕ) (u : ℂ) (q r : ℝ) : ℝ[X] :=
  let B := phaseAdaptedProuhetBase m u
  let gamma := (B.eval r)⁻¹ / (r - q)
  B * (C (-gamma * q) + C gamma * X)

/-- The phase-adapted packet is affine, not merely continuous, in its right endpoint. -/
theorem phaseAdaptedTwoEndpointProuhetPolynomial_eq_zero_add_smul_slope
    (m : ℕ) (u : ℂ) (q r tau : ℝ) :
    phaseAdaptedTwoEndpointProuhetPolynomial m u q r tau =
      phaseAdaptedTwoEndpointProuhetPolynomial m u q r 0 +
        tau • phaseAdaptedTwoEndpointProuhetEndpointSlope m u q r := by
  let B := phaseAdaptedProuhetBase m u
  let left := (B.eval q)⁻¹
  let invR := (B.eval r)⁻¹
  let gamma := invR / (r - q)
  let beta : ℝ → ℝ := fun t => (t * invR - left) / (r - q)
  let alpha : ℝ → ℝ := fun t => left - beta t * q
  have hbeta : beta tau = beta 0 + tau * gamma := by
    dsimp only [beta, gamma]
    ring
  have halpha : alpha tau = alpha 0 + tau * (-gamma * q) := by
    dsimp only [alpha]
    rw [hbeta]
    ring
  have hlinear : C (alpha tau) + C (beta tau) * X =
      (C (alpha 0) + C (beta 0) * X) +
        tau • (C (-gamma * q) + C gamma * X) := by
    ext n
    cases n with
    | zero =>
        simpa [halpha]
    | succ n =>
        cases n with
        | zero =>
            simpa [hbeta]
        | succ n =>
            simp
  change B * (C (alpha tau) + C (beta tau) * X) =
    B * (C (alpha 0) + C (beta 0) * X) +
      tau • (B * (C (-gamma * q) + C gamma * X))
  rw [hlinear, mul_add]
  congr 1
  simp only [Polynomial.smul_eq_C_mul]
  ring

/-- Complex pairing of a real polynomial's coefficients with an arbitrary indexed packet. -/
def realPolynomialComplexCoefficientPairing
    (P : ℝ[X]) (B : ℕ → ℂ) : ℂ :=
  P.sum fun j c => (c : ℂ) * B j

theorem realPolynomialComplexCoefficientPairing_add
    (P Q : ℝ[X]) (B : ℕ → ℂ) :
    realPolynomialComplexCoefficientPairing (P + Q) B =
      realPolynomialComplexCoefficientPairing P B +
        realPolynomialComplexCoefficientPairing Q B := by
  unfold realPolynomialComplexCoefficientPairing
  exact Polynomial.sum_add_index P Q _
    (fun _j => by simp)
    (fun _j a b => by push_cast; ring)

theorem realPolynomialComplexCoefficientPairing_smul
    (tau : ℝ) (P : ℝ[X]) (B : ℕ → ℂ) :
    realPolynomialComplexCoefficientPairing (tau • P) B =
      (tau : ℂ) * realPolynomialComplexCoefficientPairing P B := by
  unfold realPolynomialComplexCoefficientPairing
  rw [Polynomial.sum_smul_index]
  · change (∑ n ∈ P.support, ((tau * P.coeff n : ℝ) : ℂ) * B n) =
      (tau : ℂ) * ∑ n ∈ P.support, (P.coeff n : ℂ) * B n
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    push_cast
    ring
  · intro _j
    simp

/-- A fixed finite coefficient packet preserves pointwise cofinal convergence to zero. -/
theorem realPolynomialComplexCoefficientPairing_tendsto_atTop_zero
    (P : ℝ[X]) (B : ℕ → ℕ → ℂ)
    (hB : ∀ j : ℕ, Tendsto (fun N : ℕ => B N j) atTop (nhds 0)) :
    Tendsto (fun N : ℕ =>
      realPolynomialComplexCoefficientPairing P (B N)) atTop (nhds 0) := by
  unfold realPolynomialComplexCoefficientPairing Polynomial.sum
  have hsum := tendsto_finset_sum P.support (fun j _hj =>
    (hB j).const_mul (P.coeff j : ℂ))
  simpa using hsum

/-- Affine endpoint packets retain cofinal decay when their endpoint parameter tends to zero. -/
theorem phaseAdaptedProuhetCoefficientPairing_tendsto_of_endpoint_tendsto_zero
    (m : ℕ) (u : ℂ) (q r : ℝ) (tau : ℕ → ℝ)
    (B : ℕ → ℕ → ℂ)
    (htau : Tendsto tau atTop (nhds 0))
    (hB : ∀ j : ℕ, Tendsto (fun N : ℕ => B N j) atTop (nhds 0)) :
    Tendsto (fun N : ℕ =>
      realPolynomialComplexCoefficientPairing
        (phaseAdaptedTwoEndpointProuhetPolynomial m u q r (tau N)) (B N))
      atTop (nhds 0) := by
  let P0 := phaseAdaptedTwoEndpointProuhetPolynomial m u q r 0
  let S := phaseAdaptedTwoEndpointProuhetEndpointSlope m u q r
  have hP0 := realPolynomialComplexCoefficientPairing_tendsto_atTop_zero P0 B hB
  have hS := realPolynomialComplexCoefficientPairing_tendsto_atTop_zero S B hB
  have htauC : Tendsto (fun N : ℕ => (tau N : ℂ)) atTop (nhds 0) := by
    simpa using Complex.continuous_ofReal.continuousAt.tendsto.comp htau
  have htotal := hP0.add (htauC.mul hS)
  convert htotal using 1
  · funext N
    rw [phaseAdaptedTwoEndpointProuhetPolynomial_eq_zero_add_smul_slope,
      realPolynomialComplexCoefficientPairing_add,
      realPolynomialComplexCoefficientPairing_smul]
  · ring

/-- Every fixed translate index of the returned value packet vanishes along a positive dyadic
depth ray. -/
theorem thetaCuspTailSecondEvenRemainderReturnedValue_natDepth_tendsto_zero
    {L : ℝ} (hL : 0 < L) {z : ℂ} (hz : z.im < 1 / 2) (j : ℕ) :
    Tendsto (fun N : ℕ =>
      thetaCuspTailSecondEvenRemainderReturnedValue
        (((N + j : ℕ) : ℝ) * L) z) atTop (nhds 0) := by
  have hdepth : Tendsto (fun N : ℕ => (((N + j : ℕ) : ℝ) * L))
      atTop atTop := by
    have hcast : Tendsto (fun N : ℕ => ((N + j : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat j)
    simpa only [mul_comm] using hcast.const_mul_atTop hL
  exact thetaCuspTailSecondEvenRemainderReturnedValue_tendsto_atTop_zero hz |>.comp hdepth

theorem thetaCuspTailSecondEvenRemainderReturnedDerivative_natDepth_tendsto_zero
    {L : ℝ} (hL : 0 < L) {z : ℂ} (hz : z.im < 1 / 2) (j : ℕ) :
    Tendsto (fun N : ℕ =>
      thetaCuspTailSecondEvenRemainderReturnedDerivative
        (((N + j : ℕ) : ℝ) * L) z) atTop (nhds 0) := by
  have hdepth : Tendsto (fun N : ℕ => (((N + j : ℕ) : ℝ) * L))
      atTop atTop := by
    have hcast : Tendsto (fun N : ℕ => ((N + j : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat j)
    simpa only [mul_comm] using hcast.const_mul_atTop hL
  exact thetaCuspTailSecondEvenRemainderReturnedDerivative_tendsto_atTop_zero hz |>.comp hdepth

/-- The complete returned value packet vanishes even while the right endpoint moves to zero. -/
theorem phaseAdaptedProuhet_returnedValuePairing_tendsto_atTop_zero
    (m : ℕ) (u : ℂ) (q r : ℝ) (tau : ℕ → ℝ)
    {L : ℝ} (hL : 0 < L) {z : ℂ} (hz : z.im < 1 / 2)
    (htau : Tendsto tau atTop (nhds 0)) :
    Tendsto (fun N : ℕ =>
      realPolynomialComplexCoefficientPairing
        (phaseAdaptedTwoEndpointProuhetPolynomial m u q r (tau N))
        (fun j => thetaCuspTailSecondEvenRemainderReturnedValue
          (((N + j : ℕ) : ℝ) * L) z)) atTop (nhds 0) := by
  exact phaseAdaptedProuhetCoefficientPairing_tendsto_of_endpoint_tendsto_zero
    m u q r tau _ htau
      (thetaCuspTailSecondEvenRemainderReturnedValue_natDepth_tendsto_zero hL hz)

/-- Derivative companion for the complete moving-endpoint packet. -/
theorem phaseAdaptedProuhet_returnedDerivativePairing_tendsto_atTop_zero
    (m : ℕ) (u : ℂ) (q r : ℝ) (tau : ℕ → ℝ)
    {L : ℝ} (hL : 0 < L) {z : ℂ} (hz : z.im < 1 / 2)
    (htau : Tendsto tau atTop (nhds 0)) :
    Tendsto (fun N : ℕ =>
      realPolynomialComplexCoefficientPairing
        (phaseAdaptedTwoEndpointProuhetPolynomial m u q r (tau N))
        (fun j => thetaCuspTailSecondEvenRemainderReturnedDerivative
          (((N + j : ℕ) : ℝ) * L) z)) atTop (nhds 0) := by
  exact phaseAdaptedProuhetCoefficientPairing_tendsto_of_endpoint_tendsto_zero
    m u q r tau _ htau
      (thetaCuspTailSecondEvenRemainderReturnedDerivative_natDepth_tendsto_zero hL hz)

/-! ## Critical scaling: exact completion boundary plus a vanishing density tail -/

def thetaCuspTailSecondDensityExpOneConstant : ℝ :=
  4 * thetaCuspTailDerivativeNatExpConstant 2 1

theorem thetaCuspTailSecondDensityExpOneConstant_nonneg :
    0 ≤ thetaCuspTailSecondDensityExpOneConstant := by
  unfold thetaCuspTailSecondDensityExpOneConstant
  positivity [thetaCuspTailDerivativeNatExpConstant_two_one_nonneg]

theorem abs_thetaCuspTailSecondDensity_le_exp_neg_one
    {x : ℝ} (hx : 0 ≤ x) :
    |thetaCuspTailSecondDensity x| ≤
      thetaCuspTailSecondDensityExpOneConstant * Real.exp (-x) := by
  have h := abs_thetaCuspTailDerivative_le_nat_exp_neg 2 1 hx
  norm_num at h
  unfold thetaCuspTailSecondDensity thetaCuspTailSecondDensityExpOneConstant
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  gcongr

/-- Opposite-phase transform of the elementary completion character. -/
def thetaHalfExponentialOppositePhaseValue (z : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (Real.exp (-x / 2) : ℂ) * spectralTranslationPhase (-x) z

def thetaHalfExponentialOppositePhaseDerivative (z : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (Real.exp (-x / 2) : ℂ) *
      ((x : ℂ) * I * spectralTranslationPhase (-x) z)

def thetaCuspTailSecondDensityReturnedValue (a : ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondDensity (x + a) : ℂ) *
      spectralTranslationPhase (-x) z

def thetaCuspTailSecondDensityReturnedDerivative (a : ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 0,
    (thetaCuspTailSecondDensity (x + a) : ℂ) *
      ((x : ℂ) * I * spectralTranslationPhase (-x) z)

private theorem integrableOn_thetaHalfExponential_mul_negPhase
    {z : ℂ} (hz : z.im < 1 / 2) :
    IntegrableOn (fun x : ℝ =>
      (Real.exp (-x / 2) : ℂ) * spectralTranslationPhase (-x) z) (Ioi 0) := by
  let c := (1 / 2 : ℝ) - z.im
  have hc : 0 < c := by dsimp only [c]; linarith
  have hmajor := integrableOn_pow_mul_exp_neg_real 0 hc
  change Integrable (fun x : ℝ =>
    (Real.exp (-x / 2) : ℂ) * spectralTranslationPhase (-x) z)
      (volume.restrict (Ioi 0))
  apply Integrable.mono hmajor
  · exact ((by fun_prop : Continuous (fun x : ℝ => (Real.exp (-x / 2) : ℂ))) |>.mul
      (by unfold spectralTranslationPhase; fun_prop)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), norm_spectralTranslationPhase_neg_eq_exp_mul_im]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hx.le 0)
      (Real.exp_pos _).le)]
    simp only [pow_zero, one_mul]
    dsimp only [c]
    rw [← Real.exp_add]
    congr 1
    ring

private theorem integrableOn_thetaHalfExponential_mul_negPhaseDerivative
    {z : ℂ} (hz : z.im < 1 / 2) :
    IntegrableOn (fun x : ℝ =>
      (Real.exp (-x / 2) : ℂ) *
        ((x : ℂ) * I * spectralTranslationPhase (-x) z)) (Ioi 0) := by
  let c := (1 / 2 : ℝ) - z.im
  have hc : 0 < c := by dsimp only [c]; linarith
  have hmajor := integrableOn_pow_mul_exp_neg_real 1 hc
  change Integrable (fun x : ℝ =>
    (Real.exp (-x / 2) : ℂ) *
      ((x : ℂ) * I * spectralTranslationPhase (-x) z))
        (volume.restrict (Ioi 0))
  apply Integrable.mono hmajor
  · exact ((by fun_prop : Continuous (fun x : ℝ => (Real.exp (-x / 2) : ℂ))) |>.mul
      (by unfold spectralTranslationPhase; fun_prop)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_I, mul_one, abs_of_pos (Real.exp_pos _),
      norm_spectralTranslationPhase_neg_eq_exp_mul_im]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.le, pow_one]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx.le (Real.exp_pos _).le)]
    dsimp only [c]
    rw [← Real.exp_add]
    congr 2
    ring

theorem integrableOn_thetaCuspTailSecondDensity_shift_mul_negPhase
    {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : z.im < 1 / 2) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensity (x + a) : ℂ) *
        spectralTranslationPhase (-x) z) (Ioi 0) := by
  let C := thetaCuspTailSecondDensityExpOneConstant
  let c := (1 : ℝ) - z.im
  have hc : 0 < c := by dsimp only [c]; linarith
  have hmajor : IntegrableOn (fun x : ℝ => C * Real.exp (-c * x)) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using
      (integrableOn_pow_mul_exp_neg_real 0 hc).const_mul C
  change Integrable (fun x : ℝ =>
    (thetaCuspTailSecondDensity (x + a) : ℂ) *
      spectralTranslationPhase (-x) z) (volume.restrict (Ioi 0))
  apply Integrable.mono hmajor
  · have hrho : Continuous thetaCuspTailSecondDensity := by
      unfold thetaCuspTailSecondDensity
      exact continuous_const.mul (differentiable_thetaCuspTailDerivative 2).continuous
    exact ((Complex.continuous_ofReal.comp
      (hrho.comp (continuous_id.add continuous_const))).mul
        (by unfold spectralTranslationPhase; fun_prop)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have hxa : 0 ≤ x + a := add_nonneg hx0 ha
    have hrho := abs_thetaCuspTailSecondDensity_le_exp_neg_one hxa
    have hexpShift : Real.exp (-(x + a)) ≤ Real.exp (-x) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_spectralTranslationPhase_neg_eq_exp_mul_im]
    dsimp only [C, c]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      thetaCuspTailSecondDensityExpOneConstant_nonneg (Real.exp_pos _).le)]
    calc
      |thetaCuspTailSecondDensity (x + a)| * Real.exp (x * z.im) ≤
          (thetaCuspTailSecondDensityExpOneConstant * Real.exp (-(x + a))) *
            Real.exp (x * z.im) := by gcongr
      _ ≤ (thetaCuspTailSecondDensityExpOneConstant * Real.exp (-x)) *
            Real.exp (x * z.im) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexpShift
            thetaCuspTailSecondDensityExpOneConstant_nonneg)
          (Real.exp_pos _).le
      _ = thetaCuspTailSecondDensityExpOneConstant *
          Real.exp (-((1 : ℝ) - z.im) * x) := by
        rw [show (thetaCuspTailSecondDensityExpOneConstant * Real.exp (-x)) *
              Real.exp (x * z.im) = thetaCuspTailSecondDensityExpOneConstant *
                (Real.exp (-x) * Real.exp (x * z.im)) by ring,
          ← Real.exp_add]
        congr 2
        ring

theorem integrableOn_thetaCuspTailSecondDensity_shift_mul_negPhaseDerivative
    {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : z.im < 1 / 2) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensity (x + a) : ℂ) *
        ((x : ℂ) * I * spectralTranslationPhase (-x) z)) (Ioi 0) := by
  let C := thetaCuspTailSecondDensityExpOneConstant
  let c := (1 : ℝ) - z.im
  have hc : 0 < c := by dsimp only [c]; linarith
  have hmajor : IntegrableOn
      (fun x : ℝ => C * (x ^ 1 * Real.exp (-c * x))) (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg_real 1 hc).const_mul C
  change Integrable (fun x : ℝ =>
    (thetaCuspTailSecondDensity (x + a) : ℂ) *
      ((x : ℂ) * I * spectralTranslationPhase (-x) z))
        (volume.restrict (Ioi 0))
  apply Integrable.mono hmajor
  · have hrho : Continuous thetaCuspTailSecondDensity := by
      unfold thetaCuspTailSecondDensity
      exact continuous_const.mul (differentiable_thetaCuspTailDerivative 2).continuous
    exact ((Complex.continuous_ofReal.comp
      (hrho.comp (continuous_id.add continuous_const))).mul
        (by unfold spectralTranslationPhase; fun_prop)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have hxa : 0 ≤ x + a := add_nonneg hx0 ha
    have hrho := abs_thetaCuspTailSecondDensity_le_exp_neg_one hxa
    have hexpShift : Real.exp (-(x + a)) ≤ Real.exp (-x) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_I, mul_one, norm_spectralTranslationPhase_neg_eq_exp_mul_im]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0, pow_one]
    dsimp only [C, c]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      thetaCuspTailSecondDensityExpOneConstant_nonneg
        (mul_nonneg hx0 (Real.exp_pos _).le))]
    calc
      |thetaCuspTailSecondDensity (x + a)| * (x * Real.exp (x * z.im)) ≤
          (thetaCuspTailSecondDensityExpOneConstant * Real.exp (-(x + a))) *
            (x * Real.exp (x * z.im)) := by gcongr
      _ ≤ (thetaCuspTailSecondDensityExpOneConstant * Real.exp (-x)) *
            (x * Real.exp (x * z.im)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexpShift
            thetaCuspTailSecondDensityExpOneConstant_nonneg)
          (mul_nonneg hx0 (Real.exp_pos _).le)
      _ = thetaCuspTailSecondDensityExpOneConstant *
          (x * Real.exp (-((1 : ℝ) - z.im) * x)) := by
        rw [show (thetaCuspTailSecondDensityExpOneConstant * Real.exp (-x)) *
              (x * Real.exp (x * z.im)) = thetaCuspTailSecondDensityExpOneConstant *
                (x * (Real.exp (-x) * Real.exp (x * z.im))) by ring,
          ← Real.exp_add]
        congr 3
        ring

theorem exp_half_mul_thetaCuspTailSecondDensity_shift_tendsto_zero (x : ℝ) :
    Tendsto (fun a : ℝ =>
      Real.exp (a / 2) * thetaCuspTailSecondDensity (x + a))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let K := thetaCuspTailSecondDensityExpOneConstant * Real.exp (-x)
  have hlin : Tendsto (fun a : ℝ => -a / 2) atTop atBot := by
    have h := tendsto_id.const_mul_atTop_of_neg
      (by norm_num : (-1 / 2 : ℝ) < 0)
    convert h using 1
    funext a
    simp only [id_eq]
    ring
  have hmajor : Tendsto (fun a : ℝ => K * Real.exp (-a / 2))
      atTop (nhds 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hlin).const_mul K
  apply squeeze_zero' (Eventually.of_forall fun a => norm_nonneg _) ?_ hmajor
  filter_upwards [eventually_ge_atTop (-x)] with a ha
  have hxa : 0 ≤ x + a := by linarith
  have hrho := abs_thetaCuspTailSecondDensity_le_exp_neg_one hxa
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  dsimp only [K]
  calc
    Real.exp (a / 2) * |thetaCuspTailSecondDensity (x + a)| ≤
        Real.exp (a / 2) *
          (thetaCuspTailSecondDensityExpOneConstant * Real.exp (-(x + a))) := by
      gcongr
    _ = thetaCuspTailSecondDensityExpOneConstant * Real.exp (-x) *
        Real.exp (-a / 2) := by
      rw [show Real.exp (a / 2) *
          (thetaCuspTailSecondDensityExpOneConstant * Real.exp (-(x + a))) =
        thetaCuspTailSecondDensityExpOneConstant *
          (Real.exp (a / 2) * Real.exp (-(x + a))) by ring,
        ← Real.exp_add]
      congr 1
      ring

theorem thetaCuspTailSecondDensityReturnedValue_scaled_tendsto_zero
    {z : ℂ} (hz : z.im < 1 / 2) :
    Tendsto (fun a : ℝ =>
      (Real.exp (a / 2) : ℂ) *
        thetaCuspTailSecondDensityReturnedValue a z) atTop (nhds 0) := by
  let C := thetaCuspTailSecondDensityExpOneConstant
  let c := (1 : ℝ) - z.im
  let F : ℝ → ℝ → ℂ := fun a x =>
    ((Real.exp (a / 2) * thetaCuspTailSecondDensity (x + a) : ℝ) : ℂ) *
      spectralTranslationPhase (-x) z
  let bound : ℝ → ℝ := fun x => C * Real.exp (-c * x)
  have hc : 0 < c := by dsimp only [c]; linarith
  have hboundInt : Integrable bound (volume.restrict (Ioi 0)) := by
    change IntegrableOn (fun x : ℝ => C * Real.exp (-c * x)) (Ioi 0)
    simpa only [pow_zero, one_mul] using
      (integrableOn_pow_mul_exp_neg_real 0 hc).const_mul C
  have hFmeas : ∀ᶠ a : ℝ in atTop,
      AEStronglyMeasurable (F a) (volume.restrict (Ioi 0)) := by
    exact Eventually.of_forall fun a => by
      have hrho : Continuous (fun x : ℝ =>
          Real.exp (a / 2) * thetaCuspTailSecondDensity (x + a)) := by
        unfold thetaCuspTailSecondDensity
        exact continuous_const.mul (continuous_const.mul
          ((differentiable_thetaCuspTailDerivative 2).continuous.comp
            (continuous_id.add continuous_const)))
      exact ((Complex.continuous_ofReal.comp hrho).mul
        (by unfold spectralTranslationPhase; fun_prop)).aestronglyMeasurable.restrict
  have hbound : ∀ᶠ a : ℝ in atTop,
      ∀ᵐ x : ℝ ∂(volume.restrict (Ioi 0)), ‖F a x‖ ≤ bound x := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have hxa : 0 ≤ x + a := add_nonneg hx0 ha
    have hrho := abs_thetaCuspTailSecondDensity_le_exp_neg_one hxa
    have hea : Real.exp (-a / 2) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    dsimp only [F, bound, C, c]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_of_pos (Real.exp_pos _),
      norm_spectralTranslationPhase_neg_eq_exp_mul_im]
    calc
      Real.exp (a / 2) * |thetaCuspTailSecondDensity (x + a)| *
          Real.exp (x * z.im) ≤
        Real.exp (a / 2) *
            (thetaCuspTailSecondDensityExpOneConstant * Real.exp (-(x + a))) *
          Real.exp (x * z.im) := by gcongr
      _ = Real.exp (-a / 2) *
          (thetaCuspTailSecondDensityExpOneConstant *
            Real.exp (-((1 : ℝ) - z.im) * x)) := by
        rw [show Real.exp (a / 2) *
              (thetaCuspTailSecondDensityExpOneConstant * Real.exp (-(x + a))) *
              Real.exp (x * z.im) =
            thetaCuspTailSecondDensityExpOneConstant *
              (Real.exp (a / 2) * Real.exp (-(x + a)) *
                Real.exp (x * z.im)) by ring,
          ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ thetaCuspTailSecondDensityExpOneConstant *
          Real.exp (-((1 : ℝ) - z.im) * x) := by
        exact mul_le_of_le_one_left
          (mul_nonneg thetaCuspTailSecondDensityExpOneConstant_nonneg
            (Real.exp_pos _).le) hea
  have hlim : ∀ᵐ x : ℝ ∂(volume.restrict (Ioi 0)),
      Tendsto (fun a : ℝ => F a x) atTop (nhds (0 : ℂ)) := by
    filter_upwards with x
    have hreal := exp_half_mul_thetaCuspTailSecondDensity_shift_tendsto_zero x
    have hcplx : Tendsto (fun a : ℝ =>
        ((Real.exp (a / 2) * thetaCuspTailSecondDensity (x + a) : ℝ) : ℂ))
        atTop (nhds 0) := by
      simpa using Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    simpa only [F, zero_mul] using hcplx.mul_const (spectralTranslationPhase (-x) z)
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    bound hFmeas hbound hboundInt hlim
  convert hDCT using 1
  · funext a
    unfold F thetaCuspTailSecondDensityReturnedValue
    rw [MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    push_cast
    ring
  · simp

theorem thetaCuspTailSecondDensityReturnedDerivative_scaled_tendsto_zero
    {z : ℂ} (hz : z.im < 1 / 2) :
    Tendsto (fun a : ℝ =>
      (Real.exp (a / 2) : ℂ) *
        thetaCuspTailSecondDensityReturnedDerivative a z) atTop (nhds 0) := by
  let F : ℝ → ℝ → ℂ := fun a x =>
    ((Real.exp (a / 2) * thetaCuspTailSecondDensity (x + a) : ℝ) : ℂ) *
      ((x : ℂ) * I * spectralTranslationPhase (-x) z)
  let bound : ℝ → ℝ := fun x => thetaCuspTailSecondDensityExpOneConstant *
    (x ^ 1 * Real.exp (-((1 : ℝ) - z.im) * x))
  have hc : 0 < (1 : ℝ) - z.im := by linarith
  have hboundInt : Integrable bound (volume.restrict (Ioi 0)) :=
    (integrableOn_pow_mul_exp_neg_real 1 hc).const_mul _
  have hFmeas : ∀ᶠ a : ℝ in atTop,
      AEStronglyMeasurable (F a) (volume.restrict (Ioi 0)) := by
    exact Eventually.of_forall fun a => by
      have hrho : Continuous (fun x : ℝ =>
          Real.exp (a / 2) * thetaCuspTailSecondDensity (x + a)) := by
        unfold thetaCuspTailSecondDensity
        exact continuous_const.mul (continuous_const.mul
          ((differentiable_thetaCuspTailDerivative 2).continuous.comp
            (continuous_id.add continuous_const)))
      exact ((Complex.continuous_ofReal.comp hrho).mul
        (by unfold spectralTranslationPhase; fun_prop)).aestronglyMeasurable.restrict
  have hbound : ∀ᶠ a : ℝ in atTop,
      ∀ᵐ x : ℝ ∂(volume.restrict (Ioi 0)), ‖F a x‖ ≤ bound x := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 ≤ x := hx.le
    have hxa : 0 ≤ x + a := add_nonneg hx0 ha
    have hrho := abs_thetaCuspTailSecondDensity_le_exp_neg_one hxa
    have hea : Real.exp (-a / 2) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    dsimp only [F, bound]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_I, mul_one, abs_mul, abs_of_pos (Real.exp_pos _),
      norm_spectralTranslationPhase_neg_eq_exp_mul_im]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0, pow_one]
    calc
      Real.exp (a / 2) * |thetaCuspTailSecondDensity (x + a)| *
          (x * Real.exp (x * z.im)) ≤
        Real.exp (a / 2) *
            (thetaCuspTailSecondDensityExpOneConstant * Real.exp (-(x + a))) *
          (x * Real.exp (x * z.im)) := by gcongr
      _ = Real.exp (-a / 2) *
          (thetaCuspTailSecondDensityExpOneConstant *
            (x * Real.exp (-((1 : ℝ) - z.im) * x))) := by
        rw [show Real.exp (a / 2) *
              (thetaCuspTailSecondDensityExpOneConstant * Real.exp (-(x + a))) *
              (x * Real.exp (x * z.im)) =
            thetaCuspTailSecondDensityExpOneConstant * x *
              (Real.exp (a / 2) * Real.exp (-(x + a)) *
                Real.exp (x * z.im)) by ring,
          ← Real.exp_add, ← Real.exp_add]
        ring_nf
        congr 1
        ring
      _ ≤ thetaCuspTailSecondDensityExpOneConstant *
          (x * Real.exp (-((1 : ℝ) - z.im) * x)) := by
        exact mul_le_of_le_one_left
          (mul_nonneg thetaCuspTailSecondDensityExpOneConstant_nonneg
            (mul_nonneg hx0 (Real.exp_pos _).le)) hea
  have hlim : ∀ᵐ x : ℝ ∂(volume.restrict (Ioi 0)),
      Tendsto (fun a : ℝ => F a x) atTop (nhds (0 : ℂ)) := by
    filter_upwards with x
    have hreal := exp_half_mul_thetaCuspTailSecondDensity_shift_tendsto_zero x
    have hcplx : Tendsto (fun a : ℝ =>
        ((Real.exp (a / 2) * thetaCuspTailSecondDensity (x + a) : ℝ) : ℂ))
        atTop (nhds 0) := by
      simpa using Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    simpa only [F, zero_mul] using
      hcplx.mul_const (((x : ℂ) * I) * spectralTranslationPhase (-x) z)
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    bound hFmeas hbound hboundInt hlim
  convert hDCT using 1
  · funext a
    unfold F thetaCuspTailSecondDensityReturnedDerivative
    rw [MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    push_cast
    ring
  · simp

theorem thetaCuspTailSecondEvenRemainderReturnedValue_eq_density_sub_completion
    {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : z.im < 1 / 2) :
    thetaCuspTailSecondEvenRemainderReturnedValue a z =
      thetaCuspTailSecondDensityReturnedValue a z -
        (((1 / 2 : ℝ) * Real.exp (-a / 2) : ℝ) : ℂ) *
          thetaHalfExponentialOppositePhaseValue z := by
  unfold thetaCuspTailSecondEvenRemainderReturnedValue
    thetaCuspTailSecondDensityReturnedValue thetaHalfExponentialOppositePhaseValue
  rw [show (fun x : ℝ =>
      (thetaCuspTailSecondEvenRemainder (x + a) : ℂ) *
        spectralTranslationPhase (-x) z) =
    fun x : ℝ =>
      (thetaCuspTailSecondDensity (x + a) : ℂ) * spectralTranslationPhase (-x) z -
        ((((1 / 2 : ℝ) * Real.exp (-a / 2) : ℝ) : ℂ) *
          ((Real.exp (-x / 2) : ℂ) * spectralTranslationPhase (-x) z)) by
    funext x
    unfold thetaCuspTailSecondEvenRemainder
    rw [← Real.exp_add]
    push_cast
    congr 1
    · ring
    · ring]
  rw [MeasureTheory.integral_sub
      (integrableOn_thetaCuspTailSecondDensity_shift_mul_negPhase ha hz)
      ((integrableOn_thetaHalfExponential_mul_negPhase hz).const_mul
        (((1 / 2 : ℝ) * Real.exp (-a / 2) : ℝ) : ℂ)),
    MeasureTheory.integral_const_mul]

theorem thetaCuspTailSecondEvenRemainderReturnedDerivative_eq_density_sub_completion
    {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : z.im < 1 / 2) :
    thetaCuspTailSecondEvenRemainderReturnedDerivative a z =
      thetaCuspTailSecondDensityReturnedDerivative a z -
        (((1 / 2 : ℝ) * Real.exp (-a / 2) : ℝ) : ℂ) *
          thetaHalfExponentialOppositePhaseDerivative z := by
  unfold thetaCuspTailSecondEvenRemainderReturnedDerivative
    thetaCuspTailSecondDensityReturnedDerivative
    thetaHalfExponentialOppositePhaseDerivative
  rw [show (fun x : ℝ =>
      (thetaCuspTailSecondEvenRemainder (x + a) : ℂ) *
        ((x : ℂ) * I * spectralTranslationPhase (-x) z)) =
    fun x : ℝ =>
      (thetaCuspTailSecondDensity (x + a) : ℂ) *
          ((x : ℂ) * I * spectralTranslationPhase (-x) z) -
        ((((1 / 2 : ℝ) * Real.exp (-a / 2) : ℝ) : ℂ) *
          ((Real.exp (-x / 2) : ℂ) *
            ((x : ℂ) * I * spectralTranslationPhase (-x) z))) by
    funext x
    unfold thetaCuspTailSecondEvenRemainder
    rw [← Real.exp_add]
    push_cast
    congr 1
    · ring
    · ring]
  rw [MeasureTheory.integral_sub
      (integrableOn_thetaCuspTailSecondDensity_shift_mul_negPhaseDerivative ha hz)
      ((integrableOn_thetaHalfExponential_mul_negPhaseDerivative hz).const_mul
        (((1 / 2 : ℝ) * Real.exp (-a / 2) : ℝ) : ℂ)),
    MeasureTheory.integral_const_mul]

theorem thetaCuspTailSecondEvenRemainderReturnedValue_scaled_tendsto_completion
    {z : ℂ} (hz : z.im < 1 / 2) :
    Tendsto (fun a : ℝ =>
      (Real.exp (a / 2) : ℂ) *
        thetaCuspTailSecondEvenRemainderReturnedValue a z)
      atTop (nhds (-(1 / 2 : ℂ) * thetaHalfExponentialOppositePhaseValue z)) := by
  have hsplit : ∀ᶠ a : ℝ in atTop,
      (Real.exp (a / 2) : ℂ) *
          thetaCuspTailSecondEvenRemainderReturnedValue a z =
        (Real.exp (a / 2) : ℂ) *
          thetaCuspTailSecondDensityReturnedValue a z -
            (1 / 2 : ℂ) * thetaHalfExponentialOppositePhaseValue z := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    rw [thetaCuspTailSecondEvenRemainderReturnedValue_eq_density_sub_completion ha hz]
    push_cast
    rw [show Real.exp (a / 2) * ((1 / 2 : ℝ) * Real.exp (-a / 2)) =
      (1 / 2 : ℝ) by
      rw [show Real.exp (a / 2) * ((1 / 2 : ℝ) * Real.exp (-a / 2)) =
        (1 / 2 : ℝ) * (Real.exp (a / 2) * Real.exp (-a / 2)) by ring,
        ← Real.exp_add]
      simp]
    ring
  apply Tendsto.congr' hsplit.symm
  simpa using (thetaCuspTailSecondDensityReturnedValue_scaled_tendsto_zero hz).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℝ =>
      (1 / 2 : ℂ) * thetaHalfExponentialOppositePhaseValue z) atTop _)

theorem thetaCuspTailSecondEvenRemainderReturnedDerivative_scaled_tendsto_completion
    {z : ℂ} (hz : z.im < 1 / 2) :
    Tendsto (fun a : ℝ =>
      (Real.exp (a / 2) : ℂ) *
        thetaCuspTailSecondEvenRemainderReturnedDerivative a z)
      atTop (nhds (-(1 / 2 : ℂ) *
        thetaHalfExponentialOppositePhaseDerivative z)) := by
  have hsplit : ∀ᶠ a : ℝ in atTop,
      (Real.exp (a / 2) : ℂ) *
          thetaCuspTailSecondEvenRemainderReturnedDerivative a z =
        (Real.exp (a / 2) : ℂ) *
          thetaCuspTailSecondDensityReturnedDerivative a z -
            (1 / 2 : ℂ) * thetaHalfExponentialOppositePhaseDerivative z := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    rw [thetaCuspTailSecondEvenRemainderReturnedDerivative_eq_density_sub_completion ha hz]
    push_cast
    rw [show Real.exp (a / 2) * ((1 / 2 : ℝ) * Real.exp (-a / 2)) =
      (1 / 2 : ℝ) by
      rw [show Real.exp (a / 2) * ((1 / 2 : ℝ) * Real.exp (-a / 2)) =
        (1 / 2 : ℝ) * (Real.exp (a / 2) * Real.exp (-a / 2)) by ring,
        ← Real.exp_add]
      simp]
    ring
  apply Tendsto.congr' hsplit.symm
  simpa using (thetaCuspTailSecondDensityReturnedDerivative_scaled_tendsto_zero hz).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℝ =>
      (1 / 2 : ℂ) * thetaHalfExponentialOppositePhaseDerivative z) atTop _)

end

end RHTower
