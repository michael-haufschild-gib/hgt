import GaloisForLFunctions.RHTower.XiWardCubicBoundaryResolventKreinDilation

/-!
# Cubic Ward boundary-resolvent companion trace no-go (W-H205)

W-H198 supplies the canonical rank-one `SU(1,1)` dilation of every active boundary-resolvent
transfer.  This module audits whether those minimal dilations can be assembled cell by cell under
the literal cubic primitive Euler weight.

They cannot.  Match each primitive ordinate clock to one strict-right zero.  The exact transfer
power is then `(lambda^(2 : ℕ) / a^(2 : ℕ))^(2 : ℕ)`, where `lambda` is the primitive log frequency and `a` is the
centered horizontal zero depth.  Since `a < 1/2` and `lambda >= log 2 > 2/3`, the forced negative
companion charge is at least `lambda^(4 : ℕ)`.  On the depth-zero prime slice, multiplication by the
cubic source weight leaves at least `115 / (1944 p)`.  Euler's prime harmonic divergence therefore
proves that the full direct-sum companion trace is not summable.

This is a global trace obstruction, not a failure of the local Krein lift.  Any viable completed
coefficient-faithful incidence must mix, cancel, or short primitive cells before applying the
boundary-resolvent rate transmuter.  Independent cellwise dilation followed by a global trace can
never fit inside the finite W-H184 source budget.
-/

open Complex

namespace RHTower

noncomputable section

/-- Primitive ordinate clock phase-matched to a fixed strict-right Xi zero. -/
def xiWardCubicPhaseMatchedPrimitiveClock (q : XiRightZeroCopy) : ℝ :=
  (xiRightCenteredZero q).im

/-- At the phase-matched clock, the exact resonant transfer power is the fourth power of the
horizontal rate quotient. -/
theorem normSq_phaseMatched_primitiveStrictRight_resonantTransfer
    (pe : Nat.Primes × ℕ) (q : XiRightZeroCopy) :
    Complex.normSq
      (xiWardCubicPrimitiveStrictRightResonantTransfer pe
        (xiWardCubicPhaseMatchedPrimitiveClock q) q) =
      ((xiGammaEulerPrimitiveLogFrequency pe ^ (2 : ℕ) /
        (xiRightCenteredZero q).re ^ (2 : ℕ)) : ℝ) ^ (2 : ℕ) := by
  rw [xiWardCubicPrimitiveStrictRightResonantTransfer,
    normSq_xiWardCubicBoundaryResolventTransfer_targetResonance]
  simp only [xiWardCubicPhaseMatchedPrimitiveClock,
    routePPrimitiveBurnolSpectralPoint, xiRightCenteredZero_eq_support_sub_half,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    I_re, I_im, zero_mul, one_mul, add_zero, sub_self]
  norm_num

/-- Literal cubic primitive weight on the depth-zero prime slice. -/
theorem xiGammaEulerPrimitiveCubicLogMomentWeight_prime_zero
    (p : Nat.Primes) :
    xiGammaEulerPrimitiveCubicLogMomentWeight (p, 0) =
      (115 / 864 : ℝ) / ((p : ℝ) * Real.log (p : ℝ) ^ (2 : ℕ)) := by
  rw [xiGammaEulerPrimitiveCubicLogMomentWeight, invNatLogSq]
  norm_num
  ring

/-- Every primitive log frequency is uniformly larger than `2/3`. -/
theorem two_thirds_lt_xiGammaEulerPrimitiveLogFrequency
    (pe : Nat.Primes × ℕ) :
    (2 / 3 : ℝ) < xiGammaEulerPrimitiveLogFrequency pe := by
  have hval : 2 ≤ xiGammaEulerValuationNat pe := by
    rw [xiGammaEulerValuationNat]
    exact pe.1.property.two_le.trans (Nat.le_pow (by omega))
  have hlog : Real.log 2 ≤
      Real.log (xiGammaEulerValuationNat pe : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hval)
  rw [xiGammaEulerPrimitiveLogFrequency]
  exact (lt_trans (by norm_num) Real.log_two_gt_d9).trans_le hlog

/-- **W-H205 local lower law.** At phase match, the mandatory negative companion charge dominates
the fourth power of the primitive log frequency. -/
theorem fourth_frequency_le_phaseMatched_kreinCompanion_sq
    (pe : Nat.Primes × ℕ) (q : XiRightZeroCopy) :
    xiGammaEulerPrimitiveLogFrequency pe ^ (4 : ℕ) ≤
      xiWardCubicKreinCompanion
        (xiWardCubicPrimitiveStrictRightResonantTransfer pe
          (xiWardCubicPhaseMatchedPrimitiveClock q) q) ^ (2 : ℕ) := by
  let lambda := xiGammaEulerPrimitiveLogFrequency pe
  let a := (xiRightCenteredZero q).re
  have ha : 0 < a := by
    dsimp [a]
    exact xiRightCenteredZero_re_pos q
  have haHalf : a < 1 / 2 := by
    dsimp [a]
    exact (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2
  have ha2 : a ^ (2 : ℕ) ≤ 1 / 4 := by nlinarith [sq_nonneg (a - 1 / 2)]
  have hlambda : 2 / 3 < lambda := by
    exact two_thirds_lt_xiGammaEulerPrimitiveLogFrequency pe
  have hlambda0 : 0 ≤ lambda ^ (2 : ℕ) := sq_nonneg _
  have hratio : 4 * lambda ^ (2 : ℕ) ≤ lambda ^ (2 : ℕ) / a ^ (2 : ℕ) := by
    rw [le_div_iff₀ (sq_pos_of_pos ha)]
    nlinarith
  have hgain : 16 * lambda ^ (4 : ℕ) ≤ (lambda ^ (2 : ℕ) / a ^ (2 : ℕ)) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (lambda ^ (2 : ℕ) / a ^ (2 : ℕ) - 4 * lambda ^ (2 : ℕ))]
  have hlarge : 1 < 15 * lambda ^ (4 : ℕ) := by
    have hlambda2 : (2 / 3 : ℝ) ^ (2 : ℕ) < lambda ^ (2 : ℕ) := by nlinarith
    have hlambda4 : ((2 / 3 : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) < (lambda ^ (2 : ℕ)) ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (lambda ^ (2 : ℕ) - (2 / 3 : ℝ) ^ (2 : ℕ))]
    nlinarith
  rw [primitive_to_strictRight_kreinCompanion_sq_eq_excess_gain,
    normSq_phaseMatched_primitiveStrictRight_resonantTransfer]
  dsimp [lambda, a] at hgain ⊢
  nlinarith

/-- Cubic source weight charged by the mandatory negative companion of the phase-matched local
Krein dilation. -/
def xiWardCubicPhaseMatchedKreinCompanionTraceWeight
    (q : XiRightZeroCopy) (pe : Nat.Primes × ℕ) : ℝ :=
  xiGammaEulerPrimitiveCubicLogMomentWeight pe *
    xiWardCubicKreinCompanion
      (xiWardCubicPrimitiveStrictRightResonantTransfer pe
        (xiWardCubicPhaseMatchedPrimitiveClock q) q) ^ (2 : ℕ)

/-- **W-H205 harmonic minorant.** Each depth-zero prime pays at least a fixed positive multiple of
`1/p` in mandatory negative companion trace. -/
theorem harmonic_minorant_phaseMatchedKreinCompanionTraceWeight
    (p : Nat.Primes) (q : XiRightZeroCopy) :
    (115 / 1944 : ℝ) * (1 / (p : ℝ)) ≤
      xiWardCubicPhaseMatchedKreinCompanionTraceWeight q (p, 0) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.property.pos
  have hlog : 2 / 3 < Real.log (p : ℝ) := by
    simpa [xiGammaEulerPrimitiveLogFrequency,
      xiGammaEulerValuationNat] using
        (two_thirds_lt_xiGammaEulerPrimitiveLogFrequency (p, 0))
  have hlog0 : 0 < Real.log (p : ℝ) := by linarith
  have hcomp := fourth_frequency_le_phaseMatched_kreinCompanion_sq (p, 0) q
  norm_num [xiGammaEulerPrimitiveLogFrequency,
    xiGammaEulerValuationNat] at hcomp
  rw [xiWardCubicPhaseMatchedKreinCompanionTraceWeight,
    xiGammaEulerPrimitiveCubicLogMomentWeight_prime_zero]
  have hweight : 0 ≤
      (115 / 864 : ℝ) / ((p : ℝ) * Real.log (p : ℝ) ^ (2 : ℕ)) := by positivity
  calc
    (115 / 1944 : ℝ) * (1 / (p : ℝ)) =
        (115 / 864 : ℝ) * (4 / 9) / (p : ℝ) := by ring
    _ ≤ (115 / 864 : ℝ) * Real.log (p : ℝ) ^ (2 : ℕ) / (p : ℝ) := by
      apply (div_le_div_iff_of_pos_right hp0).2
      nlinarith
    _ = (115 / 864 : ℝ) /
          ((p : ℝ) * Real.log (p : ℝ) ^ (2 : ℕ)) *
            Real.log (p : ℝ) ^ (4 : ℕ) := by
      field_simp
    _ ≤ (115 / 864 : ℝ) /
          ((p : ℝ) * Real.log (p : ℝ) ^ (2 : ℕ)) *
            xiWardCubicKreinCompanion
              (xiWardCubicPrimitiveStrictRightResonantTransfer (p, 0)
                (xiWardCubicPhaseMatchedPrimitiveClock q) q) ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hcomp hweight

/-- **W-H205 global trace no-go.** The direct sum of minimal phase-matched cellwise Krein
companions is not trace-class under the literal cubic primitive source weight. -/
theorem not_summable_xiWardCubicPhaseMatchedKreinCompanionTraceWeight
    (q : XiRightZeroCopy) :
    ¬ Summable (xiWardCubicPhaseMatchedKreinCompanionTraceWeight q) := by
  intro hsum
  have hslice : Summable (fun p : Nat.Primes =>
      xiWardCubicPhaseMatchedKreinCompanionTraceWeight q (p, 0)) :=
    hsum.comp_injective (fun p r h => congrArg Prod.fst h)
  have hscaled : Summable (fun p : Nat.Primes =>
      (115 / 1944 : ℝ) * (1 / (p : ℝ))) :=
    Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun p => harmonic_minorant_phaseMatchedKreinCompanionTraceWeight p q) hslice
  have hharmonic : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) :=
    (summable_mul_left_iff (by norm_num : (115 / 1944 : ℝ) ≠ 0)).mp hscaled
  exact Nat.Primes.not_summable_one_div hharmonic

end

end RHTower
