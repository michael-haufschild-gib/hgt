import GaloisForLFunctions.RHTower.CCM.CCMFirstClockVolterra
import GaloisForLFunctions.RHTower.XiEndpointCentralMomentDyadicBridge
import GaloisForLFunctions.RHTower.CompletedPrimeGammaSecondMomentCenterPositive

/-!
# Xi centered reciprocal-Laurent parity and source universality

Functional-equation square folding removes the sign of the centered reciprocal Xi coordinate.
This file restores the complete signed reciprocal-power tower.  Inverse-square summability and
the verified central zero-free interval make every order at least two absolutely summable.
Reflection then annihilates every odd trace, while every even trace is exactly the existing
central moment, fixed prime--Gamma source moment, and raw-endpoint dyadic transform.
-/

open Complex

namespace RHTower

noncomputable section

/-- The signed reciprocal coordinate before functional-equation square folding. -/
def xiCenteredReciprocalLaurentCoordinate (q : XiZeroCopy) : ℂ :=
  (xiSpectralPoint q)⁻¹

/-- Functional-equation reflection negates the signed centered reciprocal coordinate. -/
@[simp] theorem xiCenteredReciprocalLaurentCoordinate_reflect (q : XiZeroCopy) :
    xiCenteredReciprocalLaurentCoordinate (xiZeroCopyReflectEquiv q) =
      -xiCenteredReciprocalLaurentCoordinate q := by
  rw [xiCenteredReciprocalLaurentCoordinate, xiSpectralPoint_reflect,
    inv_neg, xiCenteredReciprocalLaurentCoordinate]

/-- Every centered reciprocal Laurent power of order at least two is absolutely summable over
the exact Xi multiplicity copies. -/
theorem summable_xiCenteredReciprocalLaurentCoordinate_pow
    (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun q : XiZeroCopy =>
      xiCenteredReciprocalLaurentCoordinate q ^ k) := by
  apply Summable.of_norm_bounded summable_norm_xiSpectralPoint_inv_sq
  intro q
  rw [norm_pow]
  change ‖(xiSpectralPoint q)⁻¹‖ ^ k ≤ ‖(xiSpectralPoint q)⁻¹‖ ^ (2 : ℕ)
  have hnonneg : 0 ≤ ‖(xiSpectralPoint q)⁻¹‖ := norm_nonneg _
  have hle : ‖(xiSpectralPoint q)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q))).2
      (le_trans (by norm_num) (four_lt_norm_xiSpectralPoint q).le)
  have hsplit : k = (k - 2) + 2 := by omega
  rw [hsplit, pow_add]
  calc
    ‖(xiSpectralPoint q)⁻¹‖ ^ (k - 2) *
          ‖(xiSpectralPoint q)⁻¹‖ ^ (2 : ℕ) ≤
        1 * ‖(xiSpectralPoint q)⁻¹‖ ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_one₀ hnonneg hle) (pow_nonneg hnonneg 2)
    _ = ‖(xiSpectralPoint q)⁻¹‖ ^ (2 : ℕ) := one_mul _

/-- Multiplicity-exact signed centered reciprocal Laurent trace. -/
def xiCenteredReciprocalLaurentTrace (k : ℕ) : ℂ :=
  ∑' q : XiZeroCopy, xiCenteredReciprocalLaurentCoordinate q ^ k

/-- Functional-equation reflection imposes parity on the complete reciprocal Laurent trace. -/
theorem xiCenteredReciprocalLaurentTrace_reflection (k : ℕ) :
    xiCenteredReciprocalLaurentTrace k =
      (-1 : ℂ) ^ k * xiCenteredReciprocalLaurentTrace k := by
  rw [xiCenteredReciprocalLaurentTrace]
  calc
    (∑' q : XiZeroCopy, xiCenteredReciprocalLaurentCoordinate q ^ k) =
        ∑' q : XiZeroCopy,
          xiCenteredReciprocalLaurentCoordinate (xiZeroCopyReflectEquiv q) ^ k :=
      (xiZeroCopyReflectEquiv.tsum_eq
        (fun q : XiZeroCopy => xiCenteredReciprocalLaurentCoordinate q ^ k)).symm
    _ = ∑' q : XiZeroCopy,
        (-xiCenteredReciprocalLaurentCoordinate q) ^ k := by
      apply tsum_congr
      intro q
      rw [xiCenteredReciprocalLaurentCoordinate_reflect]
    _ = (-1 : ℂ) ^ k * ∑' q : XiZeroCopy,
        xiCenteredReciprocalLaurentCoordinate q ^ k := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro q
      rw [neg_pow]

/-- Every absolutely summable odd centered reciprocal Laurent trace vanishes. -/
theorem xiCenteredReciprocalLaurentTrace_odd_eq_zero (m : ℕ) :
    xiCenteredReciprocalLaurentTrace (2 * m + 3) = 0 := by
  have hodd : Odd (2 * m + 3) := ⟨m + 1, by omega⟩
  have hreflection :=
    xiCenteredReciprocalLaurentTrace_reflection (2 * m + 3)
  rw [hodd.neg_one_pow, neg_one_mul] at hreflection
  have htwo :
      (2 : ℂ) * xiCenteredReciprocalLaurentTrace (2 * m + 3) = 0 := by
    linear_combination hreflection
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The even signed Laurent tower is exactly the folded central reciprocal-square tower. -/
theorem xiCenteredReciprocalLaurentTrace_even_eq_centralMoment (m : ℕ) :
    xiCenteredReciprocalLaurentTrace (2 * m + 2) =
      xiCentralReciprocalMoment m := by
  rw [xiCenteredReciprocalLaurentTrace,
    ← tsum_xiZeroCopyReciprocalSquare_pow m]
  apply tsum_congr
  intro q
  rw [xiCenteredReciprocalLaurentCoordinate,
    xiZeroCopyReciprocalSquare]
  rw [show 2 * m + 2 = 2 * (m + 1) by omega, pow_mul]

/-- **Xi centered reciprocal-Laurent parity/source universality.**  At every depth, the odd
signed Laurent trace is an absolutely convergent vacuum.  The adjacent even trace is simultaneously
the folded central Xi moment, the fixed prime--Gamma source moment, and the explicit dyadic
negative-binomial transform of the raw endpoint trace tower. -/
theorem xi_completeCenteredReciprocalLaurentParitySourceUniversality
    (m : ℕ) :
    Summable (fun q : XiZeroCopy =>
        xiCenteredReciprocalLaurentCoordinate q ^ (2 * m + 3)) ∧
      xiCenteredReciprocalLaurentTrace (2 * m + 3) = 0 ∧
      xiCenteredReciprocalLaurentTrace (2 * m + 2) =
        xiCentralReciprocalMoment m ∧
      xiCenteredReciprocalLaurentTrace (2 * m + 2) =
        ((analyticTraceMoments
          (normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace) m : ℝ) : ℂ) ∧
      xiCenteredReciprocalLaurentTrace (2 * m + 2) =
        (-1 : ℂ) ^ (m + 1) *
          ∑' n : ℕ, ((n + (2 * m + 1)).choose (2 * m + 1) : ℂ) *
            (2 : ℂ)⁻¹ ^ n *
              xiRawReciprocalPowerTrace (n + (2 * m + 2)) := by
  have heven :=
    xiCenteredReciprocalLaurentTrace_even_eq_centralMoment m
  refine ⟨summable_xiCenteredReciprocalLaurentCoordinate_pow
      (2 * m + 3) (by omega),
    xiCenteredReciprocalLaurentTrace_odd_eq_zero m,
    heven, ?_, ?_⟩
  · exact heven.trans (primeArchSourceMoment_eq_xiCentralReciprocalMoment m).symm
  · exact heven.trans (xiCentralReciprocalMoment_eq_rawDyadicTraces m)

/-- **Low Laurent positive-even/vacuum-odd phase.**  At each of the first three folded depths,
the signed centered reciprocal trace has a strictly positive even channel and an exactly vanishing
adjacent odd channel. -/
theorem xiCenteredReciprocalLaurentTrace_lowEvenPos_oddZero
    (m : ℕ) (hm : m ≤ 2) :
    0 < (xiCenteredReciprocalLaurentTrace (2 * m + 2)).re ∧
      xiCenteredReciprocalLaurentTrace (2 * m + 3) = 0 := by
  refine ⟨?_, xiCenteredReciprocalLaurentTrace_odd_eq_zero m⟩
  rw [xiCenteredReciprocalLaurentTrace_even_eq_centralMoment,
    ← normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment]
  interval_cases m
  · exact normalizedPrimeArchMoment_zero_pos
  · exact normalizedPrimeArchMoment_one_pos
  · exact normalizedPrimeArchMoment_two_pos

end

end RHTower
