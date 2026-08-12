import GaloisForLFunctions.RHTower.Sieve.MontgomeryVaughanConvolutionReceiver

/-!
# Route T logarithmic phase receiver

Specializes the finite Montgomery--Vaughan convolution receiver to the product multiplicities and
height-uniform twisted logarithmic estimate produced by Route T.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

def routeTLogReceiverLength (C : ℕ) : ℕ :=
  (2 * C) ^ routeTLogCentreExponent

def routeTLogReceiverCutoff (C : ℕ) : ℕ :=
  4 * routeTLogReceiverLength C + 1

def routeTLogPhase (t : ℝ) (n : ℕ) : ℂ :=
  finitePhaseChar (t / (2 * Real.pi) * Real.log n)

theorem routeTLog_receiver_scales
    {u C : ℕ} (hC : routeTLogBaseThreshold u ≤ 2 * C) :
    8 ≤ routeTLogHalfBlock C ∧
      16 * (routeTLogHalfBlock C) ^ 2 ≤ routeTLogReceiverLength C := by
  let B := 2 * C
  let Q := routeTLogHalfBlock C
  have hB2 : 2 ≤ B := routeTLogBaseThreshold_ge_two (by simpa only [B] using hC)
  have hC1 : 1 ≤ C := by omega
  have hP : 2 * Q = B ^ routeTLogHalfLengthExponent := by
    simpa only [B, Q] using two_mul_routeTLogHalfBlock C
  constructor
  · change 8 ≤ Q
    have hpow : 8 ≤ B ^ 98 := by
      exact (by norm_num : 8 ≤ 2 ^ 98).trans (Nat.pow_le_pow_left hB2 98)
    change 8 ≤ C * B ^ 98
    nlinarith [Nat.mul_le_mul_right (B ^ 98) hC1]
  · change 16 * Q ^ 2 ≤ B ^ routeTLogCentreExponent
    have hBsq : 4 ≤ B ^ 2 := by nlinarith
    calc
      16 * Q ^ 2 = 4 * (2 * Q) ^ 2 := by ring
      _ = 4 * B ^ 198 := by
        rw [hP]
        simp only [routeTLogHalfLengthExponent]
        rw [← pow_mul]
      _ ≤ B ^ 2 * B ^ 198 := by
        exact Nat.mul_le_mul_right (B ^ 198) hBsq
      _ = B ^ routeTLogCentreExponent := by
        rw [← pow_add]
        norm_num [routeTLogCentreExponent]

/-- Exact MV24.10 specialization.  Only `hsmall` remains as a transparent elementary scale
condition: the Route-T twisted saving must be no larger than the coefficient block length. -/
theorem routeTLogPhase_receiver_inequality
    {u C : ℕ} {t : ℝ} (hu : 141 ≤ u)
    (hC : routeTLogBaseThreshold u ≤ 2 * C)
    (ht : 0 < t)
    (hbottom : (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u - 1) : ℕ) : ℝ)) ≤ t)
    (htop : t ≤ (((((2 * C) ^ routeTLogCentreExponent) ^
      (4 * u) : ℕ) : ℝ)))
    (hsmall :
      2 * (((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
        (2 - vinogradovRouteTPowerSavingExponent u)) ≤
        ((routeTLogHalfBlock C : ℕ) : ℝ) ^ 2) :
    (((routeTLogHalfBlock C : ℕ) : ℝ) ^ 2 / 64) *
        ‖mvPhaseBlockSum (routeTLogReceiverCutoff C)
          (routeTLogReceiverLength C) (2 * routeTLogReceiverLength C)
          (routeTLogPhase t)‖ ≤
      ((routeTLogHalfBlock C) ^ 2 + 2 * routeTLogReceiverLength C : ℕ) *
        (7 * Real.sqrt
            (((routeTLogHalfBlock C : ℕ) : ℝ) ^ 2 *
              (2 * (((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
                (2 - vinogradovRouteTPowerSavingExponent u)))) +
          3 * routeTLogHalfBlock C + 7) := by
  let Q := routeTLogHalfBlock C
  let N := routeTLogReceiverLength C
  let K := routeTLogReceiverCutoff C
  let S : ℝ := 2 * (((((2 * C) ^ routeTLogHalfLengthExponent : ℕ) : ℝ)) ^
    (2 - vinogradovRouteTPowerSavingExponent u))
  obtain ⟨hQ8, hscale⟩ := routeTLog_receiver_scales hC
  have hscale' : 16 * Q ^ 2 ≤ N := by simpa only [Q, N] using hscale
  have hQN : Q ^ 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by
    have hB2 : 2 ≤ 2 * C := routeTLogBaseThreshold_ge_two hC
    change 1 ≤ (2 * C) ^ routeTLogCentreExponent
    exact one_le_pow₀ (by omega)
  have hKprod : 4 * Q ^ 2 < K := by
    unfold K routeTLogReceiverCutoff
    omega
  have hmax : 2 * Q ^ 2 + 2 * N < K := by
    unfold K routeTLogReceiverCutoff
    omega
  have hreceiver := norm_mvCoefficientBlockSum_mul_mvPhaseBlockSum_le
    (K := K) (Q := Q) (M := Q ^ 2) (N := N) (N' := 2 * N)
    (hQ := by omega) (hM := by nlinarith) hQN (by omega) (by omega) hmax
    (routeTProductMultiplicity hKprod) (routeTLogPhase t)
    (norm_routeTProductMultiplicity_le (by omega) hKprod)
    (by
      intro n
      unfold routeTLogPhase
      rw [norm_finitePhaseChar])
    (S := S) (by positivity)
    (by simpa only [S, Q, Nat.cast_pow] using hsmall) (by
      intro r hr β
      have hrange := Finset.mem_Ioc.mp hr
      have hrprod : 4 * Q ^ 2 < r := by omega
      rw [← mvTrigSum_convolutionCoefficient]
      unfold routeTLogPhase
      rw [mvTrigSum_routeTLogConvolution_eq hKprod hrprod]
      apply norm_routeTLogTwistedShiftBilinearSum_le_two_rpow_of_shell
        hu hC ht hbottom htop
      · exact_mod_cast (show N ≤ r by omega)
      · exact_mod_cast (show r ≤ 4 * N by omega))
  have hcoeff := routeTProductMultiplicity_block_lower hQ8 hKprod
  have hfactor : 0 ≤
      ‖mvPhaseBlockSum K N (2 * N) (routeTLogPhase t)‖ := norm_nonneg _
  calc
    ((Q : ℝ) ^ 2 / 64) *
        ‖mvPhaseBlockSum K N (2 * N) (routeTLogPhase t)‖ ≤
      ‖mvCoefficientBlockSum K (Q ^ 2) (routeTProductMultiplicity hKprod)‖ *
        ‖mvPhaseBlockSum K N (2 * N) (routeTLogPhase t)‖ :=
      mul_le_mul_of_nonneg_right hcoeff hfactor
    _ = ‖mvCoefficientBlockSum K (Q ^ 2) (routeTProductMultiplicity hKprod) *
        mvPhaseBlockSum K N (2 * N) (routeTLogPhase t)‖ := by rw [norm_mul]
    _ ≤ (Q ^ 2 + 2 * N : ℕ) *
        (7 * Real.sqrt ((Q : ℝ) ^ 2 * S) + 3 * Q + 7) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, S]
        using hreceiver

end

end RHTower.Sieve
