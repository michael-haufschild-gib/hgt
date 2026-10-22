import GaloisForLFunctions.RHTower.Suzuki.SuzukiNaturalApertureCauchyEnergyEscape
import GaloisForLFunctions.RHTower.CCM.CCMRectangularTransverseGrowth
import GaloisForLFunctions.RHTower.Suzuki.SuzukiRectangularWardDefectBoundedness

/-!
# Scaling no-go for raw natural Suzuki Ward energy

The fixed-width rectangular Xi screw curvature has an unconditional square-root envelope on the
integer logarithmic mesh.  Under RH this follows from its uniform bound; under false RH it follows
from the transverse-divisor power law and the critical-strip ceiling
`xiRightTransverseSup ≤ 1/2`.

The raw natural Suzuki reporter-secant energy, by contrast, grows linearly along apertures `8n`.
Consequently its Ward defect tends to negative infinity on that subsequence.  This rules out the
unrenormalized natural Cauchy energy as the source energy in the rectangular RH connector and
forces any viable wall assembly to remove the anchor-visible linear mass before taking a Gram or
cofinal limit.
-/

open Complex Filter
open scoped Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.RHTower

theorem exists_abs_xiScrewWindowCurvature_logSample_le_sqrt (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → L ≤ Real.log n / 2 →
      |(xiScrewWindowCurvature L (Real.log n)).re| ≤ C * Real.sqrt n := by
  by_cases hRH : RiemannHypothesis
  · let C : ℝ := rectangularTwoEdgeRemainderBound L *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
    have hC : 0 ≤ C := by
      dsimp only [C, rectangularTwoEdgeRemainderBound]
      exact mul_nonneg (by positivity) (tsum_nonneg fun _ => by positivity)
    refine ⟨C, hC, fun n hn hLn => ?_⟩
    have hnorm := norm_xiWeilPolarization_rectangular_le_of_riemannHypothesis
      (L := L) (a := Real.log n / 2) hRH hLn
    rw [xiWeilPolarization_rectangular_logSample_eq_xiScrewWindowCurvature] at hnorm
    have hsqrt : 1 ≤ Real.sqrt (n : ℝ) := by
      calc
        1 = Real.sqrt 1 := by norm_num
        _ ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hn)
    calc
      |(xiScrewWindowCurvature L (Real.log n)).re| ≤
          ‖xiScrewWindowCurvature L (Real.log n)‖ := Complex.abs_re_le_norm _
      _ ≤ C := hnorm
      _ ≤ C * Real.sqrt n := by nlinarith
  · have hne : Nonempty XiRightZeroCopy :=
      nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
    let C : ℝ := 2 * xiRectangularRightCoefficientNormSum L +
      rectangularTwoEdgeRemainderBound L *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
    have hC : 0 ≤ C := by
      dsimp only [C, xiRectangularRightCoefficientNormSum,
        rectangularTwoEdgeRemainderBound]
      exact add_nonneg (mul_nonneg (by norm_num) (tsum_nonneg fun _ => norm_nonneg _))
        (mul_nonneg (by positivity) (tsum_nonneg fun _ => by positivity))
    refine ⟨C, hC, fun n hn hLn => ?_⟩
    have hnorm := norm_xiWeilPolarization_rectangular_logSample_le_transverse_power
      (L := L) hne hn hLn
    rw [xiWeilPolarization_rectangular_logSample_eq_xiScrewWindowCurvature] at hnorm
    have hpow : (n : ℝ) ^ xiRightTransverseSup ≤ (n : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
        (xiRightTransverseSup_le_half hne)
    rw [← Real.sqrt_eq_rpow] at hpow
    calc
      |(xiScrewWindowCurvature L (Real.log n)).re| ≤
          ‖xiScrewWindowCurvature L (Real.log n)‖ := Complex.abs_re_le_norm _
      _ ≤ C * (n : ℝ) ^ xiRightTransverseSup := hnorm
      _ ≤ C * Real.sqrt n := mul_le_mul_of_nonneg_left hpow hC

private theorem tendsto_const_mul_sqrt_eight_mul_sub_linear_atBot
    (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun n : ℕ =>
      C * Real.sqrt (8 * n : ℕ) - (n : ℝ) / 288) atTop atBot := by
  apply Filter.tendsto_atBot.2
  intro B
  have hsqrtTop : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hsqrtTop.eventually_ge_atTop (1728 * C),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (-576 * B)] with n hnroot hnB
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hroot0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hrootSq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0
  have hsqrtEight : Real.sqrt (8 : ℝ) ≤ 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8), Real.sqrt_nonneg (8 : ℝ)]
  have hsqrtMul : Real.sqrt (8 * n : ℕ) ≤ 3 * Real.sqrt (n : ℝ) := by
    rw [show ((8 * n : ℕ) : ℝ) = 8 * (n : ℝ) by norm_num]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
    exact mul_le_mul_of_nonneg_right hsqrtEight hroot0
  have hCle : C ≤ Real.sqrt (n : ℝ) / 1728 := by linarith
  have hCroot : C * Real.sqrt (n : ℝ) ≤ (n : ℝ) / 1728 := by
    have := mul_le_mul_of_nonneg_right hCle hroot0
    nlinarith
  have hsource : C * Real.sqrt (8 * n : ℕ) ≤ (n : ℝ) / 576 := by
    calc
      C * Real.sqrt (8 * n : ℕ) ≤ C * (3 * Real.sqrt (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hsqrtMul hC
      _ ≤ (n : ℝ) / 576 := by nlinarith
  linarith

/-- The unrenormalized natural Suzuki Cauchy energy lies in the wrong scaling class for the
rectangular Xi target: its Ward defect escapes to negative infinity on `8n`, unconditionally. -/
theorem tendsto_suzukiRectangularWardDefect_naturalCauchyEnergy_eight_mul_atBot
    (L : ℝ) :
    Tendsto (fun n : ℕ => suzukiRectangularWardDefect L
      suzukiNaturalApertureCauchyEnergy (8 * n)) atTop atBot := by
  obtain ⟨C, hC, htarget⟩ := exists_abs_xiScrewWindowCurvature_logSample_le_sqrt L
  have henvelope := tendsto_const_mul_sqrt_eight_mul_sub_linear_atBot C hC
  apply Filter.tendsto_atBot.2
  intro B
  have hscale : Tendsto (fun n : ℕ => 8 * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num)
  have hlog : Tendsto (fun n : ℕ => Real.log (8 * n : ℕ)) atTop atTop :=
    by
      have hlog' := Real.tendsto_log_atTop.comp hscale
      exact hlog'.congr' (Filter.Eventually.of_forall fun n => by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hlog.eventually_ge_atTop (2 * L),
    eventually_suzukiNaturalApertureCauchyEnergy_ge_linear,
    (Filter.tendsto_atBot.1 henvelope B)] with n hn hLn henergy henvelopeB
  have hsampleOne : 1 ≤ 8 * n := by omega
  have hsampleL : L ≤ Real.log (8 * n : ℕ) / 2 := by linarith
  have htargetAbs := htarget (8 * n) hsampleOne hsampleL
  have htargetUpper :
      (xiScrewWindowCurvature L (Real.log (8 * n : ℕ))).re ≤
        C * Real.sqrt (8 * n : ℕ) :=
    (le_abs_self _).trans htargetAbs
  rw [suzukiRectangularWardDefect]
  exact le_trans (sub_le_sub htargetUpper henergy) henvelopeB

end

end RHTower
