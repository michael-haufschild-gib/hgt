import GaloisForLFunctions.RHTower.XiGaussianUniformAnnihilatorControl
import GaloisForLFunctions.RHTower.XiGaussianFinitePhaseRemainder

/-!
# Actual phase channel along fixed-time sampled null directions

The imaginary channel is half the actual phase debt. Its perturbation has
the same degree-free energy bound as the full trace. Both its diagonal and
its complete interaction with every energy-unit test vanish uniformly along
the divisor annihilators at a fixed positive heat time.
-/

open Complex Filter Topology
noncomputable section

namespace RHTower

theorem xiGaussianImaginaryChannel_eq_half_nativeEnergy_sub_trace
    (P : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom P t q) =
      (xiGaussianNativeEnergy P t - xiPolynomialGaussianHeatTraceReal P t) / 2 := by
  have hs := summable_xiPolynomialGaussianHeatTerm t.property P
  have hre := (Complex.hasSum_re hs.hasSum).summable
  rw [xiPolynomialGaussianHeatTraceReal, xiPolynomialGaussianHeatTrace, Complex.re_tsum hs]
  simp only [xiGaussianImaginaryChannelAtom, tsum_div_const, hs.norm.tsum_sub hre,
    xiGaussianNativeEnergy]

/-- Actual imaginary-channel perturbation retains the full mixed polynomial
terms and depends on actual sampled energies, not a continuous surrogate. -/
theorem abs_xiGaussianImaginaryChannel_add_sub_le (P Q : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) (η : {η : ℝ // 0 < η}) :
    |(∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom (P + Q) t q) -
      (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom P t q)| ≤
      (η : ℝ) * xiGaussianNativeEnergy P t +
        (1 + 1 / (η : ℝ)) * xiGaussianNativeEnergy Q t := by
  rw [xiGaussianImaginaryChannel_eq_half_nativeEnergy_sub_trace,
    xiGaussianImaginaryChannel_eq_half_nativeEnergy_sub_trace]
  have hid :
      (xiGaussianNativeEnergy (P + Q) t - xiPolynomialGaussianHeatTraceReal (P + Q) t) / 2 -
        (xiGaussianNativeEnergy P t - xiPolynomialGaussianHeatTraceReal P t) / 2 =
      ((xiGaussianNativeEnergy (P + Q) t - xiGaussianNativeEnergy P t) -
        (xiPolynomialGaussianHeatTraceReal (P + Q) t - xiPolynomialGaussianHeatTraceReal P t)) / 2 := by
    ring
  rw [hid, abs_div, abs_of_pos (show (0 : ℝ) < 2 by positivity)]
  have h := abs_sub_le
    (xiGaussianNativeEnergy (P + Q) t - xiGaussianNativeEnergy P t) 0
    (xiPolynomialGaussianHeatTraceReal (P + Q) t - xiPolynomialGaussianHeatTraceReal P t)
  simp only [sub_zero, zero_sub, abs_neg] at h
  have hK := abs_xiGaussianNativeEnergy_add_sub_le P Q t η
  have hH := abs_xiGaussianHeatTraceReal_add_sub_le P Q t η
  linarith only [h, hK, hH]

/-- The actual complete imaginary channel vanishes at fixed heat time. -/
theorem tendsto_xiGaussianImaginaryChannel_annihilator_zero
    (t : {t : ℝ // 0 < t}) :
    Tendsto (fun F : Finset XiZeroCopy =>
      ∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom (xiGaussianAnnihilator F) t q)
      atTop (𝓝 0) := by
  simp only [xiGaussianImaginaryChannel_eq_half_nativeEnergy_sub_trace]
  simpa only [sub_zero, zero_div] using
    ((tendsto_xiGaussianNativeEnergy_annihilator_zero t).sub
      (tendsto_xiGaussianHeatTraceReal_annihilator_zero t)).div_const 2

/-- One cutoff controls every phase-channel perturbation on the complete
sampled unit ball, simultaneously over all polynomial orders. -/
theorem eventually_forall_xiGaussianAnnihilator_phase_perturbation_small
    (t : {t : ℝ // 0 < t}) (ε : {ε : ℝ // 0 < ε}) :
    ∀ᶠ F : Finset XiZeroCopy in atTop,
      ∀ P : {P : Polynomial ℝ // xiGaussianNativeEnergy P t ≤ 1},
        |(∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom
            (P.1 + xiGaussianAnnihilator F) t q) -
          (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom P.1 t q)| < (ε : ℝ) := by
  let η : {η : ℝ // 0 < η} := ⟨(ε : ℝ) / 2, div_pos ε.property (by positivity)⟩
  have hlim : Tendsto (fun F : Finset XiZeroCopy =>
      (η : ℝ) + (1 + 1 / (η : ℝ)) * xiGaussianNativeEnergy (xiGaussianAnnihilator F) t)
      atTop (𝓝 (η : ℝ)) := by
    simpa only [mul_zero, add_zero] using tendsto_const_nhds.add
      ((tendsto_xiGaussianNativeEnergy_annihilator_zero t).const_mul (1 + 1 / (η : ℝ)))
  have hsmall : (η : ℝ) < (ε : ℝ) := by dsimp only [η]; linarith [ε.property]
  filter_upwards [hlim.eventually (Iio_mem_nhds hsmall)] with F hF P
  have hunit : (η : ℝ) * xiGaussianNativeEnergy P.1 t ≤ (η : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left P.property η.property.le
  exact ((abs_xiGaussianImaginaryChannel_add_sub_le P.1 (xiGaussianAnnihilator F) t η).trans
    (add_le_add hunit le_rfl)).trans_lt hF

end RHTower
