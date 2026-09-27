import GaloisForLFunctions.RHTower.XiGaussianPolarAnnihilator

/-!
# A fixed nonzero prime--Gamma gap along native null directions

Polar-normalized annihilators have vanishing native energy but their literal
prime-minus-Gamma source tends to the nonzero polar term. Thus neither polar
evaluation nor the prime-minus-Gamma difference is bounded by native energy.
The completed residual still tends to zero, preserving the required cancellation.
-/

open Complex Polynomial MeasureTheory Filter Topology
open scoped Real
noncomputable section
namespace RHTower

/-- The literal signed prime source minus the full Gamma integral. -/
def xiGaussianPrimeGammaDifference (P : Polynomial ℝ) (t : {t : ℝ // 0 < t}) : ℝ :=
  (routeUPolynomialGaussianPrimeSource P t).re -
    ∫ x : ℝ, ‖routeUPolynomialGaussianDensity P t x‖ * gammaHardyPhaseRate x

theorem xiGaussianPrimeGammaDifference_eq_polar_sub_residual
    (P : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    xiGaussianPrimeGammaDifference P t =
      2 * π * (P.eval (-(1 / 4 : ℝ))) ^ 2 * Real.exp ((t : ℝ) / 4) -
        xiGaussianCompletedSourceResidual P t := by
  unfold xiGaussianPrimeGammaDifference xiGaussianCompletedSourceResidual
  ring

/-- An actual signed arithmetic lower and upper error bound, with every
prime term, Gamma term, and polynomial cross term retained. -/
theorem abs_xiGaussianPolarAnnihilator_primeGamma_sub_polar_le
    (F : Finset XiZeroCopy) (t : {t : ℝ // 0 < t}) :
    |xiGaussianPrimeGammaDifference (xiGaussianPolarAnnihilator F) t -
      2 * π * Real.exp ((t : ℝ) / 4)| ≤
        π * xiGaussianNativeEnergy (xiGaussianPolarAnnihilator F) t := by
  rw [xiGaussianPrimeGammaDifference_eq_polar_sub_residual,
    xiGaussianPolarAnnihilator_eval_pole, one_pow, mul_one,
    sub_sub_cancel_left, abs_neg]
  exact abs_xiGaussianCompletedSourceResidual_le_energy _ t

theorem tendsto_xiGaussianPolarAnnihilator_completedSource_zero (t : {t : ℝ // 0 < t}) :
    Tendsto (fun F : Finset XiZeroCopy =>
      xiGaussianCompletedSourceResidual (xiGaussianPolarAnnihilator F) t) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun F => by
    simpa only [Real.norm_eq_abs] using
      abs_xiGaussianCompletedSourceResidual_le_energy (xiGaussianPolarAnnihilator F) t)
  simpa only [mul_zero] using
    (tendsto_xiGaussianPolarAnnihilator_energy_zero t).const_mul π

/-- The full prime-minus-Gamma source has a nonzero, exactly known limit
although the native energy of these polynomials tends to zero. -/
theorem tendsto_xiGaussianPolarAnnihilator_primeGamma_polar (t : {t : ℝ // 0 < t}) :
    Tendsto (fun F : Finset XiZeroCopy =>
      xiGaussianPrimeGammaDifference (xiGaussianPolarAnnihilator F) t) atTop
        (𝓝 (2 * π * Real.exp ((t : ℝ) / 4))) := by
  simp only [xiGaussianPrimeGammaDifference_eq_polar_sub_residual,
    xiGaussianPolarAnnihilator_eval_pole, one_pow, mul_one]
  simpa only [sub_zero] using
    (tendsto_xiGaussianPolarAnnihilator_completedSource_zero t).const_sub
      (2 * π * Real.exp ((t : ℝ) / 4))

/-- No finite native-energy bound can control the polar evaluation across all orders. -/
theorem not_xiGaussian_polar_eval_bounded_by_nativeEnergy (t : {t : ℝ // 0 < t}) :
    ¬ ∃ C : ℝ, ∀ P : Polynomial ℝ,
      (P.eval (-(1 / 4 : ℝ))) ^ 2 ≤ C * xiGaussianNativeEnergy P t := by
  rintro ⟨C, hC⟩
  have hlim : Tendsto (fun F : Finset XiZeroCopy =>
      C * xiGaussianNativeEnergy (xiGaussianPolarAnnihilator F) t) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_xiGaussianPolarAnnihilator_energy_zero t).const_mul C
  have hbad : (1 : ℝ) ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    (Eventually.of_forall fun F => by
      simpa only [xiGaussianPolarAnnihilator_eval_pole, one_pow] using
        hC (xiGaussianPolarAnnihilator F))
  exact (not_le_of_gt zero_lt_one) hbad

/-- Even the signed prime-minus-Gamma expression has no finite upper
bound relative to native energy. The polar cancellation is indispensable. -/
theorem not_xiGaussian_primeGamma_bounded_by_nativeEnergy (t : {t : ℝ // 0 < t}) :
    ¬ ∃ C : ℝ, ∀ P : Polynomial ℝ,
      xiGaussianPrimeGammaDifference P t ≤ C * xiGaussianNativeEnergy P t := by
  rintro ⟨C, hC⟩
  have hlim : Tendsto (fun F : Finset XiZeroCopy =>
      C * xiGaussianNativeEnergy (xiGaussianPolarAnnihilator F) t) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_xiGaussianPolarAnnihilator_energy_zero t).const_mul C
  have hbad : 2 * π * Real.exp ((t : ℝ) / 4) ≤ 0 :=
    le_of_tendsto_of_tendsto (tendsto_xiGaussianPolarAnnihilator_primeGamma_polar t) hlim
      (Eventually.of_forall fun F => hC (xiGaussianPolarAnnihilator F))
  exact (not_le_of_gt (mul_pos (mul_pos (by positivity) Real.pi_pos) (Real.exp_pos _))) hbad

end RHTower
