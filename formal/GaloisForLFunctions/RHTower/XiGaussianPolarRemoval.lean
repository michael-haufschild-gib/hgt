import GaloisForLFunctions.RHTower.XiGaussianPolarSourceCancellation

/-!
# Removing the polar evaluation without changing the native completed form

A real polynomial can be corrected to vanish exactly at minus one quarter.
The correction and every complete mixed contribution become arbitrarily
small in native Xi energy, uniformly on a prescribed positive heat half-line.
The divisor cutoff may depend on the polynomial's polar value.
-/

open Complex Polynomial Filter Topology
open scoped Real
noncomputable section
namespace RHTower

def xiGaussianRemovePolar (P : Polynomial ℝ) (F : Finset XiZeroCopy) : Polynomial ℝ :=
  P + Polynomial.C (-(P.eval (-(1 / 4 : ℝ)))) * xiGaussianPolarAnnihilator F

theorem xiGaussianRemovePolar_eval_pole (P : Polynomial ℝ) (F : Finset XiZeroCopy) :
    (xiGaussianRemovePolar P F).eval (-(1 / 4 : ℝ)) = 0 := by
  simp only [xiGaussianRemovePolar, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, xiGaussianPolarAnnihilator_eval_pole, mul_one, add_neg_cancel]

theorem xiGaussianRemovePolar_correction_energy (P : Polynomial ℝ) (F : Finset XiZeroCopy)
    (t : {t : ℝ // 0 < t}) :
    xiGaussianNativeEnergy (xiGaussianRemovePolar P F - P) t =
      (P.eval (-(1 / 4 : ℝ))) ^ 2 * xiGaussianNativeEnergy (xiGaussianPolarAnnihilator F) t := by
  rw [xiGaussianRemovePolar, add_sub_cancel_left, xiGaussianNativeEnergy_C_mul, neg_sq]

theorem tendsto_xiGaussianRemovePolar_correction_energy_zero (P : Polynomial ℝ)
    (t : {t : ℝ // 0 < t}) :
    Tendsto (fun F : Finset XiZeroCopy => xiGaussianNativeEnergy (xiGaussianRemovePolar P F - P) t)
      atTop (𝓝 0) := by
  simp only [xiGaussianRemovePolar_correction_energy]
  simpa only [mul_zero] using (tendsto_xiGaussianPolarAnnihilator_energy_zero t).const_mul
    ((P.eval (-(1 / 4 : ℝ))) ^ 2)

/-- Exact polar removal with full cross-term control. The same corrected
polynomial works at every later heat time; polynomial degree is unrestricted. -/
theorem eventually_xiGaussianRemovePolar_heatHalfLine_control
    (P : Polynomial ℝ) (t₀ : {t : ℝ // 0 < t}) (ε : {ε : ℝ // 0 < ε}) :
    ∀ᶠ F : Finset XiZeroCopy in atTop, ∀ s : Set.Ici (t₀ : ℝ),
      let t := xiGaussianHeatAfter t₀ s
      xiGaussianNativeEnergy (xiGaussianRemovePolar P F - P) t < (ε : ℝ) ∧
      ‖xiPolynomialGaussianHeatTrace (xiGaussianRemovePolar P F) t -
        xiPolynomialGaussianHeatTrace P t‖ < (ε : ℝ) ∧
      |xiGaussianNativeEnergy (xiGaussianRemovePolar P F) t - xiGaussianNativeEnergy P t| < (ε : ℝ) ∧
      |(∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom (xiGaussianRemovePolar P F) t q) -
        (∑' q : XiZeroCopy, xiGaussianImaginaryChannelAtom P t q)| < (ε : ℝ) ∧
      |xiGaussianCompletedSourceResidual (xiGaussianRemovePolar P F) t -
        xiGaussianCompletedSourceResidual P t| < π * (ε : ℝ) := by
  let A := xiGaussianNativeEnergy P t₀
  have hA : 0 ≤ A := xiGaussianNativeEnergy_nonneg P t₀
  let η : {η : ℝ // 0 < η} := ⟨(ε : ℝ) / (4 * (A + 1)), div_pos ε.property (by positivity)⟩
  have hηA : (η : ℝ) * A < (ε : ℝ) / 2 := by
    have he : (η : ℝ) * (4 * (A + 1)) = (ε : ℝ) :=
      div_mul_cancel₀ _ (ne_of_gt (by positivity : 0 < 4 * (A + 1)))
    have hη := η.property
    nlinarith only [he, hη, ε.property]
  let C := 1 + 1 / (η : ℝ)
  have hC : 1 ≤ C := le_add_of_nonneg_right (one_div_nonneg.mpr η.property.le)
  have hlim : Tendsto (fun F : Finset XiZeroCopy =>
      C * xiGaussianNativeEnergy (xiGaussianRemovePolar P F - P) t₀) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_xiGaussianRemovePolar_correction_energy_zero P t₀).const_mul C
  filter_upwards [hlim.eventually (Iio_mem_nhds (half_pos ε.property))] with F hF s
  dsimp only
  let t := xiGaussianHeatAfter t₀ s
  let D := Polynomial.C (-(P.eval (-(1 / 4 : ℝ)))) * xiGaussianPolarAnnihilator F
  have hD : xiGaussianRemovePolar P F - P = D := by
    rw [xiGaussianRemovePolar, add_sub_cancel_left]
  rw [hD] at hF
  have hDt : xiGaussianNativeEnergy D t ≤ xiGaussianNativeEnergy D t₀ :=
    xiGaussianNativeEnergy_antitone D s.property
  have hPt : xiGaussianNativeEnergy P t ≤ A := xiGaussianNativeEnergy_antitone P s.property
  have hsmall : xiGaussianNativeEnergy D t < (ε : ℝ) := by
    have hD0 := xiGaussianNativeEnergy_nonneg D t₀
    have hDC := mul_le_mul_of_nonneg_right hC hD0
    rw [one_mul] at hDC
    exact (hDt.trans hDC).trans_lt (hF.trans (by linarith [ε.property]))
  have hb : (η : ℝ) * xiGaussianNativeEnergy P t +
      (1 + 1 / (η : ℝ)) * xiGaussianNativeEnergy D t < (ε : ℝ) := by
    change (η : ℝ) * xiGaussianNativeEnergy P t + C * xiGaussianNativeEnergy D t < (ε : ℝ)
    have hp := mul_le_mul_of_nonneg_left hPt η.property.le
    have hd := mul_le_mul_of_nonneg_left hDt (zero_le_one.trans hC)
    linarith only [hp, hd, hF, hηA]
  have hform : xiGaussianRemovePolar P F = P + D := rfl
  rw [hD, hform]
  refine ⟨hsmall, (norm_xiGaussianHeatTrace_add_sub_le P D t η).trans_lt hb,
    (abs_xiGaussianNativeEnergy_add_sub_le P D t η).trans_lt hb,
    (abs_xiGaussianImaginaryChannel_add_sub_le P D t η).trans_lt hb, ?_⟩
  exact (abs_xiGaussianCompletedSourceResidual_add_sub_le P D t η).trans_lt
    (mul_lt_mul_of_pos_left hb Real.pi_pos)

/-- Every polynomial has an exact pole-free replacement with arbitrarily
small native correction, uniformly over the whole positive heat half-line. -/
theorem exists_xiGaussian_poleFree_native_approximation (P : Polynomial ℝ)
    (t₀ : {t : ℝ // 0 < t}) (ε : {ε : ℝ // 0 < ε}) :
    ∃ Q : Polynomial ℝ, Q.eval (-(1 / 4 : ℝ)) = 0 ∧
      ∀ s : Set.Ici (t₀ : ℝ),
        xiGaussianNativeEnergy (Q - P) (xiGaussianHeatAfter t₀ s) < (ε : ℝ) ∧
        |xiGaussianCompletedSourceResidual Q (xiGaussianHeatAfter t₀ s) -
          xiGaussianCompletedSourceResidual P (xiGaussianHeatAfter t₀ s)| < π * (ε : ℝ) := by
  obtain ⟨F, hF⟩ := (eventually_xiGaussianRemovePolar_heatHalfLine_control P t₀ ε).exists
  exact ⟨xiGaussianRemovePolar P F, xiGaussianRemovePolar_eval_pole P F,
    fun s => ⟨(hF s).1, (hF s).2.2.2.2⟩⟩

/-- After exact polar removal, the literal prime-minus-Gamma expression
approximates minus the original completed residual, uniformly on the entire
heat half-line. It need not approximate the original uncompleted expression. -/
theorem eventually_xiGaussianRemovePolar_primeGamma_completed_control
    (P : Polynomial ℝ) (t₀ : {t : ℝ // 0 < t}) (ε : {ε : ℝ // 0 < ε}) :
    ∀ᶠ F : Finset XiZeroCopy in atTop, ∀ s : Set.Ici (t₀ : ℝ),
      let t := xiGaussianHeatAfter t₀ s
      |xiGaussianPrimeGammaDifference (xiGaussianRemovePolar P F) t +
        xiGaussianCompletedSourceResidual P t| < π * (ε : ℝ) := by
  filter_upwards [eventually_xiGaussianRemovePolar_heatHalfLine_control P t₀ ε] with F hF s
  dsimp only
  rw [xiGaussianPrimeGammaDifference_eq_polar_sub_residual,
    xiGaussianRemovePolar_eval_pole, zero_pow two_ne_zero, mul_zero, zero_mul, zero_sub,
    neg_add_eq_sub, abs_sub_comm]
  exact (hF s).2.2.2.2

end RHTower
