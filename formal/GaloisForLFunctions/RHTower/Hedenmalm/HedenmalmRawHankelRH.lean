import GaloisForLFunctions.RHTower.UnwindowedHankelSignCone
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGaussianHankelRH
import GaloisForLFunctions.RHTower.XiCDerivStripDecay

/-!
# Unwindowed Hedenmalm moment completeness

The actual center-mixed theta Fourier current has exponential decay, uniformly on each closed
aperture substrip, by multiplying the established Xi and derivative bounds. Its raw moments are
therefore integrable and determine its sign through the unwindowed Hankel sign law. Across the
critical aperture the complete raw hierarchy is exactly equivalent to RH.
-/

set_option backward.isDefEq.respectTransparency false
open Complex Real MeasureTheory Set
namespace RHTower
noncomputable section

/-- The actual Fourier current decays exponentially, uniformly on each closed aperture substrip.
Both Xi factors are controlled by the existing contour-shift and Cauchy estimates. -/
theorem exists_abs_thetaCuspCenterMixedFourierCurrent_le_exp
    {A δ : ℝ} (hA : A < 1) (hδ : 0 ≤ δ) (hδpi : 2 * δ < Real.pi / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ) (ha : |a| < 1), |a| ≤ A → ∀ b : ℝ,
      |thetaCuspCenterMixedFourierCurrent a ha b| ≤
        C * Real.exp (-(2 * δ * |b|)) := by
  obtain ⟨C0, hC0, h0⟩ := exists_norm_XiC_horizontal_le hA hδ hδpi
  obtain ⟨C1, hC1, h1⟩ := exists_norm_XiC_deriv_horizontal_le hA hδ hδpi
  refine ⟨2 * C0 * C1, by positivity, fun a ha haA b => ?_⟩
  let z : ℂ := (b : ℂ) - (a : ℂ) * I
  have hz0 : ‖XiC z‖ ≤ C0 * Real.exp (-(δ * |b|)) := by
    simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg, abs_neg, z] using
      h0 b (-a) (by simpa only [abs_neg] using haA)
  have hz1 : ‖deriv XiC z‖ ≤ C1 * Real.exp (-(δ * |b|)) := by
    simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg, abs_neg, z] using
      h1 b (-a) (by simpa only [abs_neg] using haA)
  have hj : |thetaCuspCenterMixedFourierCurrent a ha b| ≤
      2 * (‖XiC z‖ * ‖deriv XiC z‖) := by
    rw [thetaCuspCenterMixedFourierCurrent,
      fourier_thetaCuspHorizontalAutocorrelationTangent_scaled_eq_kreinForm,
      Complex.ofReal_re, thetaXiHankelOrbit_kreinForm_eq,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have h := Complex.abs_re_le_norm
      ((starRingEnd ℂ) (XiC z) * (-I * deriv XiC z))
    simpa only [thetaXiHankelOrbitValuePlus, thetaXiHankelOrbitTangentPlus,
      z, norm_mul, Complex.norm_conj, norm_neg, Complex.norm_I, one_mul] using h
  refine hj.trans ?_
  calc 2 * (‖XiC z‖ * ‖deriv XiC z‖) ≤
      2 * ((C0 * Real.exp (-(δ * |b|))) * (C1 * Real.exp (-(δ * |b|)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hz0 hz1 (norm_nonneg _) (by positivity)) (by norm_num)
    _ = (2 * C0 * C1) * Real.exp (-(2 * δ * |b|)) := by
      rw [show -(2 * δ * |b|) = -(δ * |b|) + -(δ * |b|) by ring,
        Real.exp_add]
      ring

/-- Every raw moment of the actual center-mixed Fourier current is integrable. -/
theorem integrable_rawMoment_thetaCuspCenterMixedFourierCurrent
    (a : ℝ) (ha : |a| < 1) (n : ℕ) :
    Integrable (fun b : ℝ => b ^ n * thetaCuspCenterMixedFourierCurrent a ha b) := by
  obtain ⟨C, hC, hb⟩ := exists_abs_thetaCuspCenterMixedFourierCurrent_le_exp
    (A := |a|) (δ := Real.pi / 8) ha (by positivity) (by linarith [Real.pi_pos])
  exact integrable_rawMoment_of_expDecay
    (continuous_thetaCuspCenterMixedFourierCurrent a ha) hC (by positivity)
    (hb a ha le_rfl) n

/-- All unwindowed current moments form a complete sign test at each physical aperture. -/
theorem hedenmalmRawHankelCone_at_iff_pointwise (a : ℝ) (ha : |a| < 1) :
    CompleteHankelCone (weightedMoment volume (thetaCuspCenterMixedFourierCurrent a ha)) ↔
      ∀ b : ℝ, 0 ≤ thetaCuspCenterMixedFourierCurrent a ha b := by
  obtain ⟨C, hC, hb⟩ := exists_abs_thetaCuspCenterMixedFourierCurrent_le_exp
    (A := |a|) (δ := Real.pi / 8) ha (by positivity) (by linarith [Real.pi_pos])
  exact completeHankelCone_rawMoment_iff_of_expDecay
    (continuous_thetaCuspCenterMixedFourierCurrent a ha) hC (by positivity)
    (hb a ha le_rfl)

/-- The complete raw Hedenmalm moment hierarchy throughout the critical aperture. -/
def HedenmalmRawHankelCone : Prop :=
  ∀ (a : ℝ) (ha : |a| < 1), 0 < a → a < 1/2 →
    CompleteHankelCone (weightedMoment volume (thetaCuspCenterMixedFourierCurrent a ha))

/-- **Unwindowed Hedenmalm criterion.** The actual raw moment hierarchy is equivalent to RH.
Exponential decay and moment determinacy are fully discharged by the theta source. -/
theorem hedenmalmRawHankelCone_iff_riemannHypothesis :
    HedenmalmRawHankelCone ↔ RiemannHypothesis := by
  rw [← thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis]
  constructor
  · intro h a ha ha0 hahalf b
    exact (hedenmalmRawHankelCone_at_iff_pointwise a ha).mp (h a ha ha0 hahalf) b
  · intro h a ha ha0 hahalf
    exact (hedenmalmRawHankelCone_at_iff_pointwise a ha).mpr (h a ha ha0 hahalf)

end
end RHTower
