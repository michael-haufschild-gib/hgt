import GaloisForLFunctions.RHTower.SoninPacketFourierPointwise

/-!
# Modulation shifts the Fourier transform

Multiplying by a unimodular character translates the Fourier transform.  The wavepacket is the
profile times a cosine, corrected by a multiple of the profile, so its transform is the average of
two translates of the profile's transform minus that multiple of the untranslated one.

This is the exact shape the frequency-concentration estimate needs: the carrier translates the
profile's transform, it does not deform it, so the mass left near the origin is a tail of a fixed
`L²` function at a radius growing with the carrier.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter
open scoped Topology FourierTransform Real

/-- **Modulation identity.**  Multiplying by `exp (2 pi i a x)` translates the Fourier transform
by `a`. -/
theorem fourier_exp_mul (f : ℝ → ℂ) (a ξ : ℝ) :
    𝓕 (fun x : ℝ => Complex.exp ((↑(2 * Real.pi * a * x) : ℂ) * Complex.I) * f x) ξ =
      𝓕 f (ξ - a) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I) *
      (Complex.exp ((↑(2 * Real.pi * a * x) : ℂ) * Complex.I) * f x) =
    Complex.exp ((↑(-2 * Real.pi * x * (ξ - a)) : ℂ) * Complex.I) * f x
  rw [← mul_assoc, ← Complex.exp_add, ← add_mul]
  congr 2
  push_cast
  ring

/-- The complexified profile times a character is integrable. -/
theorem integrable_exp_mul_soninAnnulusBump (b c : ℝ) (hb : 0 < b) (hbc : b < c) (a : ℝ) :
    Integrable (fun x : ℝ =>
      Complex.exp ((↑(2 * Real.pi * a * x) : ℂ) * Complex.I) *
        (soninAnnulusBump b c hbc x : ℂ)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)).mul
      (Complex.continuous_ofReal.comp (continuous_soninAnnulusBump b c hbc))
  · refine HasCompactSupport.of_support_subset_isCompact
      (hasCompactSupport_soninAnnulusBump b c hb hbc) ?_
    intro x hx
    refine subset_tsupport _ ?_
    intro h0
    exact hx (by simp [h0])

/-- The complexified profile is integrable. -/
theorem integrable_ofReal_soninAnnulusBump (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    Integrable (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) :=
  (integrable_soninAnnulusBump b c hb hbc).ofReal

/-- **Shifted form of the packet's transform.**  With carrier `a`, the transform of the wavepacket
is the average of the two translates of the profile's transform, corrected by the mean. -/
theorem fourier_soninPacket_eq_shift (b c : ℝ) (hb : 0 < b) (hbc : b < c) (a ξ : ℝ) :
    𝓕 (fun x : ℝ => (soninPacket b c hbc (2 * Real.pi * a) x : ℂ)) ξ =
      (2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) (ξ - a) +
        (2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) (ξ + a) -
        ((soninPacketMean b c hbc (2 * Real.pi * a) : ℝ) : ℂ) *
          𝓕 (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) ξ := by
  have hpt : ∀ x : ℝ, (soninPacket b c hbc (2 * Real.pi * a) x : ℂ) =
      (2 : ℂ)⁻¹ * (Complex.exp ((↑(2 * Real.pi * a * x) : ℂ) * Complex.I) *
          (soninAnnulusBump b c hbc x : ℂ)) +
        (2 : ℂ)⁻¹ * (Complex.exp ((↑(2 * Real.pi * (-a) * x) : ℂ) * Complex.I) *
          (soninAnnulusBump b c hbc x : ℂ)) -
        ((soninPacketMean b c hbc (2 * Real.pi * a) : ℝ) : ℂ) *
          (soninAnnulusBump b c hbc x : ℂ) := by
    intro x
    have key : ∀ z : ℂ, (2 : ℂ)⁻¹ * Complex.exp (z * Complex.I) +
        (2 : ℂ)⁻¹ * Complex.exp (-z * Complex.I) = Complex.cos z := by
      intro z
      rw [Complex.cos]
      ring
    have hneg : ((2 * Real.pi * (-a) * x : ℝ) : ℂ) = -((2 * Real.pi * a * x : ℝ) : ℂ) := by
      push_cast
      ring
    have hcos : ((Real.cos ((2 * Real.pi * a) * x) : ℝ) : ℂ) =
        (2 : ℂ)⁻¹ * Complex.exp ((↑(2 * Real.pi * a * x) : ℂ) * Complex.I) +
          (2 : ℂ)⁻¹ * Complex.exp ((↑(2 * Real.pi * (-a) * x) : ℂ) * Complex.I) := by
      rw [show (2 * Real.pi * a) * x = 2 * Real.pi * a * x by ring, Complex.ofReal_cos,
        hneg, ← key ((↑(2 * Real.pi * a * x) : ℂ))]
    show ((soninAnnulusBump b c hbc x * (Real.cos ((2 * Real.pi * a) * x) -
        soninPacketMean b c hbc (2 * Real.pi * a)) : ℝ) : ℂ) = _
    rw [Complex.ofReal_mul, Complex.ofReal_sub, hcos]
    ring
  have hI1 := integrable_exp_mul_soninAnnulusBump b c hb hbc a
  have hI2 := integrable_exp_mul_soninAnnulusBump b c hb hbc (-a)
  have hI3 := integrable_ofReal_soninAnnulusBump b c hb hbc
  have hsum : 𝓕 (fun x : ℝ => (soninPacket b c hbc (2 * Real.pi * a) x : ℂ)) ξ =
      (2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ =>
          Complex.exp ((↑(2 * Real.pi * a * x) : ℂ) * Complex.I) *
            (soninAnnulusBump b c hbc x : ℂ)) ξ +
        (2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ =>
          Complex.exp ((↑(2 * Real.pi * (-a) * x) : ℂ) * Complex.I) *
            (soninAnnulusBump b c hbc x : ℂ)) ξ -
        ((soninPacketMean b c hbc (2 * Real.pi * a) : ℝ) : ℂ) *
          𝓕 (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) ξ := by
    rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
      Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
    simp only [smul_eq_mul]
    have hJ1 : Integrable (fun x : ℝ =>
        Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I) *
          (Complex.exp ((↑(2 * Real.pi * a * x) : ℂ) * Complex.I) *
            (soninAnnulusBump b c hbc x : ℂ))) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · exact (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)).mul
          ((Complex.continuous_exp.comp
            ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)).mul
            (Complex.continuous_ofReal.comp (continuous_soninAnnulusBump b c hbc)))
      · refine HasCompactSupport.of_support_subset_isCompact
          (hasCompactSupport_soninAnnulusBump b c hb hbc) ?_
        intro x hx
        refine subset_tsupport _ ?_
        intro h0
        exact hx (by simp [h0])
    have hJ2 : Integrable (fun x : ℝ =>
        Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I) *
          (Complex.exp ((↑(2 * Real.pi * (-a) * x) : ℂ) * Complex.I) *
            (soninAnnulusBump b c hbc x : ℂ))) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · exact (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)).mul
          ((Complex.continuous_exp.comp
            ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)).mul
            (Complex.continuous_ofReal.comp (continuous_soninAnnulusBump b c hbc)))
      · refine HasCompactSupport.of_support_subset_isCompact
          (hasCompactSupport_soninAnnulusBump b c hb hbc) ?_
        intro x hx
        refine subset_tsupport _ ?_
        intro h0
        exact hx (by simp [h0])
    have hJ3 : Integrable (fun x : ℝ =>
        Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I) *
          (soninAnnulusBump b c hbc x : ℂ)) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ ?_
      · exact (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)).mul
          (Complex.continuous_ofReal.comp (continuous_soninAnnulusBump b c hbc))
      · refine HasCompactSupport.of_support_subset_isCompact
          (hasCompactSupport_soninAnnulusBump b c hb hbc) ?_
        intro x hx
        refine subset_tsupport _ ?_
        intro h0
        exact hx (by simp [h0])
    calc ∫ v : ℝ, Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
            (soninPacket b c hbc (2 * Real.pi * a) v : ℂ)
        = ∫ v : ℝ, ((2 : ℂ)⁻¹ * (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
              (Complex.exp ((↑(2 * Real.pi * a * v) : ℂ) * Complex.I) *
                (soninAnnulusBump b c hbc v : ℂ))) +
            (2 : ℂ)⁻¹ * (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
              (Complex.exp ((↑(2 * Real.pi * (-a) * v) : ℂ) * Complex.I) *
                (soninAnnulusBump b c hbc v : ℂ))) -
            ((soninPacketMean b c hbc (2 * Real.pi * a) : ℝ) : ℂ) *
              (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
                (soninAnnulusBump b c hbc v : ℂ))) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
          show Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
              (soninPacket b c hbc (2 * Real.pi * a) v : ℂ) = _
          rw [hpt v]
          ring
      _ = ((∫ v : ℝ, (2 : ℂ)⁻¹ * (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
              (Complex.exp ((↑(2 * Real.pi * a * v) : ℂ) * Complex.I) *
                (soninAnnulusBump b c hbc v : ℂ)))) +
            ∫ v : ℝ, (2 : ℂ)⁻¹ * (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
              (Complex.exp ((↑(2 * Real.pi * (-a) * v) : ℂ) * Complex.I) *
                (soninAnnulusBump b c hbc v : ℂ)))) -
            ∫ v : ℝ, ((soninPacketMean b c hbc (2 * Real.pi * a) : ℝ) : ℂ) *
              (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
                (soninAnnulusBump b c hbc v : ℂ)) := by
          have hA : Integrable (fun v : ℝ => (2 : ℂ)⁻¹ *
              (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
                (Complex.exp ((↑(2 * Real.pi * a * v) : ℂ) * Complex.I) *
                  (soninAnnulusBump b c hbc v : ℂ)))) := hJ1.const_mul _
          have hB : Integrable (fun v : ℝ => (2 : ℂ)⁻¹ *
              (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
                (Complex.exp ((↑(2 * Real.pi * (-a) * v) : ℂ) * Complex.I) *
                  (soninAnnulusBump b c hbc v : ℂ)))) := hJ2.const_mul _
          have hAB : Integrable (fun v : ℝ => (2 : ℂ)⁻¹ *
                (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
                  (Complex.exp ((↑(2 * Real.pi * a * v) : ℂ) * Complex.I) *
                    (soninAnnulusBump b c hbc v : ℂ))) +
              (2 : ℂ)⁻¹ *
                (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
                  (Complex.exp ((↑(2 * Real.pi * (-a) * v) : ℂ) * Complex.I) *
                    (soninAnnulusBump b c hbc v : ℂ)))) := hA.add hB
          have hC : Integrable (fun v : ℝ =>
              ((soninPacketMean b c hbc (2 * Real.pi * a) : ℝ) : ℂ) *
                (Complex.exp ((↑(-2 * Real.pi * v * ξ) : ℂ) * Complex.I) *
                  (soninAnnulusBump b c hbc v : ℂ))) := hJ3.const_mul _
          rw [integral_sub hAB hC, integral_add hA hB]
      _ = _ := by
          rw [integral_const_mul, integral_const_mul, integral_const_mul]

  rw [hsum, fourier_exp_mul, fourier_exp_mul]
  congr 2
  rw [sub_neg_eq_add]

end RHTower
