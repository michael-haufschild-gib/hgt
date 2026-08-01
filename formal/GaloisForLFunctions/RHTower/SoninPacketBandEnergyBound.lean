import GaloisForLFunctions.RHTower.SoninBumpFourierL2
import GaloisForLFunctions.RHTower.SoninPacketFourierModulation
import GaloisForLFunctions.RHTower.SoninShiftedTailBound

/-!
# The wavepacket's energy inside a central Fourier band

The packet's spectrum is two translates of the profile's spectrum plus a vanishing multiple of the
untranslated one.  Inside a central band the two translates contribute only what the profile's
spectrum carries beyond the gap between the carrier and the band edge, and the third term carries
the square of the mean.  Both go to zero once the carrier outruns the band.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter
open scoped Topology FourierTransform

/-- The packet's spectral energy density. -/
def soninPacketSpectralDensity (b c : ℝ) (hbc : b < c) (κ : ℝ) : ℝ → ℝ := fun η =>
  ‖𝓕 (fun x : ℝ => (soninPacket b c hbc κ x : ℂ)) η‖ ^ 2

theorem soninPacketSpectralDensity_nonneg (b c : ℝ) (hbc : b < c) (κ η : ℝ) :
    0 ≤ soninPacketSpectralDensity b c hbc κ η := by
  unfold soninPacketSpectralDensity
  positivity

theorem integrable_soninPacketSpectralDensity (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ) :
    Integrable (soninPacketSpectralDensity b c hbc κ) volume := by
  have hLp : Integrable (fun η : ℝ =>
      ‖((fourierUnitary (soninPacketL2 b c hb hbc κ) : SoninL2) : ℝ → ℂ) η‖ ^ 2) volume := by
    have := (Lp.memLp (fourierUnitary (soninPacketL2 b c hb hbc κ))).integrable_norm_rpow
      (by norm_num) (by norm_num)
    simpa using this
  refine hLp.congr ?_
  filter_upwards [fourierUnitary_soninPacketL2_coeFn b c hb hbc κ] with η hη
  unfold soninPacketSpectralDensity
  rw [hη]

/-- Norms of indicators are indicators of norms. -/
theorem norm_sq_indicator (S : Set ℝ) (f : ℝ → ℂ) (ξ : ℝ) :
    ‖S.indicator f ξ‖ ^ 2 = S.indicator (fun η : ℝ => ‖f η‖ ^ 2) ξ := by
  by_cases hmem : ξ ∈ S
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, norm_zero]
    norm_num

/-- The band energy of the packet is the band integral of its spectral density. -/
theorem norm_sq_evenFourierCutoff_soninPacketEven_eq_density
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (t κ : ℝ) :
    ‖evenFourierCutoff t (soninPacketEven b c hb hbc κ)‖ ^ 2 =
      ∫ ξ : ℝ, (centralInterval t).indicator (soninPacketSpectralDensity b c hbc κ) ξ := by
  rw [norm_sq_evenFourierCutoff_soninPacketEven b c hb hbc t κ]
  refine integral_congr_ae ?_
  filter_upwards [fourierUnitary_soninPacketL2_coeFn b c hb hbc κ] with ξ hξ
  rw [norm_sq_indicator]
  by_cases hmem : ξ ∈ centralInterval t
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    unfold soninPacketSpectralDensity
    rw [hξ]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]

/-- **Band energy bound.**  With carrier `a`, the packet's energy inside the band of radius `t` is
controlled by the profile's spectral tail beyond the gap plus the squared mean. -/
theorem norm_sq_evenFourierCutoff_soninPacketEven_le
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) (t a : ℝ) :
    ‖evenFourierCutoff t (soninPacketEven b c hb hbc (2 * Real.pi * a))‖ ^ 2 ≤
      3 * ((2 : ℝ)⁻¹ * (∫ η : ℝ, {η : ℝ | |a| - t ≤ |η|}.indicator
              (soninBumpSpectralDensity b c hbc) η) +
        (soninPacketMean b c hbc (2 * Real.pi * a)) ^ 2 *
          ∫ η : ℝ, soninBumpSpectralDensity b c hbc η) := by
  set μ : ℝ := soninPacketMean b c hbc (2 * Real.pi * a) with hμ
  set D : ℝ → ℝ := soninBumpSpectralDensity b c hbc with hD
  have hDnn : ∀ η, 0 ≤ D η := soninBumpSpectralDensity_nonneg b c hbc
  have hDint : Integrable D volume := integrable_soninBumpSpectralDensity b c hb hbc
  -- pointwise bound from the shifted form of the transform
  have hpt : ∀ ξ : ℝ, soninPacketSpectralDensity b c hbc (2 * Real.pi * a) ξ ≤
      3 * ((4 : ℝ)⁻¹ * D (ξ + (-a)) + (4 : ℝ)⁻¹ * D (ξ + a) + μ ^ 2 * D ξ) := by
    intro ξ
    have hshift := fourier_soninPacket_eq_shift b c hb hbc a ξ
    have hsub : ξ - a = ξ + (-a) := by ring
    unfold soninPacketSpectralDensity
    rw [hshift]
    set X : ℂ := (2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) (ξ - a) with hX
    set Y : ℂ := (2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) (ξ + a) with hY
    set Z : ℂ := (μ : ℂ) * 𝓕 (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) ξ with hZ
    have hXn : ‖X‖ ^ 2 = (4 : ℝ)⁻¹ * D (ξ + (-a)) := by
      rw [hX, norm_mul, hD]
      unfold soninBumpSpectralDensity
      rw [← hsub]
      simp only [norm_inv, Complex.norm_ofNat]
      ring
    have hYn : ‖Y‖ ^ 2 = (4 : ℝ)⁻¹ * D (ξ + a) := by
      rw [hY, norm_mul, hD]
      unfold soninBumpSpectralDensity
      simp only [norm_inv, Complex.norm_ofNat]
      ring
    have hZn : ‖Z‖ ^ 2 = μ ^ 2 * D ξ := by
      rw [hZ, norm_mul, hD]
      unfold soninBumpSpectralDensity
      rw [Complex.norm_real, Real.norm_eq_abs]
      rw [mul_pow, sq_abs]
    have htri : ‖X + Y - Z‖ ≤ ‖X‖ + ‖Y‖ + ‖Z‖ := by
      calc ‖X + Y - Z‖ ≤ ‖X + Y‖ + ‖Z‖ := norm_sub_le _ _
        _ ≤ (‖X‖ + ‖Y‖) + ‖Z‖ := by gcongr; exact norm_add_le _ _
    calc ‖X + Y - Z‖ ^ 2 ≤ (‖X‖ + ‖Y‖ + ‖Z‖) ^ 2 := by
          have h0 : (0 : ℝ) ≤ ‖X + Y - Z‖ := norm_nonneg _
          nlinarith [norm_nonneg X, norm_nonneg Y, norm_nonneg Z]
      _ ≤ 3 * (‖X‖ ^ 2 + ‖Y‖ ^ 2 + ‖Z‖ ^ 2) := by
          nlinarith [sq_nonneg (‖X‖ - ‖Y‖), sq_nonneg (‖X‖ - ‖Z‖), sq_nonneg (‖Y‖ - ‖Z‖)]
      _ = 3 * ((4 : ℝ)⁻¹ * D (ξ + (-a)) + (4 : ℝ)⁻¹ * D (ξ + a) + μ ^ 2 * D ξ) := by
          rw [hXn, hYn, hZn]
  -- integrate the bound over the band
  have hLint : Integrable ((centralInterval t).indicator
      (soninPacketSpectralDensity b c hbc (2 * Real.pi * a))) volume :=
    (integrable_soninPacketSpectralDensity b c hb hbc (2 * Real.pi * a)).indicator
      (measurableSet_centralInterval t)
  have hR1 : Integrable ((centralInterval t).indicator (fun ξ : ℝ => D (ξ + (-a)))) volume :=
    (hDint.comp_add_right (-a)).indicator (measurableSet_centralInterval t)
  have hR2 : Integrable ((centralInterval t).indicator (fun ξ : ℝ => D (ξ + a))) volume :=
    (hDint.comp_add_right a).indicator (measurableSet_centralInterval t)
  have hR3 : Integrable ((centralInterval t).indicator D) volume :=
    hDint.indicator (measurableSet_centralInterval t)
  have hRint : Integrable (fun ξ : ℝ => 3 * ((4 : ℝ)⁻¹ *
      (centralInterval t).indicator (fun η : ℝ => D (η + (-a))) ξ +
      (4 : ℝ)⁻¹ * (centralInterval t).indicator (fun η : ℝ => D (η + a)) ξ +
      μ ^ 2 * (centralInterval t).indicator D ξ)) volume :=
    (((hR1.const_mul _).add (hR2.const_mul _)).add (hR3.const_mul _)).const_mul _
  have hmono : ∫ ξ : ℝ,
        (centralInterval t).indicator (soninPacketSpectralDensity b c hbc (2 * Real.pi * a)) ξ ≤
      ∫ ξ : ℝ, 3 * ((4 : ℝ)⁻¹ *
        (centralInterval t).indicator (fun η : ℝ => D (η + (-a))) ξ +
        (4 : ℝ)⁻¹ * (centralInterval t).indicator (fun η : ℝ => D (η + a)) ξ +
        μ ^ 2 * (centralInterval t).indicator D ξ) := by
    refine integral_mono hLint hRint fun ξ => ?_
    by_cases hmem : ξ ∈ centralInterval t
    · simp only [Set.indicator_of_mem hmem]
      exact hpt ξ
    · simp only [Set.indicator_of_notMem hmem]
      norm_num
  -- evaluate the majorant
  have hsplit : ∫ ξ : ℝ, 3 * ((4 : ℝ)⁻¹ *
        (centralInterval t).indicator (fun η : ℝ => D (η + (-a))) ξ +
        (4 : ℝ)⁻¹ * (centralInterval t).indicator (fun η : ℝ => D (η + a)) ξ +
        μ ^ 2 * (centralInterval t).indicator D ξ) =
      3 * ((4 : ℝ)⁻¹ * (∫ ξ : ℝ, (centralInterval t).indicator
            (fun η : ℝ => D (η + (-a))) ξ) +
        (4 : ℝ)⁻¹ * (∫ ξ : ℝ, (centralInterval t).indicator (fun η : ℝ => D (η + a)) ξ) +
        μ ^ 2 * ∫ ξ : ℝ, (centralInterval t).indicator D ξ) := by
    have hA : Integrable (fun ξ : ℝ =>
        (4 : ℝ)⁻¹ * (centralInterval t).indicator (fun η : ℝ => D (η + (-a))) ξ) volume :=
      hR1.const_mul _
    have hB : Integrable (fun ξ : ℝ =>
        (4 : ℝ)⁻¹ * (centralInterval t).indicator (fun η : ℝ => D (η + a)) ξ) volume :=
      hR2.const_mul _
    have hAB : Integrable (fun ξ : ℝ =>
        (4 : ℝ)⁻¹ * (centralInterval t).indicator (fun η : ℝ => D (η + (-a))) ξ +
          (4 : ℝ)⁻¹ * (centralInterval t).indicator (fun η : ℝ => D (η + a)) ξ) volume :=
      hA.add hB
    have hC : Integrable (fun ξ : ℝ =>
        μ ^ 2 * (centralInterval t).indicator D ξ) volume := hR3.const_mul _
    rw [integral_const_mul, integral_add hAB hC, integral_add hA hB,
      integral_const_mul, integral_const_mul, integral_const_mul]
  have hT1 := integral_indicator_centralInterval_comp_add_le hDint hDnn t (-a)
  have hT2 := integral_indicator_centralInterval_comp_add_le hDint hDnn t a
  have hT3 : ∫ ξ : ℝ, (centralInterval t).indicator D ξ ≤ ∫ η : ℝ, D η := by
    refine integral_mono hR3 hDint fun ξ => ?_
    by_cases hmem : ξ ∈ centralInterval t
    · rw [Set.indicator_of_mem hmem]
    · rw [Set.indicator_of_notMem hmem]
      exact hDnn ξ
  have hμsq : (0 : ℝ) ≤ μ ^ 2 := sq_nonneg μ
  rw [norm_sq_evenFourierCutoff_soninPacketEven_eq_density b c hb hbc t (2 * Real.pi * a)]
  refine hmono.trans ?_
  rw [abs_neg] at hT1
  rw [hsplit]
  nlinarith [hT1, hT2, hT3, hμsq, mul_le_mul_of_nonneg_left hT3 hμsq]

end RHTower
