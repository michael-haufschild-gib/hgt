import GaloisForLFunctions.HTGeometry.FourierPowerBound
import GaloisForLFunctions.HTGeometry.PowerTailIntegral
import GaloisForLFunctions.RHTower.SoninMellinBlindness
import GaloisForLFunctions.RHTower.SoninPacketHighBandCapture

/-!
# Uniform polynomial high-frequency tail of the canonical Sonin packet

The qualitative concentration theorem is not enough for a tower whose height may grow with the
packet carrier.  Here compactly supported smoothness of the fixed annulus profile is used at a
specific order.  Outside twice the carrier, all three translates in the exact Fourier formula are
far from the origin.  Their squared sum is therefore of twelfth order, and integration leaves an
eleventh-order bound on the discarded energy.

The constant depends only on the fixed annulus.  It is independent of carrier and cutoff radius.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory
open scoped FourierTransform

/-- The canonical packet's spectral density has a uniform twelfth-order tail outside twice its
carrier. -/
theorem exists_soninPacketSpectralDensity_le_powerTail_twelve
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ A ξ : ℝ, 0 < A → 2 * A ≤ |ξ| →
      soninPacketSpectralDensity b c hbc (2 * Real.pi * A) ξ ≤
        K * |ξ| ^ (-(12 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ :=
    GaloisForLFunctions.HTGeometry.exists_pow_mul_norm_fourierIntegral_le
      (hasCompactSupport_ofReal_soninAnnulusBump b c hb hbc)
      (contDiff_ofReal_soninAnnulusBump b c hbc) 6
  refine ⟨4 * C ^ 2 * 2 ^ 12, by positivity, ?_⟩
  intro A ξ hA hξ
  have hξpos : 0 < |ξ| := by linarith
  have hAabs : |A| = A := abs_of_pos hA
  have hminus : |ξ| / 2 ≤ |ξ - A| := by
    have hbase : |ξ| - |A| ≤ |ξ - A| := abs_sub_abs_le_abs_sub ξ A
    rw [hAabs] at hbase
    linarith
  have hplus : |ξ| / 2 ≤ |ξ + A| := by
    have hbase : |ξ| - |-A| ≤ |ξ - (-A)| := abs_sub_abs_le_abs_sub ξ (-A)
    simp only [abs_neg, hAabs, sub_neg_eq_add] at hbase
    linarith
  have hhalfpos : 0 < |ξ| / 2 := by positivity
  have hdecay : ∀ v : ℝ, |ξ| / 2 ≤ |v| →
      ‖𝓕 (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) v‖ ≤
        C / (|ξ| / 2) ^ 6 := by
    intro v hv
    have hvpos : 0 < |v| := lt_of_lt_of_le hhalfpos hv
    have hvpow : (|ξ| / 2) ^ 6 ≤ |v| ^ 6 := pow_le_pow_left₀ hhalfpos.le hv 6
    have hmul := hC v
    rw [le_div_iff₀ (pow_pos hhalfpos 6)]
    calc ‖𝓕 (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) v‖ * (|ξ| / 2) ^ 6
        = (|ξ| / 2) ^ 6 * ‖𝓕 (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) v‖ := by ring
      _
        ≤ |v| ^ 6 * ‖𝓕 (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) v‖ :=
          mul_le_mul_of_nonneg_right hvpow (norm_nonneg _)
      _ ≤ C := hmul
  have hshift := fourier_soninPacket_eq_shift b c hb hbc A ξ
  set X : ℂ := (2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) (ξ - A)
  set Y : ℂ := (2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) (ξ + A)
  set Z : ℂ := ((soninPacketMean b c hbc (2 * Real.pi * A) : ℝ) : ℂ) *
    𝓕 (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) ξ
  have hmean := abs_soninPacketMean_le_one b c hb hbc (2 * Real.pi * A)
  have hX : ‖X‖ ≤ (2 : ℝ)⁻¹ * (C / (|ξ| / 2) ^ 6) := by
    rw [show X = (2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ =>
      (soninAnnulusBump b c hbc x : ℂ)) (ξ - A) by rfl, norm_mul]
    simp only [norm_inv, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left (hdecay _ hminus) (by positivity)
  have hY : ‖Y‖ ≤ (2 : ℝ)⁻¹ * (C / (|ξ| / 2) ^ 6) := by
    rw [show Y = (2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ =>
      (soninAnnulusBump b c hbc x : ℂ)) (ξ + A) by rfl, norm_mul]
    simp only [norm_inv, Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left (hdecay _ hplus) (by positivity)
  have hZ : ‖Z‖ ≤ C / (|ξ| / 2) ^ 6 := by
    rw [show Z = ((soninPacketMean b c hbc (2 * Real.pi * A) : ℝ) : ℂ) *
      𝓕 (fun x : ℝ => (soninAnnulusBump b c hbc x : ℂ)) ξ by rfl, norm_mul,
      Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (by positivity) hmean).trans
      (hdecay ξ (by linarith))
  have hsum : ‖X + Y - Z‖ ≤ 2 * (C / (|ξ| / 2) ^ 6) := by
    calc ‖X + Y - Z‖ ≤ ‖X‖ + ‖Y‖ + ‖Z‖ := by
          calc ‖X + Y - Z‖ ≤ ‖X + Y‖ + ‖Z‖ := norm_sub_le _ _
            _ ≤ ‖X‖ + ‖Y‖ + ‖Z‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (2 : ℝ)⁻¹ * (C / (|ξ| / 2) ^ 6) +
            (2 : ℝ)⁻¹ * (C / (|ξ| / 2) ^ 6) + C / (|ξ| / 2) ^ 6 :=
          add_le_add (add_le_add hX hY) hZ
      _ = 2 * (C / (|ξ| / 2) ^ 6) := by ring
  have hnonneg : 0 ≤ C / (|ξ| / 2) ^ 6 := by positivity
  have hsquare : ‖X + Y - Z‖ ^ 2 ≤ (2 * (C / (|ξ| / 2) ^ 6)) ^ 2 := by
    nlinarith [norm_nonneg (X + Y - Z)]
  have hrpow : |ξ| ^ (-(12 : ℝ)) = (|ξ| ^ 12)⁻¹ := by
    rw [Real.rpow_neg (abs_nonneg ξ)]
    norm_num [Real.rpow_natCast]
  unfold soninPacketSpectralDensity
  rw [hshift]
  change ‖X + Y - Z‖ ^ 2 ≤ _
  refine hsquare.trans (le_of_eq ?_)
  rw [hrpow]
  field_simp
  ring

/-- Integrating the pointwise estimate leaves an eleventh-order bound on the packet energy above
any band outside twice the carrier. -/
theorem exists_norm_sq_sub_evenFourierCutoff_soninPacketEven_le_powerTail_eleven
    (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A t : ℝ, 0 < A → 2 * A ≤ t →
      ‖soninPacketEven b c hb hbc (2 * Real.pi * A) -
          evenFourierCutoff t (soninPacketEven b c hb hbc (2 * Real.pi * A))‖ ^ 2 ≤
        C / t ^ 11 := by
  obtain ⟨K, hK0, hK⟩ := exists_soninPacketSpectralDensity_le_powerTail_twelve b c hb hbc
  refine ⟨2 * K / 11, by positivity, ?_⟩
  intro A t hA ht
  have htpos : 0 < t := by linarith
  have houter := norm_sq_sub_evenFourierCutoff_soninPacketEven_le_outer b c hb hbc t
    (2 * Real.pi * A)
  rw [integral_indicator (GaloisForLFunctions.HTGeometry.measurableSet_centralTail t)] at houter
  refine houter.trans ?_
  have hint := GaloisForLFunctions.HTGeometry.setIntegral_le_of_le_powerTail
    (fun ξ => soninPacketSpectralDensity_nonneg b c hbc (2 * Real.pi * A) ξ)
    htpos (by norm_num : (1 : ℝ) < 12)
    (fun ξ hξ => hK A ξ hA (le_trans ht hξ))
  refine hint.trans (le_of_eq ?_)
  have hrpow : t ^ (1 - (12 : ℝ)) = (t ^ 11)⁻¹ := by
    rw [show (1 : ℝ) - 12 = -(11 : ℝ) by norm_num,
      Real.rpow_neg (le_of_lt htpos)]
    norm_num [Real.rpow_natCast]
  rw [hrpow]
  ring

end RHTower
