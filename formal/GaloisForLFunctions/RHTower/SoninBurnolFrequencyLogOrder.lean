import GaloisForLFunctions.RHTower.SoninBurnolLogShellChannel
import GaloisForLFunctions.RHTower.SoninChannelAnnulusBound
import GaloisForLFunctions.RHTower.SoninChannelMovingThreshold
import GaloisForLFunctions.RHTower.SoninPacketChannelHeightBound
import GaloisForLFunctions.RHTower.SoninPacketHighTailPolynomial

/-!
# The Burnol shell conductor has only logarithmic order on source packets

The position half of the conductor is uniformly bounded because every source packet has fixed
physical support.  The reflected half sees the moving Fourier carrier.  Its exact packet tail is
polynomial, so the moving-threshold shell estimate leaves only the largest logarithm below twice
the carrier.  Consequently the full conductor pairing is bounded by an affine function of the
carrier logarithm, uniformly over every finite tower height.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

/-- Shell logarithms below twice a carrier are bounded by the base logarithm plus the carrier
logarithm. -/
theorem abs_log_logShellRadius_le_abs_log_add_log_two_mul
    {a r A : ℝ} (ha : 0 < a) (hr : 1 < r) (hA : 1 ≤ A) (k : ℕ)
    (hk : logShellRadius a r k ≤ 2 * A) :
    |Real.log (logShellRadius a r k)| ≤ |Real.log a| + Real.log (2 * A) := by
  have hρpos : 0 < logShellRadius a r k := logShellRadius_pos ha hr k
  have haρ : a ≤ logShellRadius a r k := by
    simpa [logShellRadius] using logShellRadius_mono ha hr (Nat.zero_le k)
  have hloglo : Real.log a ≤ Real.log (logShellRadius a r k) :=
    Real.log_le_log ha haρ
  have hloghi : Real.log (logShellRadius a r k) ≤ Real.log (2 * A) :=
    Real.log_le_log hρpos hk
  have hlogT0 : 0 ≤ Real.log (2 * A) :=
    Real.log_nonneg (by linarith)
  have habslo : -|Real.log a| ≤ Real.log a := neg_abs_le _
  have habs0 : 0 ≤ |Real.log a| := abs_nonneg _
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- **Exact order theorem.**  On canonical source packets the full concrete Burnol conductor has
at most affine-logarithmic quadratic-form growth.  Constants depend on fixed annulus and tower
geometry, but neither on carrier nor on the arbitrary tower height. -/
theorem exists_re_inner_soninPacketEven_soninBurnolLogShellConductor_le_log
    (b c : ℝ) (hb : 0 < b) (hbc : b < c)
    (a₀ r₀ : ℝ) (ha₀ : 0 < a₀) (hr₀ : 1 < r₀) :
    ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ ∀ (A : ℝ) (n : ℕ), 1 ≤ A →
      (⟪soninPacketEven b c hb hbc (2 * Real.pi * A),
        soninBurnolLogShellConductor a₀ r₀ n
          (soninPacketEven b c hb hbc (2 * Real.pi * A))⟫_ℂ).re ≤
        C₀ + C₁ * Real.log A := by
  obtain ⟨Ctail, hCtail0, htail⟩ :=
    exists_norm_sq_sub_evenFourierCutoff_soninPacketEven_le_powerTail_eleven b c hb hbc
  obtain ⟨Cpos, hCpos0, hpos⟩ :=
    exists_bound_norm_evenLogShellChannel_of_annulus a₀ r₀ c ha₀ hr₀ (hb.trans hbc)
  set B : ℝ := 2 * ‖soninBumpL2 b c hb hbc‖ with hB
  set D : ℝ := 4 * Ctail / a₀ ^ 10 * (1 - (r₀ ^ 10)⁻¹)⁻¹ with hD
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hrpow : (1 : ℝ) < r₀ ^ 10 := one_lt_pow₀ hr₀ (by norm_num)
  have hratio : (r₀ ^ 10)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hrpow
  have hD0 : 0 ≤ D := by
    rw [hD]
    positivity
  refine ⟨B * (Cpos * B + B * (|Real.log a₀| + Real.log 2) + Real.sqrt D),
    B ^ 2, ?_, sq_nonneg B, ?_⟩
  · have hlog20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  intro A n hA
  set w : evenSubspace := soninPacketEven b c hb hbc (2 * Real.pi * A) with hw
  set M : ℝ := |Real.log a₀| + Real.log (2 * A) with hMdef
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hT : (1 : ℝ) ≤ 2 * A := by linarith
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact add_nonneg (abs_nonneg _) (Real.log_nonneg hT)
  have hwB : ‖w‖ ≤ B := by
    rw [hB, hw]
    exact norm_soninPacketL2_le b c hb hbc _
  have hhigh : evenIndicatorCutoff c w = w := by
    rw [hw]
    exact evenIndicatorCutoff_soninPacketEven_eq_self b c hb hbc _
  have hposnorm : ‖evenLogShellChannel a₀ r₀ n w‖ ≤ Cpos * B :=
    (hpos n w hhigh).trans (mul_le_mul_of_nonneg_left hwB hCpos0)
  have hfreq0 : ‖evenFourierLogShellChannel a₀ r₀ n w‖ ≤
      Real.sqrt (M ^ 2 * ‖w‖ ^ 2 + D) := by
    rw [hD]
    refine norm_evenFourierLogShellChannel_apply_le_of_moving_powerTail
      ha₀ hr₀ hT (p := 10) (by norm_num) n w ?_ hCtail0 ?_
    · intro k hk
      rw [hMdef]
      exact abs_log_logShellRadius_le_abs_log_add_log_two_mul ha₀ hr₀ hA k hk
    · intro t ht
      rw [norm_sub_evenIndicatorCutoff_evenFourierTransform, hw]
      exact htail A t hApos ht
  have hinside : M ^ 2 * ‖w‖ ^ 2 + D ≤ M ^ 2 * B ^ 2 + D := by
    have hsq : ‖w‖ ^ 2 ≤ B ^ 2 := by
      nlinarith [norm_nonneg w]
    simpa only [add_comm] using
      add_le_add_right (mul_le_mul_of_nonneg_left hsq (sq_nonneg M)) D
  have hsqrt1 : Real.sqrt (M ^ 2 * ‖w‖ ^ 2 + D) ≤
      Real.sqrt (M ^ 2 * B ^ 2 + D) := Real.sqrt_le_sqrt hinside
  have hsqrt2 : Real.sqrt (M ^ 2 * B ^ 2 + D) ≤ M * B + Real.sqrt D := by
    have hsD := Real.sq_sqrt hD0
    have hrhs0 : 0 ≤ M * B + Real.sqrt D := by positivity
    have hsq : M ^ 2 * B ^ 2 + D ≤ (M * B + Real.sqrt D) ^ 2 := by
      have hid : (M * B + Real.sqrt D) ^ 2 =
          M ^ 2 * B ^ 2 + D + 2 * (M * B) * Real.sqrt D := by
        nlinarith
      rw [hid]
      exact le_add_of_nonneg_right (by positivity)
    have hs := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hrhs0] at hs
  have hfreq : ‖evenFourierLogShellChannel a₀ r₀ n w‖ ≤
      M * B + Real.sqrt D := hfreq0.trans (hsqrt1.trans hsqrt2)
  have hHnorm : ‖soninBurnolLogShellConductor a₀ r₀ n w‖ ≤
      Cpos * B + (M * B + Real.sqrt D) := by
    calc ‖soninBurnolLogShellConductor a₀ r₀ n w‖
        = ‖evenLogShellChannel a₀ r₀ n w +
            evenFourierLogShellChannel a₀ r₀ n w‖ := by rfl
      _ ≤ ‖evenLogShellChannel a₀ r₀ n w‖ +
          ‖evenFourierLogShellChannel a₀ r₀ n w‖ := norm_add_le _ _
      _ ≤ Cpos * B + (M * B + Real.sqrt D) := add_le_add hposnorm hfreq
  have hre : (⟪w, soninBurnolLogShellConductor a₀ r₀ n w⟫_ℂ).re ≤
      ‖(⟪w, soninBurnolLogShellConductor a₀ r₀ n w⟫_ℂ)‖ := Complex.re_le_norm _
  have hinner : ‖(⟪w, soninBurnolLogShellConductor a₀ r₀ n w⟫_ℂ)‖ ≤
      ‖w‖ * ‖soninBurnolLogShellConductor a₀ r₀ n w‖ := norm_inner_le_norm _ _
  have hprod : ‖w‖ * ‖soninBurnolLogShellConductor a₀ r₀ n w‖ ≤
      B * (Cpos * B + (M * B + Real.sqrt D)) :=
    mul_le_mul hwB hHnorm (norm_nonneg _) hB0
  have hlog : Real.log (2 * A) = Real.log 2 + Real.log A := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hApos.ne']
  have hident : B * (Cpos * B + (M * B + Real.sqrt D)) =
      B * (Cpos * B + B * (|Real.log a₀| + Real.log 2) + Real.sqrt D) +
        B ^ 2 * Real.log A := by
    rw [hMdef, hlog]
    ring
  rw [hw]
  exact le_trans (le_trans hre (le_trans hinner hprod)) (le_of_eq hident)

end RHTower
