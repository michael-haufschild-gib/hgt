import GaloisForLFunctions.RHTower.SoninAnnulusBump
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The frequency-locked annular wavepacket

Modulating the annular profile by a cosine and subtracting its mean produces a smooth, even,
compactly supported function with two exact vanishing conditions: it is zero at the origin — its
support avoids a neighbourhood of the origin — and it has zero total integral.  Those are exactly
the two Meyer Poisson-source conditions.

The frequency is carried as a single parameter here; the wavepacket family of the nonannihilation
theorem is obtained by letting it grow linearly in the dilation scale.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set

/-- The annular profile is integrable. -/
theorem integrable_soninAnnulusBump (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    Integrable (soninAnnulusBump b c hbc) :=
  (continuous_soninAnnulusBump b c hbc).integrable_of_hasCompactSupport
    (hasCompactSupport_soninAnnulusBump b c hb hbc)

/-- Its modulated version is integrable too. -/
theorem integrable_soninAnnulusBump_mul_cos (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ) :
    Integrable (fun x : ℝ => soninAnnulusBump b c hbc x * Real.cos (κ * x)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (continuous_soninAnnulusBump b c hbc).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  · exact (hasCompactSupport_soninAnnulusBump b c hb hbc).mul_right

/-- The annular profile has positive total mass. -/
theorem integral_soninAnnulusBump_pos (b c : ℝ) (hb : 0 < b) (hbc : b < c) :
    0 < ∫ x : ℝ, soninAnnulusBump b c hbc x := by
  have hint := integrable_soninAnnulusBump b c hb hbc
  have hnonneg : 0 ≤ soninAnnulusBump b c hbc := fun x =>
    soninAnnulusBump_nonneg b c hbc x
  rw [integral_pos_iff_support_of_nonneg hnonneg hint]
  have hopen : IsOpen (Function.support (soninAnnulusBump b c hbc)) :=
    isOpen_ne.preimage (continuous_soninAnnulusBump b c hbc)
  have hne : ((b + c) / 2) ∈ Function.support (soninAnnulusBump b c hbc) := by
    have := soninAnnulusBump_midpoint b c hb hbc
    simp only [Function.mem_support, this]
    exact one_ne_zero
  exact hopen.measure_pos volume ⟨_, hne⟩

/-- The mean of the modulated profile against the profile's mass. -/
def soninPacketMean (b c : ℝ) (hbc : b < c) (κ : ℝ) : ℝ :=
  (∫ x : ℝ, soninAnnulusBump b c hbc x * Real.cos (κ * x)) /
    (∫ x : ℝ, soninAnnulusBump b c hbc x)

/-- The frequency-locked annular wavepacket: the profile times a cosine, corrected to have zero
total integral. -/
def soninPacket (b c : ℝ) (hbc : b < c) (κ : ℝ) : ℝ → ℝ := fun x =>
  soninAnnulusBump b c hbc x * (Real.cos (κ * x) - soninPacketMean b c hbc κ)

theorem soninPacket_even (b c : ℝ) (hbc : b < c) (κ x : ℝ) :
    soninPacket b c hbc κ (-x) = soninPacket b c hbc κ x := by
  simp only [soninPacket, soninAnnulusBump_even b c hbc x, mul_neg, Real.cos_neg]

theorem continuous_soninPacket (b c : ℝ) (hbc : b < c) (κ : ℝ) :
    Continuous (soninPacket b c hbc κ) :=
  (continuous_soninAnnulusBump b c hbc).mul
    (((Real.continuous_cos.comp (continuous_const.mul continuous_id))).sub continuous_const)

theorem contDiff_soninPacket (b c : ℝ) (hbc : b < c) (κ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (soninPacket b c hbc κ) :=
  (contDiff_soninAnnulusBump b c hbc).mul
    ((Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).sub contDiff_const)

theorem soninPacket_support_subset (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ)
    {x : ℝ} (hx : soninPacket b c hbc κ x ≠ 0) : b < |x| ∧ |x| < c := by
  refine soninAnnulusBump_support_subset b c hb hbc ?_
  intro h0
  exact hx (by simp only [soninPacket, h0, zero_mul])

theorem soninPacket_eq_zero_of_abs_le (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ)
    {x : ℝ} (hx : |x| ≤ b) : soninPacket b c hbc κ x = 0 := by
  by_contra hne
  exact absurd hx (not_le.mpr (soninPacket_support_subset b c hb hbc κ hne).1)

theorem soninPacket_eq_zero_of_le_abs (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ)
    {x : ℝ} (hx : c ≤ |x|) : soninPacket b c hbc κ x = 0 := by
  by_contra hne
  exact absurd hx (not_le.mpr (soninPacket_support_subset b c hb hbc κ hne).2)

theorem hasCompactSupport_soninPacket (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ) :
    HasCompactSupport (soninPacket b c hbc κ) :=
  (hasCompactSupport_soninAnnulusBump b c hb hbc).mul_right

theorem integrable_soninPacket (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ) :
    Integrable (soninPacket b c hbc κ) :=
  (continuous_soninPacket b c hbc κ).integrable_of_hasCompactSupport
    (hasCompactSupport_soninPacket b c hb hbc κ)

/-- **First Meyer condition.**  The packet vanishes at the origin. -/
theorem soninPacket_zero (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ) :
    soninPacket b c hbc κ 0 = 0 :=
  soninPacket_eq_zero_of_abs_le b c hb hbc κ (by simpa using hb.le)

/-- **Second Meyer condition.**  The packet has zero total integral, so its Fourier transform
vanishes at the origin. -/
theorem integral_soninPacket (b c : ℝ) (hb : 0 < b) (hbc : b < c) (κ : ℝ) :
    ∫ x : ℝ, soninPacket b c hbc κ x = 0 := by
  have hmass := (integral_soninAnnulusBump_pos b c hb hbc).ne'
  have h1 := integrable_soninAnnulusBump_mul_cos b c hb hbc κ
  have h2 : Integrable
      (fun x : ℝ => soninPacketMean b c hbc κ * soninAnnulusBump b c hbc x) :=
    (integrable_soninAnnulusBump b c hb hbc).const_mul _
  have hstep : ∫ x : ℝ, soninPacket b c hbc κ x =
      (∫ x : ℝ, soninAnnulusBump b c hbc x * Real.cos (κ * x)) -
        ∫ x : ℝ, soninPacketMean b c hbc κ * soninAnnulusBump b c hbc x := by
    rw [← integral_sub h1 h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [soninPacket]
    ring
  have hmean : soninPacketMean b c hbc κ * ∫ x : ℝ, soninAnnulusBump b c hbc x =
      ∫ x : ℝ, soninAnnulusBump b c hbc x * Real.cos (κ * x) := by
    unfold soninPacketMean
    field_simp
  rw [hstep, integral_const_mul, hmean, sub_self]

end RHTower
