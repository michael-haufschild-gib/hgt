import GaloisForLFunctions.RHTower.SoninScaledBumpTail

/-!
# The packet mean is a reference tail

Both lobes carry the same mass, so the profile's total mass is exactly twice the half-width times
the reference mass — with no dependence on the annulus centre.  Dividing the cosine bound by it
cancels the half-width, leaving the mean bounded by reference tail values at `±δw` alone.

So the mean is small as soon as the product of half-width and frequency is large, uniformly over the
annuli of the family.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory
open scoped FourierTransform

/-- The reference profile is integrable. -/
theorem integrable_soninUnitBumpData : Integrable soninUnitBumpData := by
  refine soninUnitBumpData.continuous.integrable_of_hasCompactSupport ?_
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro x hx
  have hball : |x| < 1 := by
    by_contra hcon
    push Not at hcon
    exact hx (soninUnitBumpData_eq_zero_of_one_le hcon)
  rw [Set.mem_Icc]
  rcases abs_lt.mp hball with ⟨h1, h2⟩
  constructor <;> linarith

/-- The reference profile has positive mass. -/
theorem integral_soninUnitBumpData_pos : 0 < ∫ y : ℝ, soninUnitBumpData y := by
  rw [integral_pos_iff_support_of_nonneg (fun _ => soninUnitBumpData.nonneg)
    integrable_soninUnitBumpData]
  have hopen : IsOpen (Function.support soninUnitBumpData) :=
    isOpen_ne.preimage soninUnitBumpData.continuous
  have hne : (0 : ℝ) ∈ Function.support soninUnitBumpData := by
    have hone : soninUnitBumpData 0 = 1 := by
      refine soninUnitBumpData.one_of_mem_closedBall ?_
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_zero]
      exact le_of_lt soninUnitBumpData.rIn_pos
    simp only [Function.mem_support, hone]
    exact one_ne_zero
  exact hopen.measure_pos volume ⟨_, hne⟩

/-- A lobe carries the half-width times the reference mass. -/
theorem integral_soninOneSidedBump (m δ : ℝ) (hδ : 0 < δ) :
    ∫ x : ℝ, soninOneSidedBump m δ x = δ * ∫ y : ℝ, soninUnitBumpData y := by
  have hshift : ∫ x : ℝ, soninUnitBumpData ((x + -m) / δ) =
      ∫ x : ℝ, soninUnitBumpData (x / δ) :=
    MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun u : ℝ => soninUnitBumpData (u / δ)) (-m)
  have hpoint : ∀ x : ℝ, soninOneSidedBump m δ x = soninUnitBumpData ((x + -m) / δ) := by
    intro x
    show soninUnitBumpData ((x - m) / δ) = soninUnitBumpData ((x + -m) / δ)
    congr 2
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), hshift,
    MeasureTheory.Measure.integral_comp_div soninUnitBumpData δ, abs_of_pos hδ, smul_eq_mul]

/-- **The profile's mass is centre free.** -/
theorem integral_soninScaledAnnulusBump_eq (m δ : ℝ) (hδ : 0 < δ) :
    ∫ x : ℝ, soninScaledAnnulusBump m δ x = 2 * δ * ∫ y : ℝ, soninUnitBumpData y := by
  have hlobe : Integrable (soninOneSidedBump m δ) := by
    have hc : Continuous (soninOneSidedBump m δ) :=
      soninUnitBumpData.continuous.comp ((continuous_id.sub continuous_const).div_const δ)
    refine hc.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc (a := m - δ) (b := m + δ)) ?_
    intro x hx
    have hbump : soninUnitBumpData ((x - m) / δ) ≠ 0 := hx
    have hball : |(x - m) / δ| < 1 := by
      by_contra hcon
      push Not at hcon
      exact hbump (soninUnitBumpData_eq_zero_of_one_le hcon)
    rw [abs_div, abs_of_pos hδ, div_lt_one hδ] at hball
    rw [Set.mem_Icc]
    rcases abs_lt.mp hball with ⟨h1, h2⟩
    constructor <;> linarith
  have hrefl : ∫ x : ℝ, soninOneSidedBump m δ (-x) = ∫ x : ℝ, soninOneSidedBump m δ x :=
    MeasureTheory.integral_neg_eq_self (soninOneSidedBump m δ) volume
  have hsplit : ∀ x : ℝ, soninScaledAnnulusBump m δ x =
      soninOneSidedBump m δ x + soninOneSidedBump m δ (-x) :=
    soninScaledAnnulusBump_eq_oneSided_add m δ
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
    integral_add hlobe hlobe.comp_neg, hrefl, integral_soninOneSidedBump m δ hδ]
  ring

/-- **The mean is a reference tail.**  The half-width cancels between numerator and denominator. -/
theorem abs_soninScaledPacketMean_le (m δ w : ℝ) (hδ : 0 < δ) :
    |soninScaledPacketMean m δ (2 * Real.pi * w)| ≤
      (‖𝓕 soninUnitBumpC (δ * w)‖ + ‖𝓕 soninUnitBumpC (δ * -w)‖ +
          (‖𝓕 soninUnitBumpC (δ * -w)‖ + ‖𝓕 soninUnitBumpC (δ * -(-w))‖)) /
        (2 * ∫ y : ℝ, soninUnitBumpData y) := by
  have hmass : (0 : ℝ) < ∫ y : ℝ, soninUnitBumpData y := integral_soninUnitBumpData_pos
  have hden : ∫ x : ℝ, soninScaledAnnulusBump m δ x = 2 * δ * ∫ y : ℝ, soninUnitBumpData y :=
    integral_soninScaledAnnulusBump_eq m δ hδ
  have hnum := abs_integral_soninScaledAnnulusBump_mul_cos_le m δ w hδ
  rw [soninScaledPacketMean, abs_div, hden, abs_of_pos (by positivity : (0:ℝ) < 2 * δ *
    ∫ y : ℝ, soninUnitBumpData y)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hkey : |∫ x : ℝ, soninScaledAnnulusBump m δ x * Real.cos (2 * Real.pi * w * x)| ≤
      δ * ‖𝓕 soninUnitBumpC (δ * w)‖ + δ * ‖𝓕 soninUnitBumpC (δ * -w)‖ +
        (δ * ‖𝓕 soninUnitBumpC (δ * -w)‖ + δ * ‖𝓕 soninUnitBumpC (δ * -(-w))‖) := hnum
  nlinarith [hmass, hδ, norm_nonneg (𝓕 soninUnitBumpC (δ * w)),
    norm_nonneg (𝓕 soninUnitBumpC (δ * -w)), norm_nonneg (𝓕 soninUnitBumpC (δ * -(-w)))]

end RHTower
