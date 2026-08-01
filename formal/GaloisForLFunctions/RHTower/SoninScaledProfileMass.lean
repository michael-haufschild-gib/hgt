import GaloisForLFunctions.RHTower.SoninScaledAnnulusProfile

/-!
# The mass of the rescaled annulus profile

The scaling law makes the profile's total mass exactly proportional to the half-width: substituting
the dilation turns the integral at half-width `δ` into `δ` times the integral of the reference
profile.  The mass is positive, since the profile is continuous, nonnegative, and at least one at
the centre of its annulus.

This is the first quantitative consequence of the rescaled construction, and the normalisation any
mean-zero modulation of the profile divides by.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open MeasureTheory Metric Set

/-- The rescaled profile has compact support. -/
theorem hasCompactSupport_soninScaledAnnulusBump (m δ : ℝ) (hδ : 0 < δ) :
    HasCompactSupport (soninScaledAnnulusBump m δ) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := -(|m| + δ)) (b := |m| + δ))
  intro x hx
  rcases soninScaledAnnulusBump_support_subset m δ hδ hx with h | h
  · rw [abs_lt] at h
    constructor <;> [linarith [neg_abs_le m, le_abs_self m]; linarith [le_abs_self m]]
  · rw [abs_lt] at h
    constructor <;> [linarith [le_abs_self m]; linarith [neg_abs_le m, le_abs_self m]]

/-- The rescaled profile is integrable. -/
theorem integrable_soninScaledAnnulusBump (m δ : ℝ) (hδ : 0 < δ) :
    Integrable (soninScaledAnnulusBump m δ) :=
  ((contDiff_soninScaledAnnulusBump m δ hδ).continuous).integrable_of_hasCompactSupport
    (hasCompactSupport_soninScaledAnnulusBump m δ hδ)

/-- **Mass scaling.**  The total mass is the half-width times the reference mass. -/
theorem integral_soninScaledAnnulusBump_scaling (m δ : ℝ) (hδ : 0 < δ) :
    ∫ x : ℝ, soninScaledAnnulusBump m δ x =
      δ * ∫ y : ℝ, soninScaledAnnulusBump (m / δ) 1 y := by
  have hpoint : ∀ x : ℝ, soninScaledAnnulusBump m δ x =
      soninScaledAnnulusBump (m / δ) 1 (x / δ) := fun x =>
    soninScaledAnnulusBump_scaling m δ hδ x
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [MeasureTheory.Measure.integral_comp_div
    (fun y : ℝ => soninScaledAnnulusBump (m / δ) 1 y) δ]
  rw [abs_of_pos hδ, smul_eq_mul]

/-- The rescaled profile has positive mass. -/
theorem integral_soninScaledAnnulusBump_pos (m δ : ℝ) (hδ : 0 < δ) :
    0 < ∫ x : ℝ, soninScaledAnnulusBump m δ x := by
  have hint := integrable_soninScaledAnnulusBump m δ hδ
  have hnonneg : 0 ≤ soninScaledAnnulusBump m δ := fun x =>
    soninScaledAnnulusBump_nonneg m δ x
  rw [integral_pos_iff_support_of_nonneg hnonneg hint]
  have hopen : IsOpen (Function.support (soninScaledAnnulusBump m δ)) :=
    isOpen_ne.preimage ((contDiff_soninScaledAnnulusBump m δ hδ).continuous)
  have hne : m ∈ Function.support (soninScaledAnnulusBump m δ) := by
    have hone := one_le_soninScaledAnnulusBump_center m δ hδ
    have : soninScaledAnnulusBump m δ m ≠ 0 := by
      intro hzero
      rw [hzero] at hone
      linarith
    exact this
  exact hopen.measure_pos volume ⟨_, hne⟩

end RHTower
