import GaloisForLFunctions.RHTower.SoninAnnulusBump

/-!
# An annulus profile that is one fixed profile rescaled

The corpus's annulus bump is built from a `ContDiffBump` whose radii depend on the annulus, and
mathlib's bump family is abstract, so nothing relates the profiles of two different annuli.  Here the
profile is instead one fixed reference bump precomposed with a dilation, so profiles of different
widths are related by an exact scaling law.

That law is what carries width dependence through a Fourier estimate: the transform of the profile
at half-width `δ` is `δ` times the transform of the reference profile at `δ` times the frequency.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open Metric Set

/-- The reference profile: one fixed smooth bump on the unit scale. -/
def soninUnitBumpData : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The reference profile placed at `±m` with half-width `δ`. -/
def soninScaledAnnulusBump (m δ : ℝ) : ℝ → ℝ := fun x =>
  soninUnitBumpData ((x - m) / δ) + soninUnitBumpData ((-x - m) / δ)

theorem soninScaledAnnulusBump_even (m δ : ℝ) (x : ℝ) :
    soninScaledAnnulusBump m δ (-x) = soninScaledAnnulusBump m δ x := by
  simp only [soninScaledAnnulusBump, neg_neg]
  ring

theorem soninScaledAnnulusBump_nonneg (m δ : ℝ) (x : ℝ) :
    0 ≤ soninScaledAnnulusBump m δ x :=
  add_nonneg soninUnitBumpData.nonneg soninUnitBumpData.nonneg

theorem contDiff_soninScaledAnnulusBump (m δ : ℝ) (_hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (soninScaledAnnulusBump m δ) := by
  have hone : ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => (x - m) / δ :=
    ((contDiff_id.sub contDiff_const).div_const δ)
  have htwo : ContDiff ℝ (⊤ : ℕ∞) fun x : ℝ => (-x - m) / δ :=
    (((contDiff_neg).sub contDiff_const).div_const δ)
  exact (soninUnitBumpData.contDiff.comp hone).add (soninUnitBumpData.contDiff.comp htwo)

/-- **The scaling law.**  The profile of half-width `δ` is the unit-width profile precomposed with
the dilation by `δ`. -/
theorem soninScaledAnnulusBump_scaling (m δ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    soninScaledAnnulusBump m δ x = soninScaledAnnulusBump (m / δ) 1 (x / δ) := by
  have h₁ : x / δ - m / δ = (x - m) / δ := by field_simp
  have h₂ : -(x / δ) - m / δ = (-x - m) / δ := by field_simp
  simp only [soninScaledAnnulusBump, div_one, h₁, h₂]

/-- The reference profile vanishes outside the unit ball. -/
theorem soninUnitBumpData_eq_zero_of_one_le {y : ℝ} (hy : 1 ≤ |y|) :
    soninUnitBumpData y = 0 := by
  refine soninUnitBumpData.zero_of_le_dist ?_
  rw [Real.dist_eq, sub_zero]
  exact hy

/-- The profile lives in the two intervals of half-width `δ` around `±m`. -/
theorem soninScaledAnnulusBump_support_subset (m δ : ℝ) (hδ : 0 < δ) {x : ℝ}
    (hx : soninScaledAnnulusBump m δ x ≠ 0) : |x - m| < δ ∨ |x + m| < δ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h₁, h₂⟩ := hcon
  have hz₁ : soninUnitBumpData ((x - m) / δ) = 0 := by
    refine soninUnitBumpData_eq_zero_of_one_le ?_
    rw [abs_div, abs_of_pos hδ, le_div_iff₀ hδ]
    linarith
  have hz₂ : soninUnitBumpData ((-x - m) / δ) = 0 := by
    refine soninUnitBumpData_eq_zero_of_one_le ?_
    rw [abs_div, abs_of_pos hδ, le_div_iff₀ hδ]
    have habs : |(-x - m)| = |x + m| := by
      rw [show -x - m = -(x + m) by ring, abs_neg]
    rw [habs]
    linarith
  rw [soninScaledAnnulusBump, hz₁, hz₂, add_zero] at hx
  exact hx rfl

/-- The profile is at least one at the centre of its annulus. -/
theorem one_le_soninScaledAnnulusBump_center (m δ : ℝ) (_hδ : 0 < δ) :
    1 ≤ soninScaledAnnulusBump m δ m := by
  have hone : soninUnitBumpData ((m - m) / δ) = 1 := by
    refine soninUnitBumpData.one_of_mem_closedBall ?_
    rw [mem_closedBall, Real.dist_eq, sub_zero, sub_self, zero_div, abs_zero]
    exact le_of_lt (by norm_num : (0 : ℝ) < 1 / 2)
  have hnn : 0 ≤ soninUnitBumpData ((-m - m) / δ) := soninUnitBumpData.nonneg
  rw [soninScaledAnnulusBump, hone]
  linarith

end RHTower
