import GaloisForLFunctions.RHTower.SoninScaledProfileMass

/-!
# The modulated packet on the rescaled profile

Substituting the dilation into the cosine-weighted integral turns it into the reference integral at
the rescaled frequency, and the same substitution scales the mass.  The two factors of the
half-width cancel in the ratio, so the packet's mean depends on the width and the frequency only
through their product.

That is the width dependence the earlier construction could not express: with an abstract bump the
profiles of two widths are unrelated, so no such statement exists for them.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open MeasureTheory

/-- The cosine-weighted profile is integrable. -/
theorem integrable_soninScaledAnnulusBump_mul_cos (m δ κ : ℝ) (hδ : 0 < δ) :
    Integrable fun x : ℝ => soninScaledAnnulusBump m δ x * Real.cos (κ * x) := by
  have hcont : Continuous fun x : ℝ => soninScaledAnnulusBump m δ x * Real.cos (κ * x) :=
    ((contDiff_soninScaledAnnulusBump m δ hδ).continuous).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  refine hcont.integrable_of_hasCompactSupport ?_
  exact (hasCompactSupport_soninScaledAnnulusBump m δ hδ).mul_right

/-- **Numerator scaling.**  The cosine-weighted mass is the half-width times the reference mass at
the rescaled frequency. -/
theorem integral_soninScaledAnnulusBump_mul_cos_scaling (m δ κ : ℝ) (hδ : 0 < δ) :
    ∫ x : ℝ, soninScaledAnnulusBump m δ x * Real.cos (κ * x) =
      δ * ∫ y : ℝ, soninScaledAnnulusBump (m / δ) 1 y * Real.cos (δ * κ * y) := by
  have hpoint : ∀ x : ℝ, soninScaledAnnulusBump m δ x * Real.cos (κ * x) =
      soninScaledAnnulusBump (m / δ) 1 (x / δ) * Real.cos (δ * κ * (x / δ)) := by
    intro x
    rw [soninScaledAnnulusBump_scaling m δ hδ x]
    congr 2
    field_simp
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
    MeasureTheory.Measure.integral_comp_div
      (fun y : ℝ => soninScaledAnnulusBump (m / δ) 1 y * Real.cos (δ * κ * y)) δ,
    abs_of_pos hδ, smul_eq_mul]

/-- The mean of the cosine against the rescaled profile. -/
def soninScaledPacketMean (m δ κ : ℝ) : ℝ :=
  (∫ x : ℝ, soninScaledAnnulusBump m δ x * Real.cos (κ * x)) /
    ∫ x : ℝ, soninScaledAnnulusBump m δ x

/-- **The mean sees only the product of width and frequency.** -/
theorem soninScaledPacketMean_scaling (m δ κ : ℝ) (hδ : 0 < δ) :
    soninScaledPacketMean m δ κ = soninScaledPacketMean (m / δ) 1 (δ * κ) := by
  rw [soninScaledPacketMean, soninScaledPacketMean,
    integral_soninScaledAnnulusBump_mul_cos_scaling m δ κ hδ,
    integral_soninScaledAnnulusBump_scaling m δ hδ]
  rw [mul_div_mul_left _ _ hδ.ne']

/-- The mean-zero modulation of the rescaled profile. -/
def soninScaledPacket (m δ κ : ℝ) : ℝ → ℝ := fun x =>
  soninScaledAnnulusBump m δ x * (Real.cos (κ * x) - soninScaledPacketMean m δ κ)

theorem soninScaledPacket_eq_zero_of_bump_eq_zero (m δ κ : ℝ) {x : ℝ}
    (hx : soninScaledAnnulusBump m δ x = 0) : soninScaledPacket m δ κ x = 0 := by
  rw [soninScaledPacket, hx, zero_mul]

/-- **The second Meyer condition.**  The modulated packet has vanishing integral. -/
theorem integral_soninScaledPacket (m δ κ : ℝ) (hδ : 0 < δ) :
    ∫ x : ℝ, soninScaledPacket m δ κ x = 0 := by
  have hmass : (0 : ℝ) < ∫ x : ℝ, soninScaledAnnulusBump m δ x :=
    integral_soninScaledAnnulusBump_pos m δ hδ
  have hA : Integrable fun x : ℝ => soninScaledAnnulusBump m δ x * Real.cos (κ * x) :=
    integrable_soninScaledAnnulusBump_mul_cos m δ κ hδ
  have hB : Integrable fun x : ℝ =>
      soninScaledAnnulusBump m δ x * soninScaledPacketMean m δ κ :=
    (integrable_soninScaledAnnulusBump m δ hδ).mul_const _
  have hsplit : ∀ x : ℝ, soninScaledPacket m δ κ x =
      soninScaledAnnulusBump m δ x * Real.cos (κ * x) -
        soninScaledAnnulusBump m δ x * soninScaledPacketMean m δ κ := by
    intro x
    rw [soninScaledPacket]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit), integral_sub hA hB,
    integral_mul_const, soninScaledPacketMean]
  field_simp
  ring

end RHTower
