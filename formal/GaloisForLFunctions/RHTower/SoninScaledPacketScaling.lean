import GaloisForLFunctions.RHTower.SoninScaledPacket

/-!
# The packet itself is a rescaling

Profile and mean both rescale, so the modulated packet at half-width `δ` and frequency `κ` is the
reference packet at frequency `δκ`, precomposed with the dilation by `δ`.  Every integral quantity
attached to it therefore reduces to the reference one: the energy is `δ` times the reference energy
at the rescaled frequency.

A narrower annulus at a proportionally higher carrier is thus not a new function needing its own
estimate — it is one function seen at another scale.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open MeasureTheory

/-- **The packet rescales.** -/
theorem soninScaledPacket_scaling (m δ κ : ℝ) (hδ : 0 < δ) (x : ℝ) :
    soninScaledPacket m δ κ x = soninScaledPacket (m / δ) 1 (δ * κ) (x / δ) := by
  have hbump : soninScaledAnnulusBump m δ x = soninScaledAnnulusBump (m / δ) 1 (x / δ) :=
    soninScaledAnnulusBump_scaling m δ hδ x
  have hmean : soninScaledPacketMean m δ κ = soninScaledPacketMean (m / δ) 1 (δ * κ) :=
    soninScaledPacketMean_scaling m δ κ hδ
  have hcos : Real.cos (κ * x) = Real.cos (δ * κ * (x / δ)) := by
    congr 1
    field_simp
  rw [soninScaledPacket, soninScaledPacket, hbump, hmean, hcos]

/-- The packet is even. -/
theorem soninScaledPacket_even (m δ κ : ℝ) (x : ℝ) :
    soninScaledPacket m δ κ (-x) = soninScaledPacket m δ κ x := by
  rw [soninScaledPacket, soninScaledPacket, soninScaledAnnulusBump_even m δ x,
    show κ * -x = -(κ * x) by ring, Real.cos_neg]

/-- The packet lives where its profile does. -/
theorem soninScaledPacket_support_subset (m δ κ : ℝ) (hδ : 0 < δ) {x : ℝ}
    (hx : soninScaledPacket m δ κ x ≠ 0) : |x - m| < δ ∨ |x + m| < δ := by
  refine soninScaledAnnulusBump_support_subset m δ hδ ?_
  intro hzero
  exact hx (soninScaledPacket_eq_zero_of_bump_eq_zero m δ κ hzero)

/-- The packet is continuous. -/
theorem continuous_soninScaledPacket (m δ κ : ℝ) (hδ : 0 < δ) :
    Continuous (soninScaledPacket m δ κ) :=
  ((contDiff_soninScaledAnnulusBump m δ hδ).continuous).mul
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).sub continuous_const)

/-- The packet has compact support. -/
theorem hasCompactSupport_soninScaledPacket (m δ κ : ℝ) (hδ : 0 < δ) :
    HasCompactSupport (soninScaledPacket m δ κ) :=
  (hasCompactSupport_soninScaledAnnulusBump m δ hδ).mul_right

/-- **Energy scaling.**  The packet energy is the half-width times the reference energy at the
rescaled frequency. -/
theorem integral_soninScaledPacket_sq_scaling (m δ κ : ℝ) (hδ : 0 < δ) :
    ∫ x : ℝ, soninScaledPacket m δ κ x ^ 2 =
      δ * ∫ y : ℝ, soninScaledPacket (m / δ) 1 (δ * κ) y ^ 2 := by
  have hpoint : ∀ x : ℝ, soninScaledPacket m δ κ x ^ 2 =
      soninScaledPacket (m / δ) 1 (δ * κ) (x / δ) ^ 2 := by
    intro x
    rw [soninScaledPacket_scaling m δ κ hδ x]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
    MeasureTheory.Measure.integral_comp_div
      (fun y : ℝ => soninScaledPacket (m / δ) 1 (δ * κ) y ^ 2) δ,
    abs_of_pos hδ, smul_eq_mul]

end RHTower
