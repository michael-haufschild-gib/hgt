import GaloisForLFunctions.RHTower.SoninScaledProfileSquareTail

/-!
# The rescaled packet keeps a definite share of its profile's energy

Squaring the packet turns the carrier into a constant plus a doubled carrier, so the packet's energy
is half the squared profile's mass plus two oscillatory corrections and a nonnegative mean term.
Both corrections are cosine masses of the squared profile, hence reference-square tails, while the
mass itself is the half-width times a positive constant.

So the packet's energy is at least the half-width times that constant, minus quantities that are
small once the product of half-width and carrier is large — and this is uniform in the annulus,
since neither the mass nor the tail bound sees the centre.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory
open scoped FourierTransform

/-- The squared profile is integrable. -/
theorem integrable_soninScaledAnnulusBump_sq (m δ : ℝ) (hδ : 0 < δ) :
    Integrable fun x : ℝ => soninScaledAnnulusBump m δ x ^ 2 := by
  have hcont : Continuous fun x : ℝ => soninScaledAnnulusBump m δ x ^ 2 :=
    (contDiff_soninScaledAnnulusBump m δ hδ).continuous.pow 2
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact
    (hasCompactSupport_soninScaledAnnulusBump m δ hδ) ?_
  intro x hx
  refine subset_tsupport _ ?_
  intro h0
  exact hx (by simp [h0])

/-- The squared profile against a cosine is integrable. -/
theorem integrable_soninScaledAnnulusBump_sq_mul_cos (m δ w : ℝ) (hδ : 0 < δ) :
    Integrable fun x : ℝ =>
      soninScaledAnnulusBump m δ x ^ 2 * Real.cos (2 * Real.pi * w * x) := by
  have hcont : Continuous fun x : ℝ =>
      soninScaledAnnulusBump m δ x ^ 2 * Real.cos (2 * Real.pi * w * x) :=
    ((contDiff_soninScaledAnnulusBump m δ hδ).continuous.pow 2).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.mul_right ?_
  refine HasCompactSupport.of_support_subset_isCompact
    (hasCompactSupport_soninScaledAnnulusBump m δ hδ) ?_
  intro x hx
  refine subset_tsupport _ ?_
  intro h0
  exact hx (by simp [h0])

/-- **The energy identity.**  Half the squared profile's mass, two oscillatory corrections, and a
nonnegative mean term. -/
theorem norm_sq_soninScaledPacketEven_eq_expansion (m δ w : ℝ) (hδ : 0 < δ) :
    ‖soninScaledPacketEven m δ (2 * Real.pi * w) hδ‖ ^ 2 =
      2⁻¹ * (∫ x : ℝ, soninScaledAnnulusBump m δ x ^ 2) +
        2⁻¹ * (∫ x : ℝ, soninScaledAnnulusBump m δ x ^ 2 *
          Real.cos (2 * Real.pi * (2 * w) * x)) +
        -(2 * soninScaledPacketMean m δ (2 * Real.pi * w)) *
          (∫ x : ℝ, soninScaledAnnulusBump m δ x ^ 2 * Real.cos (2 * Real.pi * w * x)) +
        soninScaledPacketMean m δ (2 * Real.pi * w) ^ 2 *
          (∫ x : ℝ, soninScaledAnnulusBump m δ x ^ 2) := by
  set μ : ℝ := soninScaledPacketMean m δ (2 * Real.pi * w) with hμ
  have hsq := integrable_soninScaledAnnulusBump_sq m δ hδ
  have hcos2 := integrable_soninScaledAnnulusBump_sq_mul_cos m δ (2 * w) hδ
  have hcos1 := integrable_soninScaledAnnulusBump_sq_mul_cos m δ w hδ
  have hsplit : ∀ x : ℝ, soninScaledPacket m δ (2 * Real.pi * w) x ^ 2 =
      2⁻¹ * (soninScaledAnnulusBump m δ x ^ 2) +
        2⁻¹ * (soninScaledAnnulusBump m δ x ^ 2 *
          Real.cos (2 * Real.pi * (2 * w) * x)) +
        -(2 * μ) * (soninScaledAnnulusBump m δ x ^ 2 *
          Real.cos (2 * Real.pi * w * x)) +
        μ ^ 2 * (soninScaledAnnulusBump m δ x ^ 2) := by
    intro x
    have hc : Real.cos (2 * Real.pi * w * x) ^ 2 =
        2⁻¹ + 2⁻¹ * Real.cos (2 * Real.pi * (2 * w) * x) := by
      have h := Real.cos_sq (2 * Real.pi * w * x)
      have harg : 2 * (2 * Real.pi * w * x) = 2 * Real.pi * (2 * w) * x := by ring
      rw [harg] at h
      linarith
    calc soninScaledPacket m δ (2 * Real.pi * w) x ^ 2
        = soninScaledAnnulusBump m δ x ^ 2 * Real.cos (2 * Real.pi * w * x) ^ 2 -
            2 * μ * (soninScaledAnnulusBump m δ x ^ 2 *
              Real.cos (2 * Real.pi * w * x)) +
            μ ^ 2 * soninScaledAnnulusBump m δ x ^ 2 := by
          rw [soninScaledPacket]
          ring
      _ = _ := by rw [hc]; ring
  rw [norm_sq_soninScaledPacketEven m δ (2 * Real.pi * w) hδ,
    integral_congr_ae (Filter.Eventually.of_forall hsplit),
    integral_add (((hsq.const_mul _).add (hcos2.const_mul _)).add (hcos1.const_mul _))
      (hsq.const_mul _),
    integral_add ((hsq.const_mul _).add (hcos2.const_mul _)) (hcos1.const_mul _),
    integral_add (hsq.const_mul _) (hcos2.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]

/-- **The packet's energy floor.**  Up to reference-square tails, the packet keeps the half-width
times the reference square's mass. -/
theorem norm_sq_soninScaledPacketEven_ge (m δ w : ℝ) (hδ : 0 < δ) (hm : δ < m) :
    δ * (∫ y : ℝ, soninUnitBumpSq y) -
        (2 * δ * soninRefSqTailSup (δ * |w|) +
          2 * (|soninScaledPacketMean m δ (2 * Real.pi * w)| *
            (4 * δ * soninRefSqTailSup (δ * |w|)))) ≤
      ‖soninScaledPacketEven m δ (2 * Real.pi * w) hδ‖ ^ 2 := by
  set μ : ℝ := soninScaledPacketMean m δ (2 * Real.pi * w) with hμ
  set S : ℝ := soninRefSqTailSup (δ * |w|) with hS
  set I : ℝ := ∫ y : ℝ, soninUnitBumpSq y with hI
  set B : ℝ := ∫ x : ℝ, soninScaledAnnulusBump m δ x ^ 2 *
    Real.cos (2 * Real.pi * (2 * w) * x) with hB
  set C : ℝ := ∫ x : ℝ, soninScaledAnnulusBump m δ x ^ 2 *
    Real.cos (2 * Real.pi * w * x) with hC
  have hIpos : 0 < I := integral_soninUnitBumpSq_pos
  have hSnn : 0 ≤ S := soninRefSqTailSup_nonneg _
  have hA : (∫ x : ℝ, soninScaledAnnulusBump m δ x ^ 2) = 2 * δ * I :=
    integral_soninScaledAnnulusBump_sq_eq m δ hδ hm
  have hBbound : |B| ≤ 4 * δ * S := by
    refine abs_integral_soninScaledAnnulusBump_sq_mul_cos_le_tailSup m δ (2 * w) (δ * |w|)
      hδ hm ?_
    rw [abs_mul, abs_two]
    nlinarith [abs_nonneg w, hδ]
  have hCbound : |C| ≤ 4 * δ * S :=
    abs_integral_soninScaledAnnulusBump_sq_mul_cos_le_tailSup m δ w (δ * |w|) hδ hm le_rfl
  have hnegB : -|B| ≤ B := neg_abs_le B
  have habsC : |2 * μ * C| = 2 * (|μ| * |C|) := by
    rw [abs_mul, abs_mul, abs_two]
  have hnegC : -(2 * μ * C) ≤ 2 * (|μ| * |C|) := by
    rw [← habsC]
    exact neg_le_abs _
  have hmuC : |μ| * |C| ≤ |μ| * (4 * δ * S) :=
    mul_le_mul_of_nonneg_left hCbound (abs_nonneg μ)
  have hmean : 0 ≤ μ ^ 2 * (2 * δ * I) := by positivity
  rw [norm_sq_soninScaledPacketEven_eq_expansion m δ w hδ, hA]
  linarith [hBbound, hnegB, hnegC, hmuC, hmean]

end RHTower
