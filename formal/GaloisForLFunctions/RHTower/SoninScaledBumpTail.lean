import GaloisForLFunctions.RHTower.SoninReferenceProfileDecay
import GaloisForLFunctions.RHTower.SoninMellinBlindness

/-!
# The cosine mass of the profile is a reference tail

The profile is two lobes, so its transform is one lobe's read at both signs, and each of those is
the reference transform at the rescaled frequency.  The cosine-weighted mass of the profile is the
average of its transform at `±w`, hence bounded by the half-width times reference tail values at
`±δw`.

This is the numerator of the packet's mean, so the mean too is governed by the reference tail in the
variable `δ w`.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory
open scoped Topology FourierTransform

/-- A lobe of the profile is integrable. -/
theorem integrable_soninOneSidedBump (m δ : ℝ) (hδ : 0 < δ) :
    Integrable fun x : ℝ => ((soninOneSidedBump m δ x : ℝ) : ℂ) := by
  have hcont : Continuous fun x : ℝ => ((soninOneSidedBump m δ x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp
      (soninUnitBumpData.continuous.comp ((continuous_id.sub continuous_const).div_const δ))
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc (a := m - δ) (b := m + δ)) ?_
  intro x hx
  have hbump : soninUnitBumpData ((x - m) / δ) ≠ 0 := by
    intro hzero
    exact hx (by simp [soninOneSidedBump, hzero])
  have hball : |(x - m) / δ| < 1 := by
    by_contra hcon
    push Not at hcon
    exact hbump (soninUnitBumpData_eq_zero_of_one_le hcon)
  rw [abs_div, abs_of_pos hδ, div_lt_one hδ] at hball
  rw [Set.mem_Icc]
  rcases abs_lt.mp hball with ⟨h1, h2⟩
  constructor <;> linarith

/-- The profile's transform is a lobe's read at both signs. -/
theorem fourier_soninScaledAnnulusBump_eq_oneSided (m δ : ℝ) (hδ : 0 < δ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => ((soninScaledAnnulusBump m δ x : ℝ) : ℂ)) ξ =
      𝓕 (fun x : ℝ => ((soninOneSidedBump m δ x : ℝ) : ℂ)) ξ +
        𝓕 (fun x : ℝ => ((soninOneSidedBump m δ x : ℝ) : ℂ)) (-ξ) := by
  have hint := integrable_soninOneSidedBump m δ hδ
  have hrefl : Integrable fun x : ℝ =>
      (fun y : ℝ => ((soninOneSidedBump m δ y : ℝ) : ℂ)) (-x) := hint.comp_neg
  have hsplit : (fun x : ℝ => ((soninScaledAnnulusBump m δ x : ℝ) : ℂ)) =
      fun x : ℝ => ((soninOneSidedBump m δ x : ℝ) : ℂ) +
        (fun y : ℝ => ((soninOneSidedBump m δ y : ℝ) : ℂ)) (-x) := by
    funext x
    rw [soninScaledAnnulusBump_eq_oneSided_add m δ x]
    push_cast
    ring
  rw [hsplit, GaloisForLFunctions.HTGeometry.fourierIntegral_add hint hrefl ξ]
  congr 1
  exact fourier_comp_neg (fun y : ℝ => ((soninOneSidedBump m δ y : ℝ) : ℂ)) ξ

/-- **The profile's spectrum is two reference tails.** -/
theorem norm_fourier_soninScaledAnnulusBump_le (m δ : ℝ) (hδ : 0 < δ) (ξ : ℝ) :
    ‖𝓕 (fun x : ℝ => ((soninScaledAnnulusBump m δ x : ℝ) : ℂ)) ξ‖ ≤
      δ * ‖𝓕 soninUnitBumpC (δ * ξ)‖ + δ * ‖𝓕 soninUnitBumpC (δ * -ξ)‖ := by
  rw [fourier_soninScaledAnnulusBump_eq_oneSided m δ hδ ξ]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_fourier_soninOneSidedBump m δ hδ ξ, norm_fourier_soninOneSidedBump m δ hδ (-ξ)]

/-- **The cosine mass of the profile is bounded by reference tails.** -/
theorem abs_integral_soninScaledAnnulusBump_mul_cos_le (m δ w : ℝ) (hδ : 0 < δ) :
    |∫ x : ℝ, soninScaledAnnulusBump m δ x * Real.cos (2 * Real.pi * w * x)| ≤
      δ * ‖𝓕 soninUnitBumpC (δ * w)‖ + δ * ‖𝓕 soninUnitBumpC (δ * -w)‖ +
        (δ * ‖𝓕 soninUnitBumpC (δ * -w)‖ + δ * ‖𝓕 soninUnitBumpC (δ * -(-w))‖) := by
  have hcont : Continuous fun x : ℝ => ((soninScaledAnnulusBump m δ x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (contDiff_soninScaledAnnulusBump m δ hδ).continuous
  have hsupp : HasCompactSupport fun x : ℝ => ((soninScaledAnnulusBump m δ x : ℝ) : ℂ) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (hasCompactSupport_soninScaledAnnulusBump m δ hδ) ?_
    intro x hx
    refine subset_tsupport _ ?_
    intro h0
    exact hx (by simp [h0])
  have havg := integral_mul_cos_eq_fourier_avg hcont hsupp w
  have hreal : ((∫ x : ℝ, soninScaledAnnulusBump m δ x * Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ) =
      ∫ x : ℝ, ((soninScaledAnnulusBump m δ x : ℝ) : ℂ) *
        (Real.cos (2 * Real.pi * w * x) : ℂ) := by
    have hint : Integrable fun x : ℝ =>
        soninScaledAnnulusBump m δ x * Real.cos (2 * Real.pi * w * x) := by
      have hc : Continuous fun x : ℝ =>
          soninScaledAnnulusBump m δ x * Real.cos (2 * Real.pi * w * x) :=
        ((contDiff_soninScaledAnnulusBump m δ hδ).continuous).mul
          (Real.continuous_cos.comp (continuous_const.mul continuous_id))
      exact hc.integrable_of_hasCompactSupport
        (hasCompactSupport_soninScaledAnnulusBump m δ hδ).mul_right
    rw [show ((∫ x : ℝ, soninScaledAnnulusBump m δ x *
          Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ) =
        Complex.ofRealCLM (∫ x : ℝ, soninScaledAnnulusBump m δ x *
          Real.cos (2 * Real.pi * w * x)) from rfl,
      ← Complex.ofRealCLM.integral_comp_comm hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Complex.ofRealCLM (soninScaledAnnulusBump m δ x * Real.cos (2 * Real.pi * w * x)) =
      ((soninScaledAnnulusBump m δ x : ℝ) : ℂ) * ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ)
    rw [Complex.ofRealCLM_apply, Complex.ofReal_mul]
  have hnorm : |∫ x : ℝ, soninScaledAnnulusBump m δ x * Real.cos (2 * Real.pi * w * x)| =
      ‖(2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ => ((soninScaledAnnulusBump m δ x : ℝ) : ℂ)) w +
        (2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ => ((soninScaledAnnulusBump m δ x : ℝ) : ℂ)) (-w)‖ := by
    rw [← havg, ← hreal, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖(2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ => ((soninScaledAnnulusBump m δ x : ℝ) : ℂ)) w‖ ≤
      δ * ‖𝓕 soninUnitBumpC (δ * w)‖ + δ * ‖𝓕 soninUnitBumpC (δ * -w)‖ := by
    rw [norm_mul]
    refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)) ?_
    exact norm_fourier_soninScaledAnnulusBump_le m δ hδ w
  have h2 : ‖(2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ => ((soninScaledAnnulusBump m δ x : ℝ) : ℂ)) (-w)‖ ≤
      δ * ‖𝓕 soninUnitBumpC (δ * -w)‖ + δ * ‖𝓕 soninUnitBumpC (δ * -(-w))‖ := by
    rw [norm_mul]
    refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)) ?_
    exact norm_fourier_soninScaledAnnulusBump_le m δ hδ (-w)
  exact add_le_add h1 h2

end RHTower
