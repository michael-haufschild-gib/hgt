import GaloisForLFunctions.RHTower.SoninScaledProfileSquare

/-!
# The squared profile's spectral tail

The squared profile is two translated dilates of the reference square, so everything proved for the
profile transfers: its transform is one squared lobe's read at both signs, each of those is the
reference square's transform at the rescaled frequency, and the whole family is therefore governed
by one tail supremum in the variable `δ w`.

The consequence used downstream is the oscillation bound: the squared profile integrated against a
cosine is at most four times the half-width times that supremum, so it is negligible against the
squared profile's own mass, which is two times the half-width times a positive constant.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open MeasureTheory Filter
open scoped Topology FourierTransform ContDiff

/-- The complexified squared lobe is integrable. -/
theorem integrable_soninOneSidedBump_sqC (m δ : ℝ) (hδ : 0 < δ) :
    Integrable fun x : ℝ => ((soninOneSidedBump m δ x ^ 2 : ℝ) : ℂ) :=
  (integrable_soninOneSidedBump_sq m δ hδ).ofReal

/-- **Centre freedom for the squared lobe.**  Its transform's magnitude is the half-width times the
reference square's magnitude at the rescaled frequency. -/
theorem norm_fourier_soninOneSidedBump_sq (m δ : ℝ) (hδ : 0 < δ) (ξ : ℝ) :
    ‖𝓕 (fun x : ℝ => ((soninOneSidedBump m δ x ^ 2 : ℝ) : ℂ)) ξ‖ =
      δ * ‖𝓕 soninUnitBumpSqC (δ * ξ)‖ :=
  GaloisForLFunctions.HTGeometry.norm_fourierIntegral_comp_div_sub soninUnitBumpSqC m δ hδ ξ

/-- The squared profile's transform is a squared lobe's read at both signs. -/
theorem fourier_soninScaledAnnulusBump_sq_eq_oneSided (m δ : ℝ) (hδ : 0 < δ) (hm : δ < m) (ξ : ℝ) :
    𝓕 (fun x : ℝ => ((soninScaledAnnulusBump m δ x ^ 2 : ℝ) : ℂ)) ξ =
      𝓕 (fun x : ℝ => ((soninOneSidedBump m δ x ^ 2 : ℝ) : ℂ)) ξ +
        𝓕 (fun x : ℝ => ((soninOneSidedBump m δ x ^ 2 : ℝ) : ℂ)) (-ξ) := by
  have hint := integrable_soninOneSidedBump_sqC m δ hδ
  have hrefl : Integrable fun x : ℝ =>
      (fun y : ℝ => ((soninOneSidedBump m δ y ^ 2 : ℝ) : ℂ)) (-x) := hint.comp_neg
  have hsplit : (fun x : ℝ => ((soninScaledAnnulusBump m δ x ^ 2 : ℝ) : ℂ)) =
      fun x : ℝ => ((soninOneSidedBump m δ x ^ 2 : ℝ) : ℂ) +
        (fun y : ℝ => ((soninOneSidedBump m δ y ^ 2 : ℝ) : ℂ)) (-x) := by
    funext x
    rw [soninScaledAnnulusBump_sq m δ hδ hm x]
    push_cast
    ring
  rw [hsplit, GaloisForLFunctions.HTGeometry.fourierIntegral_add hint hrefl ξ]
  congr 1
  exact fourier_comp_neg (fun y : ℝ => ((soninOneSidedBump m δ y ^ 2 : ℝ) : ℂ)) ξ

/-- **The squared profile's spectrum is two reference-square tails.** -/
theorem norm_fourier_soninScaledAnnulusBump_sq_le (m δ : ℝ) (hδ : 0 < δ) (hm : δ < m) (ξ : ℝ) :
    ‖𝓕 (fun x : ℝ => ((soninScaledAnnulusBump m δ x ^ 2 : ℝ) : ℂ)) ξ‖ ≤
      δ * ‖𝓕 soninUnitBumpSqC (δ * ξ)‖ + δ * ‖𝓕 soninUnitBumpSqC (δ * -ξ)‖ := by
  rw [fourier_soninScaledAnnulusBump_sq_eq_oneSided m δ hδ hm ξ]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_fourier_soninOneSidedBump_sq m δ hδ ξ, norm_fourier_soninOneSidedBump_sq m δ hδ (-ξ)]

/-- **The reference square's tail majorant.** -/
def soninRefSqTailSup (u : ℝ) : ℝ :=
  GaloisForLFunctions.HTGeometry.fourierTailSup soninUnitBumpSqC u

theorem norm_fourier_soninUnitBumpSqC_le_tailSup {u v : ℝ} (h : u ≤ |v|) :
    ‖𝓕 soninUnitBumpSqC v‖ ≤ soninRefSqTailSup u :=
  GaloisForLFunctions.HTGeometry.le_fourierTailSup soninUnitBumpSqC h

theorem soninRefSqTailSup_nonneg (u : ℝ) : 0 ≤ soninRefSqTailSup u :=
  GaloisForLFunctions.HTGeometry.fourierTailSup_nonneg soninUnitBumpSqC u

/-- **The reference square's majorant vanishes.** -/
theorem tendsto_soninRefSqTailSup_atTop : Tendsto soninRefSqTailSup atTop (𝓝 0) :=
  tendsto_fourierTailSup_atTop hasCompactSupport_soninUnitBumpSqC contDiff_soninUnitBumpSqC

/-- The complexified squared profile has compact support. -/
theorem hasCompactSupport_soninScaledAnnulusBump_sqC (m δ : ℝ) (hδ : 0 < δ) :
    HasCompactSupport fun x : ℝ => ((soninScaledAnnulusBump m δ x ^ 2 : ℝ) : ℂ) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (hasCompactSupport_soninScaledAnnulusBump m δ hδ) ?_
  intro x hx
  refine subset_tsupport _ ?_
  intro h0
  exact hx (by simp [h0])

/-- **The cosine mass of the squared profile is a reference-square tail.** -/
theorem abs_integral_soninScaledAnnulusBump_sq_mul_cos_le (m δ w : ℝ) (hδ : 0 < δ) (hm : δ < m) :
    |∫ x : ℝ, soninScaledAnnulusBump m δ x ^ 2 * Real.cos (2 * Real.pi * w * x)| ≤
      δ * ‖𝓕 soninUnitBumpSqC (δ * w)‖ + δ * ‖𝓕 soninUnitBumpSqC (δ * -w)‖ +
        (δ * ‖𝓕 soninUnitBumpSqC (δ * -w)‖ + δ * ‖𝓕 soninUnitBumpSqC (δ * -(-w))‖) := by
  have hcontR : Continuous fun x : ℝ => soninScaledAnnulusBump m δ x ^ 2 :=
    (contDiff_soninScaledAnnulusBump m δ hδ).continuous.pow 2
  have hcont : Continuous fun x : ℝ => ((soninScaledAnnulusBump m δ x ^ 2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hcontR
  have hsupp := hasCompactSupport_soninScaledAnnulusBump_sqC m δ hδ
  have havg := integral_mul_cos_eq_fourier_avg hcont hsupp w
  have hsuppR : HasCompactSupport fun x : ℝ => soninScaledAnnulusBump m δ x ^ 2 := by
    refine HasCompactSupport.of_support_subset_isCompact
      (hasCompactSupport_soninScaledAnnulusBump m δ hδ) ?_
    intro x hx
    refine subset_tsupport _ ?_
    intro h0
    exact hx (by simp [h0])
  have hreal : ((∫ x : ℝ, soninScaledAnnulusBump m δ x ^ 2 *
        Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ) =
      ∫ x : ℝ, ((soninScaledAnnulusBump m δ x ^ 2 : ℝ) : ℂ) *
        (Real.cos (2 * Real.pi * w * x) : ℂ) := by
    have hint : Integrable fun x : ℝ =>
        soninScaledAnnulusBump m δ x ^ 2 * Real.cos (2 * Real.pi * w * x) := by
      have hc : Continuous fun x : ℝ =>
          soninScaledAnnulusBump m δ x ^ 2 * Real.cos (2 * Real.pi * w * x) :=
        hcontR.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
      exact hc.integrable_of_hasCompactSupport hsuppR.mul_right
    rw [show ((∫ x : ℝ, soninScaledAnnulusBump m δ x ^ 2 *
          Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ) =
        Complex.ofRealCLM (∫ x : ℝ, soninScaledAnnulusBump m δ x ^ 2 *
          Real.cos (2 * Real.pi * w * x)) from rfl,
      ← Complex.ofRealCLM.integral_comp_comm hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Complex.ofRealCLM (soninScaledAnnulusBump m δ x ^ 2 * Real.cos (2 * Real.pi * w * x)) =
      ((soninScaledAnnulusBump m δ x ^ 2 : ℝ) : ℂ) * ((Real.cos (2 * Real.pi * w * x) : ℝ) : ℂ)
    rw [Complex.ofRealCLM_apply, Complex.ofReal_mul]
  have hnorm : |∫ x : ℝ, soninScaledAnnulusBump m δ x ^ 2 * Real.cos (2 * Real.pi * w * x)| =
      ‖(2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ => ((soninScaledAnnulusBump m δ x ^ 2 : ℝ) : ℂ)) w +
        (2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ => ((soninScaledAnnulusBump m δ x ^ 2 : ℝ) : ℂ)) (-w)‖ := by
    rw [← havg, ← hreal, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖(2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ => ((soninScaledAnnulusBump m δ x ^ 2 : ℝ) : ℂ)) w‖ ≤
      δ * ‖𝓕 soninUnitBumpSqC (δ * w)‖ + δ * ‖𝓕 soninUnitBumpSqC (δ * -w)‖ := by
    rw [norm_mul]
    refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)) ?_
    exact norm_fourier_soninScaledAnnulusBump_sq_le m δ hδ hm w
  have h2 : ‖(2 : ℂ)⁻¹ * 𝓕 (fun x : ℝ => ((soninScaledAnnulusBump m δ x ^ 2 : ℝ) : ℂ)) (-w)‖ ≤
      δ * ‖𝓕 soninUnitBumpSqC (δ * -w)‖ + δ * ‖𝓕 soninUnitBumpSqC (δ * -(-w))‖ := by
    rw [norm_mul]
    refine le_trans (mul_le_of_le_one_left (norm_nonneg _) (by norm_num)) ?_
    exact norm_fourier_soninScaledAnnulusBump_sq_le m δ hδ hm (-w)
  exact add_le_add h1 h2

/-- **The oscillation bound in majorant form.**  Against a cosine of frequency `w`, the squared
profile contributes at most four half-widths times the reference-square majorant at `δ|w|`. -/
theorem abs_integral_soninScaledAnnulusBump_sq_mul_cos_le_tailSup
    (m δ w u : ℝ) (hδ : 0 < δ) (hm : δ < m) (hu : u ≤ δ * |w|) :
    |∫ x : ℝ, soninScaledAnnulusBump m δ x ^ 2 * Real.cos (2 * Real.pi * w * x)| ≤
      4 * δ * soninRefSqTailSup u := by
  have hpos : ‖𝓕 soninUnitBumpSqC (δ * w)‖ ≤ soninRefSqTailSup u := by
    refine norm_fourier_soninUnitBumpSqC_le_tailSup ?_
    rw [abs_mul, abs_of_pos hδ]
    exact hu
  have hneg : ‖𝓕 soninUnitBumpSqC (δ * -w)‖ ≤ soninRefSqTailSup u := by
    refine norm_fourier_soninUnitBumpSqC_le_tailSup ?_
    rw [abs_mul, abs_of_pos hδ, abs_neg]
    exact hu
  have hnegneg : ‖𝓕 soninUnitBumpSqC (δ * -(-w))‖ ≤ soninRefSqTailSup u := by
    refine norm_fourier_soninUnitBumpSqC_le_tailSup ?_
    rw [abs_mul, abs_of_pos hδ, neg_neg]
    exact hu
  have hmain := abs_integral_soninScaledAnnulusBump_sq_mul_cos_le m δ w hδ hm
  nlinarith [hmain, hpos, hneg, hnegneg, hδ, soninRefSqTailSup_nonneg u]

end RHTower
