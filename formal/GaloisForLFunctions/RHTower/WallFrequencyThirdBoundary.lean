import GaloisForLFunctions.RHTower.WallFrequencySecondBoundary
import GaloisForLFunctions.RHTower.WallGeneratorThirdJet

/-!
# The third boundary term after multiplication by the frequency

The third integration by parts produces a boundary amplitude with *two* powers of `(1+|x|)^{-1}`.
Multiplying by the frequency spends one of them and leaves one — and one power is square integrable
on a terminal ray.  So unlike the first two boundary terms this one needs no oscillation argument at
all: its pointwise bound already suffices.

That is the precise sense in which the third integration by parts pays for the derivative statement:
it converts the last boundary term from borderline to summable, and simultaneously turns the
remainder's tail from `O(x^{p-2})` into `O(x^{-2})`.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {T : X →L[ℂ] X}

/-- **The third boundary amplitude decays quadratically.** -/
theorem norm_invFamilyProduct2_wallGeneratorShift_le' {σ L μ₀ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀) {t : ℝ} (ht : 1 ≤ |t|)
    (hfloor : μ₀ ≤ wallFloor T σ t + L) :
    ‖invFamilyProduct2 (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) (wallGeneratorD2 X σ) t‖
      ≤ (μ₀⁻¹ * wallAmplitudeConst μ₀) * ((1 + |t|)⁻¹) ^ 2 := by
  have hA := norm_invFamily_wallGeneratorShift_le' (T := T) hσ0 hσ1 hμ hfloor
  have hP := norm_invFamilyProductDeriv_wallGeneratorShift_le' (T := T) hσ0 hσ1 hμ ht hfloor
  have hμ0 : (0 : ℝ) ≤ μ₀⁻¹ := by positivity
  have hC : (0 : ℝ) ≤ wallAmplitudeConst μ₀ := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    rw [wallAmplitudeConst]
    positivity
  have hw : (0 : ℝ) < ((1 + |t|)⁻¹) ^ 2 := by positivity
  refine (norm_mul_le _ _).trans ?_
  calc ‖invFamily (wallGeneratorShift T σ L) t‖
        * ‖invFamilyProductDeriv (wallGeneratorShift T σ L) (wallGeneratorD1 X σ)
            (wallGeneratorD2 X σ) t‖
      ≤ μ₀⁻¹ * (wallAmplitudeConst μ₀ * ((1 + |t|)⁻¹) ^ 2) :=
        mul_le_mul hA hP (norm_nonneg _) hμ0
    _ = (μ₀⁻¹ * wallAmplitudeConst μ₀) * ((1 + |t|)⁻¹) ^ 2 := by ring

/-- The third boundary term of the expansion. -/
def thirdBoundary (T : X →L[ℂ] X) (g : ℝ → X) (m σ x : ℝ) : X :=
  ∫ L in Icc m (m + 1), Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) •
    (invFamilyProduct2 (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) (wallGeneratorD2 X σ) x
      (g L))

/-- **The third boundary term survives multiplication by the frequency.**  Its two powers of
`(1+|x|)^{-1}` leave one after the frequency is spent, and one power is square integrable on a
terminal ray. -/
theorem norm_freq_smul_thirdBoundary_le {σ x m μ₀ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    {g : ℝ → X} (hgint : IntegrableOn g (Icc m (m + 1))) {A : ℝ}
    (hA : (∫ L in Icc m (m + 1), ‖g L‖) ≤ A) (hx : 1 ≤ |x|)
    (hfloor : ∀ L ∈ Icc m (m + 1), μ₀ ≤ wallFloor T σ x + L) :
    ‖x • thirdBoundary T g m σ x‖
      ≤ ((μ₀⁻¹ * wallAmplitudeConst μ₀) * A) * (1 + |x|) ^ (-(1 : ℝ)) := by
  have hC : (0 : ℝ) ≤ wallAmplitudeConst μ₀ := by
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    rw [wallAmplitudeConst]
    positivity
  have hμ0 : (0 : ℝ) ≤ μ₀⁻¹ := by positivity
  have hxpos : (0 : ℝ) < 1 + |x| := by positivity
  have hbound : ∀ L ∈ Icc m (m + 1),
      ‖Complex.exp (-(Complex.I) * (L : ℂ) * (x : ℂ)) •
        (invFamilyProduct2 (wallGeneratorShift T σ L) (wallGeneratorD1 X σ) (wallGeneratorD2 X σ) x
          (g L))‖
      ≤ ((μ₀⁻¹ * wallAmplitudeConst μ₀) * ((1 + |x|)⁻¹) ^ 2) * ‖g L‖ := by
    intro L hL
    rw [norm_smul, norm_expPhase, one_mul]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    exact mul_le_mul_of_nonneg_right
      (norm_invFamilyProduct2_wallGeneratorShift_le' hσ0 hσ1 hμ hx (hfloor L hL)) (norm_nonneg _)
  have hmaj : IntegrableOn
      (fun L : ℝ => ((μ₀⁻¹ * wallAmplitudeConst μ₀) * ((1 + |x|)⁻¹) ^ 2) * ‖g L‖)
      (Icc m (m + 1)) := hgint.norm.const_mul _
  have hle := MeasureTheory.norm_integral_le_of_norm_le hmaj
    (by filter_upwards [ae_restrict_mem measurableSet_Icc] with L hL using hbound L hL)
  rw [integral_const_mul] at hle
  have hstep : ‖x • thirdBoundary T g m σ x‖
      ≤ |x| * (((μ₀⁻¹ * wallAmplitudeConst μ₀) * ((1 + |x|)⁻¹) ^ 2)
        * ∫ L in Icc m (m + 1), ‖g L‖) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hle (abs_nonneg x)
  refine hstep.trans ?_
  rw [Real.rpow_neg_one]
  have hxle : |x| * ((1 + |x|)⁻¹) ^ 2 ≤ (1 + |x|)⁻¹ := by
    have hw : (0 : ℝ) ≤ (1 + |x|)⁻¹ := by positivity
    have h1 : |x| * (1 + |x|)⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ hxpos, one_mul]
      linarith [abs_nonneg x]
    calc |x| * ((1 + |x|)⁻¹) ^ 2 = (|x| * (1 + |x|)⁻¹) * (1 + |x|)⁻¹ := by ring
      _ ≤ 1 * (1 + |x|)⁻¹ := mul_le_mul_of_nonneg_right h1 hw
      _ = (1 + |x|)⁻¹ := one_mul _
  have hAnn : (0 : ℝ) ≤ ∫ L in Icc m (m + 1), ‖g L‖ :=
    setIntegral_nonneg measurableSet_Icc fun L _ => norm_nonneg _
  have hC' : (0 : ℝ) ≤ μ₀⁻¹ * wallAmplitudeConst μ₀ := mul_nonneg hμ0 hC
  calc |x| * (((μ₀⁻¹ * wallAmplitudeConst μ₀) * ((1 + |x|)⁻¹) ^ 2)
        * ∫ L in Icc m (m + 1), ‖g L‖)
      = (|x| * ((1 + |x|)⁻¹) ^ 2)
        * ((μ₀⁻¹ * wallAmplitudeConst μ₀) * ∫ L in Icc m (m + 1), ‖g L‖) := by ring
    _ ≤ (1 + |x|)⁻¹ * ((μ₀⁻¹ * wallAmplitudeConst μ₀) * A) := by
        refine mul_le_mul hxle (mul_le_mul_of_nonneg_left hA hC') (by positivity) (by positivity)
    _ = ((μ₀⁻¹ * wallAmplitudeConst μ₀) * A) * (1 + |x|)⁻¹ := by ring

end GaloisForLFunctions.RHTower
