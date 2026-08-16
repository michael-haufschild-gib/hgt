import GaloisForLFunctions.RHTower.WallBlockResolventRegularity
import GaloisForLFunctions.RHTower.WallEvenAmplitudeBounds

/-!
# The block amplitudes differentiated in the position

The shifted generator `C(x,L) = B(x) + L` moves at unit speed in the position, so the block
resolvent's position derivative is minus its square and the second boundary amplitude's is a sum of
three products, each with one more resolvent power than the amplitude itself.

That extra power is what makes the position integration by parts pay for multiplication by the
frequency: `∂_L e^{-iLx} = -ix e^{-iLx}`, so moving the derivative onto the amplitude and the block
profile trades a factor of `x` for either a further resolvent power or the profile's own derivative
— and both keep the frequency decay `(1+|x|)^{-1}` that the amplitude already has.
-/

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

variable {T : X →L[ℂ] X}

/-- **The shifted generator moves at unit speed in the position.** -/
theorem hasDerivAt_wallGeneratorShift_position (T : X →L[ℂ] X) (σ x : ℝ) (L : ℝ) :
    HasDerivAt (fun M : ℝ => wallGeneratorShift T σ M x) (ContinuousLinearMap.id ℂ X) L := by
  have hofReal : HasDerivAt (fun M : ℝ => (M : ℂ)) 1 L := Complex.ofRealCLM.hasDerivAt
  have hsmul : HasDerivAt (fun M : ℝ => (M : ℂ) • (ContinuousLinearMap.id ℂ X))
      ((1 : ℂ) • (ContinuousLinearMap.id ℂ X)) L := hofReal.smul_const _
  have h : HasDerivAt (fun M : ℝ => wallGenerator T σ x + (M : ℂ) • ContinuousLinearMap.id ℂ X)
      ((1 : ℂ) • (ContinuousLinearMap.id ℂ X)) L := hsmul.const_add _
  refine h.congr_deriv ?_
  rw [one_smul]

/-- The position derivative of the block resolvent. -/
def wallResolventPosDeriv (T : X →L[ℂ] X) (σ x L : ℝ) : X →L[ℂ] X :=
  invFamilyDeriv (fun M : ℝ => wallGeneratorShift T σ M x)
    (fun _ : ℝ => ContinuousLinearMap.id ℂ X) L

/-- **The block resolvent's position derivative is minus its square.** -/
theorem hasDerivAt_invFamily_position {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {x L : ℝ}
    (hgap : 0 < wallFloor T σ x + L) :
    HasDerivAt (fun M : ℝ => invFamily (wallGeneratorShift T σ M) x)
      (wallResolventPosDeriv T σ x L) L := by
  have hunit : IsUnit (wallGeneratorShift T σ L x) := isUnit_wallGeneratorShift hσ0 hσ1 hgap
  have hbase := hasDerivAt_invFamily
    (C := fun M : ℝ => wallGeneratorShift T σ M x)
    (C₁ := fun _ : ℝ => ContinuousLinearMap.id ℂ X)
    (hasDerivAt_wallGeneratorShift_position T σ x L) hunit
  exact hbase

/-- The position derivative of the resolvent is bounded by the square of the floor's inverse. -/
theorem norm_wallResolventPosDeriv_le {σ L μ₀ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ₀)
    {x : ℝ} (hfloor : μ₀ ≤ wallFloor T σ x + L) :
    ‖wallResolventPosDeriv T σ x L‖ ≤ (μ₀⁻¹) ^ 2 := by
  have hA : ‖invFamily (fun M : ℝ => wallGeneratorShift T σ M x) L‖ ≤ μ₀⁻¹ :=
    norm_invFamily_wallGeneratorShift_le' (T := T) hσ0 hσ1 hμ hfloor
  have hid : ‖(ContinuousLinearMap.id ℂ X)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hbase := norm_invFamilyDeriv_le (fun M : ℝ => wallGeneratorShift T σ M x)
    (fun _ : ℝ => ContinuousLinearMap.id ℂ X) L
  refine (le_of_eq rfl).trans (hbase.trans ?_)
  have hAnn : (0 : ℝ) ≤ ‖invFamily (fun M : ℝ => wallGeneratorShift T σ M x) L‖ := norm_nonneg _
  have hμ0 : (0 : ℝ) ≤ μ₀⁻¹ := by positivity
  nlinarith [hA, hAnn, hid, norm_nonneg (ContinuousLinearMap.id ℂ X)]

/-- The position derivative of the second boundary amplitude. -/
def wallSecondAmplitudePosDeriv (T : X →L[ℂ] X) (σ x L : ℝ) : X →L[ℂ] X :=
  -(wallResolventPosDeriv T σ x L * invFamily (wallGeneratorShift T σ L) x
      * wallGeneratorD1 X σ x * invFamily (wallGeneratorShift T σ L) x)
    - (invFamily (wallGeneratorShift T σ L) x * wallResolventPosDeriv T σ x L
      * wallGeneratorD1 X σ x * invFamily (wallGeneratorShift T σ L) x)
    - (invFamily (wallGeneratorShift T σ L) x * invFamily (wallGeneratorShift T σ L) x
      * wallGeneratorD1 X σ x * wallResolventPosDeriv T σ x L)

/-- **The second boundary amplitude is differentiable in the position.** -/
theorem hasDerivAt_wallSecondAmplitude_position {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {x L : ℝ}
    (hgap : 0 < wallFloor T σ x + L) :
    HasDerivAt (fun M : ℝ => invFamilyProduct (wallGeneratorShift T σ M) (wallGeneratorD1 X σ) x)
      (wallSecondAmplitudePosDeriv T σ x L) L := by
  have hA : HasDerivAt (fun M : ℝ => invFamily (wallGeneratorShift T σ M) x)
      (wallResolventPosDeriv T σ x L) L := hasDerivAt_invFamily_position hσ0 hσ1 hgap
  have hinner : HasDerivAt
      (fun M : ℝ => invFamily (wallGeneratorShift T σ M) x * wallGeneratorD1 X σ x
        * invFamily (wallGeneratorShift T σ M) x)
      ((wallResolventPosDeriv T σ x L * wallGeneratorD1 X σ x)
          * invFamily (wallGeneratorShift T σ L) x
        + (invFamily (wallGeneratorShift T σ L) x * wallGeneratorD1 X σ x)
          * wallResolventPosDeriv T σ x L) L :=
    (hA.mul_const (wallGeneratorD1 X σ x)).mul hA
  have h := hA.mul hinner.neg
  refine h.congr_deriv ?_
  rw [wallSecondAmplitudePosDeriv]
  simp only [Pi.neg_apply]
  noncomm_ring

omit [CompleteSpace X] in
/-- The quadruple product bound. -/
theorem norm_mul₄_le (a b c d : X →L[ℂ] X) : ‖a * b * c * d‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ := by
  refine (norm_mul_le _ _).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine (norm_mul_le _ _).trans ?_
  exact mul_le_mul_of_nonneg_right (norm_mul_le a b) (norm_nonneg _)

/-- **The position derivative of the second boundary amplitude keeps the frequency decay.** -/
theorem norm_wallSecondAmplitudePosDeriv_le {σ L μ₀ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hμ : 0 < μ₀) {x : ℝ} (hx : 1 ≤ |x|) (hfloor : μ₀ ≤ wallFloor T σ x + L) :
    ‖wallSecondAmplitudePosDeriv T σ x L‖
      ≤ (3 * (μ₀⁻¹) ^ 4 * (3 + Real.pi)) * (1 + |x|)⁻¹ := by
  have hA : ‖invFamily (wallGeneratorShift T σ L) x‖ ≤ μ₀⁻¹ :=
    norm_invFamily_wallGeneratorShift_le' hσ0 hσ1 hμ hfloor
  have hD : ‖wallResolventPosDeriv T σ x L‖ ≤ (μ₀⁻¹) ^ 2 :=
    norm_wallResolventPosDeriv_le hσ0 hσ1 hμ hfloor
  have hK : ‖wallGeneratorD1 X σ x‖ ≤ (3 + Real.pi) * (1 + |x|)⁻¹ :=
    norm_wallGeneratorShiftD1_le' hσ0 hσ1 hx
  have hμ0 : (0 : ℝ) ≤ μ₀⁻¹ := by positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hw : (0 : ℝ) < (1 + |x|)⁻¹ := by positivity
  have t1 : ‖wallResolventPosDeriv T σ x L * invFamily (wallGeneratorShift T σ L) x
      * wallGeneratorD1 X σ x * invFamily (wallGeneratorShift T σ L) x‖
      ≤ (μ₀⁻¹) ^ 2 * μ₀⁻¹ * ((3 + Real.pi) * (1 + |x|)⁻¹) * μ₀⁻¹ := by
    refine (norm_mul₄_le _ _ _ _).trans ?_
    gcongr
  have t2 : ‖invFamily (wallGeneratorShift T σ L) x * wallResolventPosDeriv T σ x L
      * wallGeneratorD1 X σ x * invFamily (wallGeneratorShift T σ L) x‖
      ≤ μ₀⁻¹ * (μ₀⁻¹) ^ 2 * ((3 + Real.pi) * (1 + |x|)⁻¹) * μ₀⁻¹ := by
    refine (norm_mul₄_le _ _ _ _).trans ?_
    gcongr
  have t3 : ‖invFamily (wallGeneratorShift T σ L) x * invFamily (wallGeneratorShift T σ L) x
      * wallGeneratorD1 X σ x * wallResolventPosDeriv T σ x L‖
      ≤ μ₀⁻¹ * μ₀⁻¹ * ((3 + Real.pi) * (1 + |x|)⁻¹) * (μ₀⁻¹) ^ 2 := by
    refine (norm_mul₄_le _ _ _ _).trans ?_
    gcongr
  have t1' : ‖-(wallResolventPosDeriv T σ x L * invFamily (wallGeneratorShift T σ L) x
      * wallGeneratorD1 X σ x * invFamily (wallGeneratorShift T σ L) x)‖
      ≤ (μ₀⁻¹) ^ 2 * μ₀⁻¹ * ((3 + Real.pi) * (1 + |x|)⁻¹) * μ₀⁻¹ := by
    rw [norm_neg]
    exact t1
  rw [wallSecondAmplitudePosDeriv]
  refine le_trans (norm_sub_le _ _) ?_
  refine le_trans (add_le_add (le_trans (norm_sub_le _ _) (add_le_add t1' t2)) t3) ?_
  nlinarith [hμ0, hw.le]

end GaloisForLFunctions.RHTower
