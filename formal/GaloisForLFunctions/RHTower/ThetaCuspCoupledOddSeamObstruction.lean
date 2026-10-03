import GaloisForLFunctions.RHTower.ThetaCuspCoupledOddSeamSigns
import GaloisForLFunctions.RHTower.ThetaCuspCoupledOddSeamDirection
import GaloisForLFunctions.RHTower.ThetaCuspCoupledOddNeutral
import GaloisForLFunctions.RHTower.ThetaCuspModularEnergyBounds

/-!
# Fixed-direction obstruction and optimal-direction seam reserve

The complete source at the self-dual seam has a strictly negative fourth
coupled determinant at the original direction 168*pi-56. The canonical C3
coefficient is retained exactly. This rejects this correction candidate;
it does not reject the coupled route or assert a conclusion about RH.
-/

namespace RHTower.ThetaCuspCoupledSeamObstruction
noncomputable section
open HTGeometry.ThetaSeamCoupled
open GaloisForLFunctions.HTGeometry

private abbrev X : ℝ := thetaCuspSelfDualModularScale^2
private abbrev M : ℝ := thetaCuspSelfDualThetaMass

private theorem mass_pos : 0 < M := by
  have := thetaCuspSelfDualThetaMass_gt_five_thousand_four_hundred_thirty_one_div_five_thousand
  linarith

private theorem native_moment (k : Fin 7) :
    (-1:ℝ)^(k.val+1)*thetaCuspNativeReflectionJet (2*(k.val+1)) 0 =
      M^2*moment k X := by
  fin_cases k
  · simpa [moment] using thetaCuspNativeEvenMoment_zero_eq_polynomial (1:Fin 7)
  · simpa [moment] using thetaCuspNativeEvenMoment_zero_eq_polynomial (2:Fin 7)
  · simpa [moment] using thetaCuspNativeEvenMoment_zero_eq_polynomial (3:Fin 7)
  · simpa [moment] using thetaCuspNativeEvenMoment_zero_eq_polynomial (4:Fin 7)
  · simpa [moment] using thetaCuspNativeEvenMoment_zero_eq_polynomial (5:Fin 7)
  · simpa [moment] using thetaCuspNativeEvenMoment_zero_eq_polynomial (6:Fin 7)
  · norm_num [moment]
    exact ThetaCuspCoupledSeam.native_fourteen

private theorem native_head_eq : thetaCuspNativeOddHeadDet 0=M^4*headTwo X := by
  have h0 := native_moment 0
  have h1 := native_moment 1
  have h2 := native_moment 2
  norm_num at h0 h1 h2
  unfold thetaCuspNativeOddHeadDet
  rw [h0,h1,h2]
  unfold headTwo
  ring

private theorem native_three_eq : thetaCuspNativeOddHankelThreeDet 0=M^6*detThree X := by
  have h0 := native_moment 0
  have h1 := native_moment 1
  have h2 := native_moment 2
  have h3 := native_moment 3
  have h4 := native_moment 4
  norm_num at h0 h1 h2 h3 h4
  unfold thetaCuspNativeOddHankelThreeDet HilbertMetric.signedEvenHankelThreeDet
  rw [h0,h1,h2,h3,h4]
  unfold detThree
  ring

private def G : ℝ := 3*sourceSquare X

private theorem source_correction_zero : thetaCuspCenterCompensationSource 0=M^2*G := by
  unfold thetaCuspCenterCompensationSource
  rw [thetaCuspFullSource_zero_eq_modularScale]
  unfold G sourceSquare
  ring


private def normalizedFourth : ℝ :=
  hankelFourDet (moment 0 X) (moment 1 X) (moment 2 X) (moment 3 X)
    (moment 4 X) (moment 5 X) (moment 6 X)

private def normalizedBorder : ℝ :=
  -(moment 0 X*moment 2 X*moment 5 X-moment 0 X*moment 3 X*moment 4 X-
    (moment 1 X)^2*moment 5 X+moment 1 X*moment 2 X*moment 4 X+
    moment 1 X*(moment 3 X)^2-(moment 2 X)^2*moment 3 X)

private theorem sourceMoment_eq (k : Fin 7) :
    ThetaCuspCoupledSeamDirection.sourceMoment k=M^2*moment k X := native_moment k

private theorem nativeFourth_eq : ThetaCuspCoupledSeamDirection.nativeFourth=M^8*normalizedFourth := by
  unfold ThetaCuspCoupledSeamDirection.nativeFourth normalizedFourth
  simp only [sourceMoment_eq]
  unfold hankelFourDet
  ring

private theorem border_eq : ThetaCuspCoupledSeamDirection.borderCofactor=M^6*normalizedBorder := by
  unfold ThetaCuspCoupledSeamDirection.borderCofactor normalizedBorder
  simp only [sourceMoment_eq]
  ring

private theorem cleared_actual :
    thetaCuspNativeOddHeadDet 0*
      (ThetaCuspCoupledSeamDirection.seamMatrix 10000000000000 (168*Real.pi-56)).det=
        M^12*canonicalCleared X Real.pi := by
  rw [ThetaCuspCoupledSeamDirection.determinant_direction_square]
  change -2*thetaCuspNativeOddHeadDet 0*
      (ThetaCuspCoupledSeamDirection.nativeFourth+
        10000000000000*thetaCuspCenterCompensationSource 0*thetaCuspNativeOddHankelThreeDet 0)-
      3*(thetaCuspNativeOddHankelThreeDet 0*(168*Real.pi-56)+
        ThetaCuspCoupledSeamDirection.borderCofactor)^2=M^12*canonicalCleared X Real.pi
  rw [native_head_eq,native_three_eq,source_correction_zero,nativeFourth_eq,border_eq]
  unfold canonicalCleared normalizedFourth normalizedBorder G sourceSquare
    detThree headTwo hankelFourDet
  ring

/-- The original moving direction with C4=10^13 fails at the literal self-dual source. -/
theorem actual_seam_determinant_neg :
    (ThetaCuspCoupledSeamDirection.seamMatrix 10000000000000 (168*Real.pi-56)).det < 0 := by
  have hc : canonicalCleared X Real.pi < 0 := canonical_neg_of_box
    thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.le
    thetaCuspSelfDualModularScale_sq_lt_ninetySix_fifths.le
    (by have := Real.pi_gt_d4; linarith) (by have := Real.pi_lt_d2; linarith)
  have hp := mul_neg_of_pos_of_neg (pow_pos mass_pos 12) hc
  rw [← cleared_actual] at hp
  by_contra hn
  exact (not_le_of_gt hp) (mul_nonneg (thetaCuspNativeOddHeadDet_pos 0).le (le_of_not_gt hn))

private theorem cleared_optimal_actual :
    -2*thetaCuspNativeOddHeadDet 0*(ThetaCuspCoupledSeamDirection.nativeFourth+
      10000000000000*thetaCuspCenterCompensationSource 0*thetaCuspNativeOddHankelThreeDet 0)=
        M^12*optimalHom X 1 := by
  rw [native_head_eq,native_three_eq,source_correction_zero,nativeFourth_eq,optimalHom_one]
  unfold G sourceSquare normalizedFourth
  ring

/-- The same final load has a strictly positive literal determinant at the optimal direction. -/
theorem actual_optimal_seam_determinant_pos :
    0 < (ThetaCuspCoupledSeamDirection.seamMatrix 10000000000000
      ThetaCuspCoupledSeamDirection.optimalDirection).det := by
  apply (ThetaCuspCoupledSeamDirection.optimal_determinant_pos_iff 10000000000000).mpr
  change ThetaCuspCoupledSeamDirection.nativeFourth+
    10000000000000*thetaCuspCenterCompensationSource 0*thetaCuspNativeOddHankelThreeDet 0 < 0
  have hmod := optimal_pos_of_box thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one.le
    thetaCuspSelfDualModularScale_sq_lt_ninetySix_fifths.le
  have hp := mul_pos (pow_pos mass_pos 12) hmod
  rw [← cleared_optimal_actual] at hp
  by_contra hn
  have hh := mul_nonneg (thetaCuspNativeOddHeadDet_pos 0).le (le_of_not_gt hn)
  nlinarith only [hp,hh]

/-- The optimal source direction repairs the entire fourth odd seam form at the same load. -/
theorem actual_optimal_seam_posDef :
    (ThetaCuspCoupledSeamDirection.seamMatrix 10000000000000
      ThetaCuspCoupledSeamDirection.optimalDirection).PosDef :=
  ThetaCuspCoupledSeamDirection.posDef_of_determinant_pos _ _ actual_optimal_seam_determinant_pos

open ThetaCuspCoupledOddNeutral
open ThetaCuspCoupledSeamDirection
open scoped Matrix

private theorem energy_eq (C : ℝ) (c : Fin 4 → ℝ) :
    coupledOddFourEnergy C 0 c =
      dotProduct (star c) (Matrix.mulVec (seamMatrix C (168*Real.pi-56)) c) := by
  unfold coupledOddFourEnergy
  dsimp [seamMatrix]
  norm_num [ThetaCuspCoupledSeamDirection.sourceMoment,thetaCuspSingleAtomReflectionScale,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ,
    show Fin.succ (2 : Fin 3)=(3 : Fin 4) from rfl]
  ring

private theorem seamMatrix_hermitian (C t : ℝ) : (seamMatrix C t).IsHermitian := by
  change (seamMatrix C t).conjTranspose=seamMatrix C t
  ext i j
  fin_cases i <;> fin_cases j <;> simp [seamMatrix,Matrix.conjTranspose]

/-- Actual C4=10^13 candidate fails, with a strictly negative native coefficient vector. -/
theorem exists_coupledOddFourEnergy_seam_neg :
    ∃ c : Fin 4 → ℝ, c ≠ 0 ∧ coupledOddFourEnergy 10000000000000 0 c < 0 := by
  classical
  by_contra hn
  push Not at hn
  have hs : (seamMatrix 10000000000000 (168*Real.pi-56)).PosSemidef := by
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨seamMatrix_hermitian _ _,?_⟩
    intro c
    rw [← energy_eq]
    by_cases hc : c=0
    · subst c
      simp [coupledOddFourEnergy]
    · exact hn c hc
  exact (not_le_of_gt actual_seam_determinant_neg) hs.det_nonneg


/-- One literal source vector rejects every load in the proved adverse-ray coefficient range. -/
theorem exists_common_negative_vector_below_load :
    ∃ c : Fin 4 → ℝ, c ≠ 0 ∧ ∀ C : ℝ, C ≤ 10000000000000 →
      coupledOddFourEnergy C 0 c < 0 := by
  obtain ⟨c,hc,he⟩ := exists_coupledOddFourEnergy_seam_neg
  refine ⟨c,hc,?_⟩
  intro C hC
  have hG : 0 ≤ thetaCuspCenterCompensationSource 0 := by
    unfold thetaCuspCenterCompensationSource
    simp only [mul_zero,zero_mul,add_zero]
    positivity
  have hn := mul_nonneg (sub_nonneg.mpr hC) (mul_nonneg hG (sq_nonneg (c 3)))
  have hi : coupledOddFourEnergy 10000000000000 0 c-coupledOddFourEnergy C 0 c =
      (10000000000000-C)*(thetaCuspCenterCompensationSource 0*(c 3)^2) := by
    unfold coupledOddFourEnergy
    ring
  linarith only [he,hn,hi]

end
end RHTower.ThetaCuspCoupledSeamObstruction
