import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleThirtyTwoSourceBounds

/-!
# A complete-source obstruction to the quartic cross-load

At theta scale thirty-two, the last Gaussian coordinate is negative for the
quartic repair and for its literal weighted source at every critical aperture.
The comparison includes all atoms and the differentiated aperture remainder.
-/

noncomputable section
open Matrix RHTower RHTower.ThetaCuspGaussianLimit
namespace GaloisForLFunctions.ThetaCuspSections.ThirtyTwoCrossObstruction
open ThirtyTwoCrossSource FifthNativeRay FifthRemainder FifthLeadingPair
open EightCrossData EvenFiveEndpoint

/-- The complete source with an arbitrary scalar coefficient of the fixed cross-load. -/
def loadedSource (c : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  nativeShiftedMatrix 5 0 center+c • crossLoad paidSevenSchur

private theorem normalized_loaded (c : ℝ) :
    normalizedGram center (loadedSource c) =
      sourceGram center+(c/sourceUnit center) • loadGram 32 := by
  simp only [loadedSource,sourceGram,normalizedGram_eq_congruence,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,smul_add,smul_smul,
    loadGram,crossLoad,Matrix.conjTranspose_mul,Matrix.mul_assoc,center_scale]
  rw [show (1/sourceUnit center)*c=c/sourceUnit center by ring]

/-- A concrete coordinate excludes every normalized load below the stated threshold. -/
theorem loaded_last_negative {c : ℝ} (hc : c/sourceUnit center ≤ -216*61^2) :
    normalizedGram center (loadedSource c) 4 4 < 0 := by
  have hm := ThirtyTwoCrossData.upper_model_last_negative
  rw [polyModel_eq (by norm_num : (32 : ℝ) ≠ 0)] at hm
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,
    if_pos rfl,mul_one] at hm
  have he := (abs_le.mp source_last_error).2
  have hb : 0 ≤ loadGram 32 4 4 := (loadGram_posSemidef 32).diag_nonneg
  have hl := mul_le_mul_of_nonneg_right hc hb
  rw [normalized_loaded]
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  linarith only [hm,he,hl]

/-- A sufficiently negative coefficient fails semidefiniteness in the original coordinates. -/
theorem loaded_not_posSemidef {c : ℝ} (hc : c/sourceUnit center ≤ -216*61^2) :
    ¬ (loadedSource c).PosSemidef := by
  intro h
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  have hp : (normalizedGram center (loadedSource c)).PosSemidef := by
    rw [normalizedGram_eq_congruence,center_scale]
    exact (h.conjTranspose_mul_mul_same (nativeBasis 32)).smul (by positivity)
  exact (not_lt_of_ge (hp.diag_nonneg (i := 4))) (loaded_last_negative hc)

/-- The quartic profiled complete source is not positive semidefinite at scale thirty-two. -/
theorem repair_not_posSemidef : ¬ (FifthPolynomialCross.repair center).PosSemidef := by
  change ¬ (loadedSource (FifthPolynomialCross.compensation center)).PosSemidef
  exact loaded_not_posSemidef (normalized_compensation_upper.trans (by norm_num))

/-- Every critical positive aperture has the same complete weighted-source obstruction. -/
theorem weightedRepair_not_posSemidef {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    ¬ (FifthPolynomialCross.weightedRepair a (2*center)).PosSemidef := by
  let w := 2*center*Real.sinh (a*(2*center))
  have hw : 0 < w := mul_pos (mul_pos (by norm_num) center_pos)
    (Real.sinh_pos_iff.mpr (mul_pos ha0 (mul_pos (by norm_num) center_pos)))
  have hK := sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)
  have hf := thetaCuspSourceTerm_pos_of_pos_of_nat_pos center_pos (by norm_num : 0 < (1 : ℕ))
  have hq : 7 ≤ thetaCuspSingleAtomReflectionScale 1 center := by rw [center_scale]; norm_num
  have hm := mul_self_le_mul_self hf.le (FifthCrossEnvelope.mass_slope_bounds hq).1
  have hs := FifthCrossEnvelope.first_mass_square center
  rw [center_scale] at hs
  have hd : deriv (FifthPolynomialCross.flux a) (2*center)/w ≤
      -268*thetaCuspFullSource center^2 := by
    apply (div_le_iff₀ hw).mpr
    simpa only [w,mul_comm] using weighted_derivative_upper ha0.le ha
  have hc : (deriv (FifthPolynomialCross.flux a) (2*center)/w)/sourceUnit center ≤ -216*61^2 := by
    apply (div_le_iff₀ hK).mpr
    nlinarith only [hd,hm,hs,hK.le]
  intro h
  have he : (1/w) • FifthPolynomialCross.weightedRepair a (2*center) =
      loadedSource (deriv (FifthPolynomialCross.flux a) (2*center)/w) := by
    ext i j
    simp only [FifthPolynomialCross.weightedRepair,loadedSource,Matrix.add_apply,
      Matrix.smul_apply,smul_eq_mul,show 2*center/2=center by ring]
    change 1/w*(w*nativeShiftedMatrix 5 0 center i j+
      deriv (FifthPolynomialCross.flux a) (2*center)*crossLoad paidSevenSchur i j) = _
    field_simp [hw.ne']
  have hp := h.smul (show 0 ≤ 1/w by positivity)
  rw [he] at hp
  exact loaded_not_posSemidef hc hp

end GaloisForLFunctions.ThetaCuspSections.ThirtyTwoCrossObstruction
