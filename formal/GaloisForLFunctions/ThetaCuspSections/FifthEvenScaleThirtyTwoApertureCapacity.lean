import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleThirtyTwoCapacity

/-!
# Aperture dependence of the quartic scaling capacity

At scale thirty-two the literal differentiated coefficient is a positive
fraction of the negative aperture-independent coefficient. The admissible
scalar load therefore ends at the base capacity divided by that fraction.
Every critical aperture shares the base positive-load interval.
-/

noncomputable section
open Matrix RHTower RHTower.ThetaCuspGaussianLimit
namespace GaloisForLFunctions.ThetaCuspSections.ThirtyTwoApertureCapacity
open ThirtyTwoCrossSource ThirtyTwoCrossObstruction EvenFiveEndpoint

/-- Physical weight at the fixed center. -/
def weight (a : ℝ) : ℝ := 2*center*Real.sinh (a*(2*center))

/-- Literal differentiated coefficient relative to the aperture-independent coefficient. -/
def fraction (a : ℝ) : ℝ :=
  (deriv (FifthPolynomialCross.flux a) (2*center)/weight a)/
    FifthPolynomialCross.compensation center

/-- The literal weighted source with a scalar multiple of its flux correction. -/
def scaledSource (a t : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  weight a • nativeShiftedMatrix 5 0 center+
    (t*deriv (FifthPolynomialCross.flux a) (2*center)) • crossLoad paidSevenSchur

/-- Exact aperture-dependent scalar capacity. -/
def capacity (a : ℝ) : ℝ := ThirtyTwoCrossCapacity.capacity/fraction a

private theorem weight_pos {a : ℝ} (ha : 0 < a) : 0 < weight a :=
  mul_pos (mul_pos (by norm_num) center_pos)
    (Real.sinh_pos_iff.mpr (mul_pos ha (mul_pos (by norm_num) center_pos)))

private theorem compensation_negative : FifthPolynomialCross.compensation center < 0 :=
  profile_compensation_upper.trans_lt
    (mul_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos (thetaCuspFullSource_pos_all center)))

/-- The aperture correction reduces the magnitude of the negative base coefficient. -/
theorem fraction_bounds {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    0 < fraction a ∧ fraction a ≤ 1 := by
  have hw := weight_pos ha0
  have hG := compensation_negative
  have hd : deriv (FifthPolynomialCross.flux a) (2*center)/weight a < 0 := by
    have h := weighted_derivative_upper ha0.le ha
    have hn : weight a*(-268*thetaCuspFullSource center^2) < 0 :=
      mul_neg_of_pos_of_neg hw
        (mul_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos (thetaCuspFullSource_pos_all center)))
    exact div_neg_of_neg_of_pos (h.trans_lt hn) hw
  have hl : FifthPolynomialCross.compensation center ≤
      deriv (FifthPolynomialCross.flux a) (2*center)/weight a := by
    apply (le_div_iff₀ hw).mpr
    have h := FifthPolynomialCross.deriv_flux_lower ha0.le
      (show 0 ≤ 2*center from mul_nonneg (by norm_num) center_pos.le)
    rw [show 2*center/2=center by ring] at h
    simpa only [weight,mul_comm] using h
  have he : fraction a*FifthPolynomialCross.compensation center=
      deriv (FifthPolynomialCross.flux a) (2*center)/weight a := by
    unfold fraction
    field_simp [hG.ne]
  constructor
  · unfold fraction
    exact div_pos_of_neg_of_neg hd hG
  · by_contra h
    have hn := mul_neg_of_pos_of_neg (sub_pos.mpr (lt_of_not_ge h)) hG
    nlinarith only [hn,he,hl]

private theorem source_eq {a : ℝ} (ha : 0 < a) (t : ℝ) :
    scaledSource a t=weight a • ThirtyTwoCrossCapacity.scaledSource (t*fraction a) := by
  have hw := weight_pos ha
  have hG := compensation_negative
  ext i j
  simp only [scaledSource,ThirtyTwoCrossCapacity.scaledSource,loadedSource,fraction,
    Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  field_simp [hw.ne',hG.ne]

/-- The exact aperture capacity determines strict positivity at every scalar load. -/
theorem posDef_iff {a t : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    (scaledSource a t).PosDef ↔ t < capacity a := by
  have hw := weight_pos ha0
  have hα := (fraction_bounds ha0 ha).1
  have hi : (1/weight a)*weight a=1 := by field_simp [hw.ne']
  rw [source_eq ha0]
  have hp : (weight a • ThirtyTwoCrossCapacity.scaledSource (t*fraction a)).PosDef ↔
      (ThirtyTwoCrossCapacity.scaledSource (t*fraction a)).PosDef := by
    constructor
    · intro h
      have hs := h.smul (show 0 < 1/weight a by positivity)
      simpa only [smul_smul,hi,one_smul] using hs
    · exact fun h => h.smul hw
  rw [hp,ThirtyTwoCrossCapacity.posDef_iff]
  exact (lt_div_iff₀ hα).symm

/-- Semidefiniteness includes exactly the aperture-dependent capacity endpoint. -/
theorem posSemidef_iff {a t : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    (scaledSource a t).PosSemidef ↔ t ≤ capacity a := by
  have hw := weight_pos ha0
  have hα := (fraction_bounds ha0 ha).1
  have hi : (1/weight a)*weight a=1 := by field_simp [hw.ne']
  rw [source_eq ha0]
  have hp : (weight a • ThirtyTwoCrossCapacity.scaledSource (t*fraction a)).PosSemidef ↔
      (ThirtyTwoCrossCapacity.scaledSource (t*fraction a)).PosSemidef := by
    constructor
    · intro h
      have hs := h.smul (show 0 ≤ 1/weight a by positivity)
      simpa only [smul_smul,hi,one_smul] using hs
    · exact fun h => h.smul hw.le
  rw [hp,ThirtyTwoCrossCapacity.posSemidef_iff]
  exact (le_div_iff₀ hα).symm

/-- Every critical aperture admits the base load interval and rejects the unit load. -/
theorem capacity_bounds {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    0 < ThirtyTwoCrossCapacity.capacity ∧
      ThirtyTwoCrossCapacity.capacity ≤ capacity a ∧ capacity a < 1 := by
  have hc := ThirtyTwoCrossCapacity.capacity_bounds.1
  have hα := fraction_bounds ha0 ha
  refine ⟨hc,?_,?_⟩
  · apply (le_div_iff₀ hα.1).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hα.2 hc.le
  · apply lt_of_not_ge
    intro h
    have hp := (posSemidef_iff ha0 ha).mpr h
    have he : scaledSource a 1=FifthPolynomialCross.weightedRepair a (2*center) := by
      simp only [scaledSource,FifthPolynomialCross.weightedRepair,weight,one_mul,
        show 2*center/2=center by ring]
    rw [he] at hp
    exact weightedRepair_not_posSemidef ha0 ha hp

/-- The exact aperture endpoint is positive semidefinite and singular. -/
theorem boundary {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    (scaledSource a (capacity a)).PosSemidef ∧ (scaledSource a (capacity a)).det=0 := by
  have hp := (posSemidef_iff ha0 ha).mpr le_rfl
  refine ⟨hp,?_⟩
  by_contra hn
  have hd := hp.posDef_iff_det_ne_zero.mpr hn
  exact (not_lt_of_ge le_rfl) ((posDef_iff ha0 ha).mp hd)

/-- One explicit load bound excludes every critical aperture simultaneously. -/
theorem capacity_upper {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) : capacity a < 54/67 := by
  have hw := weight_pos ha0
  have hG := compensation_negative
  have hα := (fraction_bounds ha0 ha).1
  have he : fraction a*FifthPolynomialCross.compensation center=
      deriv (FifthPolynomialCross.flux a) (2*center)/weight a := by
    unfold fraction
    field_simp [hG.ne]
  have hn : ¬ (ThirtyTwoCrossCapacity.scaledSource ((54/67)*fraction a)).PosSemidef := by
    apply loaded_not_posSemidef
    have h := mul_le_mul_of_nonneg_left (normalized_weighted_derivative_upper ha0 ha)
      (by norm_num : (0 : ℝ) ≤ 54/67)
    change (54/67)*((deriv (FifthPolynomialCross.flux a) (2*center)/weight a)/
      FifthRemainder.sourceUnit center) ≤ (54/67)*(-268*61^2) at h
    change (((54/67)*fraction a)*FifthPolynomialCross.compensation center)/
      FifthRemainder.sourceUnit center ≤ _
    calc
      _ = (54/67)*((deriv (FifthPolynomialCross.flux a) (2*center)/weight a)/
          FifthRemainder.sourceUnit center) := by
        rw [show ((54/67)*fraction a)*FifthPolynomialCross.compensation center=
          (54/67)*(fraction a*FifthPolynomialCross.compensation center) by ring,he]
        ring
      _ ≤ -216*61^2 := by nlinarith only [h]
  by_contra h
  have ht : (54/67)*fraction a ≤ ThirtyTwoCrossCapacity.capacity :=
    (le_div_iff₀ hα).mp (le_of_not_gt h)
  exact hn (ThirtyTwoCrossCapacity.posSemidef_iff.mpr ht)

end GaloisForLFunctions.ThetaCuspSections.ThirtyTwoApertureCapacity
