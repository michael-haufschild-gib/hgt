import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleSixCapacity

/-!
# Aperture dependence of the quartic scaling capacity

At scale six the literal differentiated coefficient is a positive
fraction of the negative aperture-independent coefficient. The admissible
scalar load therefore ends at the base capacity divided by that fraction.
Every critical aperture shares the base positive-load interval.
-/

noncomputable section
open Matrix RHTower RHTower.ThetaCuspGaussianLimit
namespace GaloisForLFunctions.ThetaCuspSections.SixApertureCapacity
open SixSourceBounds FifthNativeRay FifthRemainder EvenFiveEndpoint

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
def capacity (a : ℝ) : ℝ := SixCrossCapacity.capacity/fraction a

private theorem weight_pos {a : ℝ} (ha : 0 < a) : 0 < weight a :=
  mul_pos (mul_pos (by norm_num) center_pos)
    (Real.sinh_pos_iff.mpr (mul_pos ha (mul_pos (by norm_num) center_pos)))

/-- The aperture correction reduces the magnitude of the negative base coefficient. -/
theorem fraction_bounds {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    0 < fraction a ∧ fraction a ≤ 1 := by
  have hw := weight_pos ha0
  have hG := compensation_negative
  have hd : deriv (FifthPolynomialCross.flux a) (2*center)/weight a < 0 := by
    have h := weighted_derivative_upper ha0.le ha
    have hn : weight a*(-120*sourceUnit center) < 0 :=
      mul_neg_of_pos_of_neg hw
        (mul_neg_of_neg_of_pos (by norm_num) (sourceUnit_pos (x := center) (by rw [center_scale]; norm_num)))
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

/-- Every critical aperture retains at least twenty twenty-firsts of the base coefficient. -/
theorem fraction_lower {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) : 20/21 ≤ fraction a := by
  have hw := weight_pos ha0
  have hG := compensation_negative
  have hd : deriv (FifthPolynomialCross.flux a) (2*center)/weight a ≤
      (20/21)*FifthPolynomialCross.compensation center := by
    have hu : deriv (FifthPolynomialCross.flux a) (2*center)/weight a ≤
        -120*sourceUnit center := by
      apply (div_le_iff₀ hw).mpr
      simpa only [weight,mul_comm] using weighted_derivative_upper ha0.le ha
    have hl := FifthPolynomialCross.compensation_six_lower center_scale
    nlinarith only [hu,hl]
  have he : fraction a*FifthPolynomialCross.compensation center=
      deriv (FifthPolynomialCross.flux a) (2*center)/weight a := by
    unfold fraction
    field_simp [hG.ne]
  by_contra h
  have hn := mul_neg_of_pos_of_neg (sub_pos.mpr (lt_of_not_ge h)) hG
  nlinarith only [hn,he,hd]

private theorem source_eq {a : ℝ} (ha : 0 < a) (t : ℝ) :
    scaledSource a t=weight a • SixSourceBounds.scaledSource (t*fraction a) := by
  have hw := weight_pos ha
  have hG := compensation_negative
  ext i j
  simp only [scaledSource,SixSourceBounds.scaledSource,fraction,
    Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  field_simp [hw.ne',hG.ne]

/-- The exact aperture capacity determines strict positivity at every scalar load. -/
theorem posDef_iff {a t : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    (scaledSource a t).PosDef ↔ t < capacity a := by
  have hw := weight_pos ha0
  have hα := (fraction_bounds ha0 ha).1
  have hi : (1/weight a)*weight a=1 := by field_simp [hw.ne']
  rw [source_eq ha0]
  have hp : (weight a • SixSourceBounds.scaledSource (t*fraction a)).PosDef ↔
      (SixSourceBounds.scaledSource (t*fraction a)).PosDef := by
    constructor
    · intro h
      have hs := h.smul (show 0 < 1/weight a by positivity)
      simpa only [smul_smul,hi,one_smul] using hs
    · exact fun h => h.smul hw
  rw [hp,SixCrossCapacity.source_posDef_iff]
  exact (lt_div_iff₀ hα).symm

/-- Semidefiniteness includes exactly the aperture-dependent capacity endpoint. -/
theorem posSemidef_iff {a t : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    (scaledSource a t).PosSemidef ↔ t ≤ capacity a := by
  have hw := weight_pos ha0
  have hα := (fraction_bounds ha0 ha).1
  have hi : (1/weight a)*weight a=1 := by field_simp [hw.ne']
  rw [source_eq ha0]
  have hp : (weight a • SixSourceBounds.scaledSource (t*fraction a)).PosSemidef ↔
      (SixSourceBounds.scaledSource (t*fraction a)).PosSemidef := by
    constructor
    · intro h
      have hs := h.smul (show 0 ≤ 1/weight a by positivity)
      simpa only [smul_smul,hi,one_smul] using hs
    · exact fun h => h.smul hw.le
  rw [hp,SixCrossCapacity.source_posSemidef_iff]
  exact (le_div_iff₀ hα).symm

/-- Every critical aperture admits the base load interval and rejects the unit load. -/
theorem capacity_bounds {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    0 < SixCrossCapacity.capacity ∧
      SixCrossCapacity.capacity ≤ capacity a ∧ capacity a < 1 := by
  have hc := SixCrossCapacity.capacity_bounds.1
  have hα := fraction_bounds ha0 ha
  refine ⟨hc,?_,?_⟩
  · apply (le_div_iff₀ hα.1).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hα.2 hc.le
  · apply (div_lt_one hα.1).mpr
    exact SixCrossCapacity.capacity_strict_upper.trans_le
      ((by norm_num : (1000/1251 : ℝ) ≤ 20/21).trans (fraction_lower ha0 ha))

/-- The exact aperture endpoint is positive semidefinite and singular. -/
theorem boundary {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    (scaledSource a (capacity a)).PosSemidef ∧ (scaledSource a (capacity a)).det=0 := by
  have hp := (posSemidef_iff ha0 ha).mpr le_rfl
  refine ⟨hp,?_⟩
  by_contra hn
  have hd := hp.posDef_iff_det_ne_zero.mpr hn
  exact (not_lt_of_ge le_rfl) ((posDef_iff ha0 ha).mp hd)

/-- Aperture dependence increases the exact capacity by at most the factor twenty-one over twenty. -/
theorem capacity_gain_bound {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    capacity a ≤ (21/20)*SixCrossCapacity.capacity := by
  have hc := SixCrossCapacity.capacity_bounds.1
  have hα := (fraction_bounds ha0 ha).1
  apply (div_le_iff₀ hα).mpr
  have h := mul_le_mul_of_nonneg_left (fraction_lower ha0 ha)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 21/20) hc.le)
  nlinarith only [h]

/-- One explicit load bound excludes every critical aperture simultaneously. -/
theorem capacity_upper {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) : capacity a < 350/417 := by
  have h := mul_lt_mul_of_pos_left SixCrossCapacity.capacity_strict_upper
    (by norm_num : (0 : ℝ) < 21/20)
  exact (capacity_gain_bound ha0 ha).trans_lt (by nlinarith only [h])

end GaloisForLFunctions.ThetaCuspSections.SixApertureCapacity
