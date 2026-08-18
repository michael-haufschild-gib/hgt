import Mathlib

/-!
# Hahn--Jordan residuals before source compression

Finite-atomic form of the Hahn--Jordan boundary used by the completed Euler/Wold source. Positive
and negative residuals reconstruct a signed source coefficient. Forgetting the grade contracts
total variation, strictly when both opposed grades are occupied. Selection is scalar and precedes
operator transport, so it uses no spectral functional calculus.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Positive Jordan part of one real source coefficient. -/
def sourceJordanPositivePart (x : ℝ) : ℝ := max x 0

/-- Negative Jordan part of one real source coefficient. -/
def sourceJordanNegativePart (x : ℝ) : ℝ := max (-x) 0

theorem sourceJordanPositivePart_sub_negativePart (x : ℝ) :
    sourceJordanPositivePart x - sourceJordanNegativePart x = x := by
  rcases le_total 0 x with hx | hx
  · simp [sourceJordanPositivePart, sourceJordanNegativePart, max_eq_left hx,
      max_eq_right (neg_nonpos.mpr hx)]
  · simp [sourceJordanPositivePart, sourceJordanNegativePart, max_eq_right hx,
      max_eq_left (neg_nonneg.mpr hx)]

theorem sourceJordanPositivePart_add_negativePart (x : ℝ) :
    sourceJordanPositivePart x + sourceJordanNegativePart x = |x| := by
  rcases le_total 0 x with hx | hx
  · simp [sourceJordanPositivePart, sourceJordanNegativePart, max_eq_left hx,
      max_eq_right (neg_nonpos.mpr hx), abs_of_nonneg hx]
  · simp [sourceJordanPositivePart, sourceJordanNegativePart, max_eq_right hx,
      max_eq_left (neg_nonneg.mpr hx), abs_of_nonpos hx]

theorem sourceJordanPositivePart_mul_negativePart (x : ℝ) :
    sourceJordanPositivePart x * sourceJordanNegativePart x = 0 := by
  rcases le_total 0 x with hx | hx
  · simp [sourceJordanPositivePart, sourceJordanNegativePart, max_eq_left hx,
      max_eq_right (neg_nonpos.mpr hx)]
  · simp [sourceJordanPositivePart, sourceJordanNegativePart, max_eq_right hx,
      max_eq_left (neg_nonneg.mpr hx)]

/-- Jordan selection is nonlinear; cancellation before selection loses one negative unit. -/
theorem sourceJordanNegativePart_not_additive :
    sourceJordanNegativePart ((1 : ℝ) + (-1)) ≠
      sourceJordanNegativePart 1 + sourceJordanNegativePart (-1) := by
  norm_num [sourceJordanNegativePart]

/-- Intrinsically graded signed density: negative Euler grade, positive regulator grade. -/
def signedSourceGradeDensity {ι κ : Type*} (e : ι → ℝ) (w : κ → ℝ) :
    Sum ι κ → ℝ
  | Sum.inl i => -e i
  | Sum.inr k => w k

@[simp] theorem sourceJordanNegativePart_signedSourceGradeDensity_inl
    {ι κ : Type*} (e : ι → ℝ) (w : κ → ℝ) (i : ι) (he : 0 ≤ e i) :
    sourceJordanNegativePart (signedSourceGradeDensity e w (Sum.inl i)) = e i := by
  simp [sourceJordanNegativePart, signedSourceGradeDensity, max_eq_left he]

@[simp] theorem sourceJordanPositivePart_signedSourceGradeDensity_inl
    {ι κ : Type*} (e : ι → ℝ) (w : κ → ℝ) (i : ι) (he : 0 ≤ e i) :
    sourceJordanPositivePart (signedSourceGradeDensity e w (Sum.inl i)) = 0 := by
  simp [sourceJordanPositivePart, signedSourceGradeDensity, max_eq_right (neg_nonpos.mpr he)]

@[simp] theorem sourceJordanNegativePart_signedSourceGradeDensity_inr
    {ι κ : Type*} (e : ι → ℝ) (w : κ → ℝ) (k : κ) (hw : 0 ≤ w k) :
    sourceJordanNegativePart (signedSourceGradeDensity e w (Sum.inr k)) = 0 := by
  simp [sourceJordanNegativePart, signedSourceGradeDensity, max_eq_right (neg_nonpos.mpr hw)]

@[simp] theorem sourceJordanPositivePart_signedSourceGradeDensity_inr
    {ι κ : Type*} (e : ι → ℝ) (w : κ → ℝ) (k : κ) (hw : 0 ≤ w k) :
    sourceJordanPositivePart (signedSourceGradeDensity e w (Sum.inr k)) = w k := by
  simp [sourceJordanPositivePart, signedSourceGradeDensity, max_eq_left hw]

/-- Total variation retained before forgetting the two source grades. -/
def twoGradePreCompressionVariation (e w : ℝ) : ℝ := e + w

/-- Total variation visible after the signed grades are linearly merged. -/
def twoGradePostCompressionVariation (e w : ℝ) : ℝ := |w - e|

theorem twoGradePostCompressionVariation_le_pre
    {e w : ℝ} (he : 0 ≤ e) (hw : 0 ≤ w) :
    twoGradePostCompressionVariation e w ≤ twoGradePreCompressionVariation e w := by
  rw [twoGradePostCompressionVariation, twoGradePreCompressionVariation]
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem twoGradeCompression_loss_eq_twice_regulator
    {e w : ℝ} (_hw : 0 ≤ w) (hwe : w ≤ e) :
    twoGradePreCompressionVariation e w - twoGradePostCompressionVariation e w = 2 * w := by
  rw [twoGradePreCompressionVariation, twoGradePostCompressionVariation,
    abs_of_nonpos (sub_nonpos.mpr hwe)]
  ring

theorem twoGradePostCompressionVariation_lt_pre
    {e w : ℝ} (hw : 0 < w) (hwe : w ≤ e) :
    twoGradePostCompressionVariation e w < twoGradePreCompressionVariation e w := by
  have h := twoGradeCompression_loss_eq_twice_regulator hw.le hwe
  linarith

/-- Literature frontier in finite-atomic form: Jordan residuals reconstruct the signed current,
while linear grade forgetting strictly contracts variation when both opposed grades are occupied. -/
theorem sourceGradeJordanResidual_dataProcessing
    {e w : ℝ} (he : 0 < e) (hw : 0 < w) (hwe : w ≤ e) :
    sourceJordanPositivePart (-e) = 0 ∧
    sourceJordanNegativePart (-e) = e ∧
    sourceJordanPositivePart w = w ∧
    sourceJordanNegativePart w = 0 ∧
    twoGradePostCompressionVariation e w < twoGradePreCompressionVariation e w := by
  refine ⟨?_, ?_, ?_, ?_, twoGradePostCompressionVariation_lt_pre hw hwe⟩ <;>
    simp [sourceJordanPositivePart, sourceJordanNegativePart, he.le, hw.le]

end

end GaloisForLFunctions.HTGeometry
