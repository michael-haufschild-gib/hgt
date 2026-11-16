import GaloisForLFunctions.BiarithmeticGeometry.Affine.PositiveAffineIndex

/-!
# Conjugacy in the positive rational affine group

Conjugation preserves the slope. Away from slope one, translation removes
the shift completely. At slope one, the remaining invariant is the orbit
of the shift under positive rational scaling. This realizes the
semidirect-product classification by the cokernel of `1 - slope`.
-/

noncomputable section
open GaloisForLFunctions.ArithmeticPositiveDuality
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Affine conjugation preserves the scalar part. -/
theorem affine_conjugate_slope (k g : AffineGroupQ) :
    affSlope (k * g * k⁻¹) = affSlope g := by
  rw [affSlope_mul, affSlope_mul, affSlope_inv]
  field_simp [affSlope_ne_zero k]

/-- The translation part of conjugation is a scalar orbit plus a coboundary. -/
theorem affine_conjugate_shift (k g : AffineGroupQ) :
    affShift (k * g * k⁻¹) =
      affSlope k * affShift g + (1 - affSlope g) * affShift k := by
  rw [affShift_mul, affShift_mul, affSlope_mul, affShift_inv]
  field_simp [affSlope_ne_zero k]
  ring

/-- Complete conjugacy criterion: nonunit slopes have one conjugacy class
per slope; translations retain their positive-scaling orbit. -/
theorem positiveAffine_conjugacy_iff (g h : posAffine) :
    (∃ k : posAffine, k * g * k⁻¹ = h) ↔
      affSlope g = affSlope h ∧
        (affSlope g ≠ 1 ∨
          ∃ u : posUnits, affShift h = ((u : ℚˣ) : ℚ) * affShift g) := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨(affine_conjugate_slope k g).symm, ?_⟩
    by_cases ha : affSlope g = 1
    · right
      refine ⟨posAffineSlope k, ?_⟩
      change affShift ((k : AffineGroupQ) * g * (k : AffineGroupQ)⁻¹) =
        affSlope k * affShift g
      rw [affine_conjugate_shift, ha, sub_self, zero_mul, add_zero]
    · exact Or.inl ha
  · rintro ⟨hs, ha | ⟨u, hu⟩⟩
    · let b := (affShift h - affShift g) / (1 - affSlope g)
      refine ⟨posAffineTranslation b, Subtype.ext (affine_ext ?_ ?_)⟩
      · exact (affine_conjugate_slope _ _).trans hs
      · change affShift (translation b * (g : AffineGroupQ) * (translation b)⁻¹) = _
        rw [affine_conjugate_shift, affSlope_translation, affShift_translation, one_mul]
        dsimp only [b]
        field_simp [sub_ne_zero.mpr (Ne.symm ha)]
        ring
    · refine ⟨posAffineDilation u, Subtype.ext (affine_ext ?_ ?_)⟩
      · exact (affine_conjugate_slope _ _).trans hs
      · change affShift (dilation u * (g : AffineGroupQ) * (dilation u)⁻¹) = _
        rw [affine_conjugate_shift, affSlope_dilation, affShift_dilation,
          mul_zero, add_zero, hu]

/-- Translation conjugacy is exactly positive rational rescaling of the step. -/
theorem positiveAffine_translation_conjugacy_iff (b c : ℚ) :
    (∃ k : posAffine,
      k * posAffineTranslation b * k⁻¹ = posAffineTranslation c) ↔
      ∃ u : posUnits, c = ((u : ℚˣ) : ℚ) * b := by
  rw [positiveAffine_conjugacy_iff]
  simp only [posAffineTranslation, affSlope_translation, affShift_translation,
    ne_eq, not_true_eq_false, false_or, true_and]

/-- Group-theoretic form of the complete conjugacy classification. -/
theorem positiveAffine_isConj_iff (g h : posAffine) :
    IsConj g h ↔ affSlope g = affSlope h ∧
      (affSlope g ≠ 1 ∨
        ∃ u : posUnits, affShift h = ((u : ℚˣ) : ℚ) * affShift g) := by
  rw [isConj_iff, positiveAffine_conjugacy_iff]

/-- Translations have exactly three conjugacy types: zero, positive, and negative. -/
theorem positiveAffine_translation_isConj_iff (b c : ℚ) :
    IsConj (posAffineTranslation b) (posAffineTranslation c) ↔
      (b = 0 ∧ c = 0) ∨ (0 < b ∧ 0 < c) ∨ (b < 0 ∧ c < 0) := by
  rw [isConj_iff, positiveAffine_translation_conjugacy_iff]
  constructor
  · rintro ⟨u, rfl⟩
    rcases lt_trichotomy b 0 with hb | hb | hb
    · exact Or.inr (Or.inr ⟨hb, mul_neg_of_pos_of_neg u.property hb⟩)
    · exact Or.inl ⟨hb, by rw [hb, mul_zero]⟩
    · exact Or.inr (Or.inl ⟨hb, mul_pos u.property hb⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨hb, hc⟩ | ⟨hb, hc⟩)
    · exact ⟨1, by simp⟩
    · refine ⟨⟨Units.mk0 (c / b) (div_ne_zero hc.ne' hb.ne'), div_pos hc hb⟩, ?_⟩
      exact (div_mul_cancel₀ c hb.ne').symm
    · refine ⟨⟨Units.mk0 (c / b) (div_ne_zero hc.ne hb.ne),
        div_pos_of_neg_of_neg hc hb⟩, ?_⟩
      exact (div_mul_cancel₀ c hb.ne).symm

#print axioms positiveAffine_conjugacy_iff
#print axioms positiveAffine_translation_conjugacy_iff
#print axioms positiveAffine_isConj_iff
#print axioms positiveAffine_translation_isConj_iff

end GaloisForLFunctions.BiarithmeticGeometry
