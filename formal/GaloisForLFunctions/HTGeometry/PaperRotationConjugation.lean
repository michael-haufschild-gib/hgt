import GaloisForLFunctions.HTGeometry.PaperRotationCommutatorIdealTrace
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Isometric conjugation by bilateral shifts

Shift conjugation fixes shifts and multiplies modulations by their literal rotation phase. The
whole operator algebra is transported by a star algebra automorphism, preserving its norm.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The already constructed shift, bundled with its exact inverse and isometry. -/
def paperRotationShiftEquiv (a : ℤ) : PaperRotationHilbert ≃ₗᵢ[ℂ] PaperRotationHilbert where
  toLinearEquiv :=
    { (paperRotationShift a).toLinearMap with
      invFun := paperRotationShift (-a)
      left_inv := fun v => by
        change (paperRotationShift (-a) ∘L paperRotationShift a) v = v
        rw [paperRotationShift_comp, neg_add_cancel, paperRotationShift_zero]
        rfl
      right_inv := fun v => by
        change (paperRotationShift a ∘L paperRotationShift (-a)) v = v
        rw [paperRotationShift_comp, add_neg_cancel, paperRotationShift_zero]
        rfl }
  norm_map' := paperRotationShift_norm a

/-- Pull an operator back by the integer shift. -/
def paperRotationConjugation (a : ℤ) :
    (PaperRotationHilbert →L[ℂ] PaperRotationHilbert) ≃⋆ₐ[ℂ]
      (PaperRotationHilbert →L[ℂ] PaperRotationHilbert) :=
  (paperRotationShiftEquiv a).symm.conjStarAlgEquiv

@[simp] theorem paperRotationConjugation_apply (a : ℤ)
    (T : PaperRotationHilbert →L[ℂ] PaperRotationHilbert) (v : PaperRotationHilbert) :
    paperRotationConjugation a T v =
      paperRotationShift (-a) (T (paperRotationShift a v)) := rfl

theorem paperRotationConjugation_norm (a : ℤ)
    (T : PaperRotationHilbert →L[ℂ] PaperRotationHilbert) :
    ‖paperRotationConjugation a T‖ = ‖T‖ :=
  NonUnitalStarAlgHom.norm_map (paperRotationConjugation a)
    (paperRotationConjugation a).injective T

theorem paperRotationConjugation_isometry (a : ℤ) :
    Isometry (paperRotationConjugation a) :=
  NonUnitalStarAlgHom.isometry (paperRotationConjugation a)
    (paperRotationConjugation a).injective

/-- Shift conjugation fixes every integer translation. -/
theorem paperRotationConjugation_shift (a b : ℤ) :
    paperRotationConjugation a (paperRotationShift b) = paperRotationShift b := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext i
  simp only [paperRotationConjugation_apply, paperRotationShift_apply]
  have hi : i - -a - b - a = i - b := by omega
  rw [hi]

/-- The modulation acquires exactly the native signed rotation multiplier. -/
theorem paperRotationConjugation_modulation (a : ℤ) (t : ℝ) :
    paperRotationConjugation a (paperRotationModulation t) =
      paperRotationPhase ((a : ℝ) * t) • paperRotationModulation t := by
  apply ContinuousLinearMap.ext
  intro v
  apply lp.ext
  funext i
  simp only [paperRotationConjugation_apply, paperRotationShift_apply,
    paperRotationModulation_apply, smul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  have hi : i - -a - a = i := by omega
  rw [hi, ← mul_assoc, ← paperRotationPhase_add]
  congr 2
  push_cast
  ring

/-- Conjugation preserves each Weyl word up to its scalar character. -/
theorem paperRotationConjugation_word (a b : ℤ) (t : ℝ) :
    paperRotationConjugation a (paperRotationWord b t) =
      paperRotationPhase ((a : ℝ) * t) • paperRotationWord b t := by
  change paperRotationConjugation a (paperRotationModulation t * paperRotationShift b) = _
  rw [map_mul, paperRotationConjugation_modulation, paperRotationConjugation_shift,
    smul_mul_assoc]
  rfl

end

end GaloisForLFunctions.HTGeometry
