import GaloisForLFunctions.HTGeometry.DifferentialAlgebra.OreAffineTranslation
import GaloisForLFunctions.HTGeometry.PseudoDiffOpAutomorphism

/-!
# Affine translations of rational pseudodifferential operators

The affine change of differential generator extends across every nonzero Ore
denominator. Its inverse is the opposite translation, so rational operator
identities can be transported without choosing a presentation by fractions.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.DiffOp

open OreLocalization

variable {K : Type*} [Field K] [Differential K]

/-- The affine substitution extended by the Ore localization universal property. -/
def pseudoAffineTranslationHom (a : K) : PseudoDiffOp K →+* PseudoDiffOp K :=
  OreLocalization.universalHom
    (numeratorRingHom.comp (affineTranslation a).toRingHom)
    (mapNonzeroUnits (affineTranslation a)) (fun _ => rfl)

@[simp] theorem pseudoAffineTranslationHom_numerator (a : K) (p : DiffOp K) :
    pseudoAffineTranslationHom a (numeratorRingHom p) =
      numeratorRingHom (affineTranslationHom a p) :=
  OreLocalization.universalHom_commutes _ _ _

theorem pseudoAffineTranslationHom_comp (a b : K) :
    (pseudoAffineTranslationHom a).comp (pseudoAffineTranslationHom b) =
      pseudoAffineTranslationHom (a + b) := by
  apply pseudoDiffOp_ringHom_ext
  intro p
  change pseudoAffineTranslationHom a (pseudoAffineTranslationHom b (numeratorRingHom p)) = _
  rw [pseudoAffineTranslationHom_numerator, pseudoAffineTranslationHom_numerator,
    pseudoAffineTranslationHom_numerator, affineTranslationHom_comp]

theorem pseudoAffineTranslationHom_zero :
    pseudoAffineTranslationHom (0 : K) = RingHom.id (PseudoDiffOp K) := by
  apply pseudoDiffOp_ringHom_ext
  intro p
  rw [pseudoAffineTranslationHom_numerator, affineTranslationHom_zero]
  rfl

/-- Affine generator translation is an automorphism of the rational operator skew field. -/
def pseudoAffineTranslation (a : K) : PseudoDiffOp K ≃+* PseudoDiffOp K where
  toFun := pseudoAffineTranslationHom a
  invFun := pseudoAffineTranslationHom (-a)
  left_inv x := by
    have h := pseudoAffineTranslationHom_comp (-a) a
    rw [neg_add_cancel, pseudoAffineTranslationHom_zero] at h
    exact DFunLike.congr_fun h x
  right_inv x := by
    have h := pseudoAffineTranslationHom_comp a (-a)
    rw [add_neg_cancel, pseudoAffineTranslationHom_zero] at h
    exact DFunLike.congr_fun h x
  map_mul' := (pseudoAffineTranslationHom a).map_mul
  map_add' := (pseudoAffineTranslationHom a).map_add

@[simp] theorem pseudoAffineTranslation_X (a : K) :
    pseudoAffineTranslation a (numeratorRingHom (X : DiffOp K)) =
      numeratorRingHom X + numeratorRingHom (C a) := by
  change pseudoAffineTranslationHom a (numeratorRingHom X) = _
  rw [pseudoAffineTranslationHom_numerator, affineTranslationHom_X, _root_.map_add]

@[simp] theorem pseudoAffineTranslation_C (a c : K) :
    pseudoAffineTranslation a (numeratorRingHom (C c)) = numeratorRingHom (C c) := by
  change pseudoAffineTranslationHom a (numeratorRingHom (C c)) = _
  rw [pseudoAffineTranslationHom_numerator, affineTranslationHom_C]

/-- Inverse differential generators transform by the same rational substitution. -/
theorem pseudoAffineTranslation_inv_X (a : K) :
    pseudoAffineTranslation a (numeratorRingHom (X : DiffOp K))⁻¹ =
      (numeratorRingHom X + numeratorRingHom (C a))⁻¹ := by
  rw [map_inv₀, pseudoAffineTranslation_X]

end GaloisForLFunctions.HTGeometry.DiffOp

#print axioms GaloisForLFunctions.HTGeometry.DiffOp.pseudoAffineTranslation
