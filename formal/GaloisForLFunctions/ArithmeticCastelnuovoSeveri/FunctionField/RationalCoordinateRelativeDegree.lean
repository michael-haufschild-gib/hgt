import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# Relative degrees after rational coordinate realization

Realization at a transcendental coordinate identifies the rational
function field with its actual intermediate field in the ambient
extension. Mapping both fields through this embedding preserves their
relative degree, including rational quotient coordinates.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open scoped IntermediateField
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Rational realization preserves the index of every simple rational-function subfield. -/
theorem rationalCoordinate_relfinrank {x : L} (hx : Transcendental K x) (f : RatFunc K) :
    K⟮((RatFunc.algEquivOfTranscendental x hx) f : L)⟯.relfinrank K⟮x⟯ =
      Module.finrank K⟮f⟯ (RatFunc K) := by
  let φ : RatFunc K →ₐ[K] L := K⟮x⟯.val.comp (RatFunc.algEquivOfTranscendental x hx).toAlgHom
  have hφrange : φ.fieldRange = K⟮x⟯ := by
    rw [show φ = K⟮x⟯.val.comp (RatFunc.algEquivOfTranscendental x hx).toAlgHom from rfl,
      ← AlgHom.map_fieldRange, AlgEquiv.fieldRange_eq_top,
      ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
  have h := IntermediateField.relfinrank_map_map K⟮f⟯ (⊤ : IntermediateField K (RatFunc K)) φ
  rw [IntermediateField.adjoin_map, Set.image_singleton,
    ← AlgHom.fieldRange_eq_map, hφrange, IntermediateField.relfinrank_top_right] at h
  exact h

/-- Polynomial elements realize as polynomial evaluation at the transcendental coordinate. -/
theorem rationalCoordinate_polynomial {x : L} (hx : Transcendental K x) (f : K[X]) :
    ((RatFunc.algEquivOfTranscendental x hx) (algebraMap K[X] (RatFunc K) f) : L) =
      aeval x f := by
  let φ : RatFunc K →ₐ[K] L := K⟮x⟯.val.comp (RatFunc.algEquivOfTranscendental x hx).toAlgHom
  have hhom : φ.comp (IsScalarTower.toAlgHom K K[X] (RatFunc K)) = aeval x := by
    apply Polynomial.algHom_ext
    rw [aeval_X]
    change φ (algebraMap K[X] (RatFunc K) X) = x
    rw [RatFunc.algebraMap_X]
    exact RatFunc.algEquivOfTranscendental_X x hx
  exact congrArg (fun h : K[X] →ₐ[K] L => h f) hhom

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
