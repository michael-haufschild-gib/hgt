import GaloisForLFunctions.HTGeometry.RatFuncCompositionDegree
import Mathlib.FieldTheory.RatFunc.IntermediateField


/-!
# Polynomial subfields of a rational function field

A polynomial in the rational coordinate generates a subfield of index
exactly its polynomial degree. This supplies the base-field degree in
trace-polynomial covers before applying the radical-extension tower law.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open scoped IntermediateField

/-- A polynomial coordinate generates a rational subfield whose index is its exact degree. -/
theorem rationalPolynomialSubfield_finrank {K : Type*} [Field K] (f : K[X]) :
    Module.finrank K⟮algebraMap K[X] (RatFunc K) f⟯ (RatFunc K) = f.natDegree := by
  rw [RatFunc.finrank_eq_max_natDegree, RatFunc.num_algebraMap, RatFunc.denom_algebraMap,
    natDegree_one, Nat.max_zero]


/-- Polynomial substitution has the same exact relative degree inside any ambient field. -/
theorem polynomialCoordinate_relfinrank {K L : Type*} [Field K] [Field L] [Algebra K L]
    {x : L} (hx : Transcendental K x) (f : K[X]) :
    K⟮aeval x f⟯.relfinrank K⟮x⟯ = f.natDegree := by
  let φ : RatFunc K →ₐ[K] L := K⟮x⟯.val.comp (RatFunc.algEquivOfTranscendental x hx).toAlgHom
  have hφrange : φ.fieldRange = K⟮x⟯ := by
    rw [show φ = K⟮x⟯.val.comp (RatFunc.algEquivOfTranscendental x hx).toAlgHom from rfl,
      ← AlgHom.map_fieldRange, AlgEquiv.fieldRange_eq_top,
      ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
  have hφX : φ (algebraMap K[X] (RatFunc K) X) = x := by
    rw [RatFunc.algebraMap_X]
    exact RatFunc.algEquivOfTranscendental_X x hx
  have hφC (a : K) : φ (algebraMap K[X] (RatFunc K) (C a)) = algebraMap K L a := by
    rw [show algebraMap K[X] (RatFunc K) (C a) = algebraMap K (RatFunc K) a from
      (IsScalarTower.algebraMap_apply K K[X] (RatFunc K) a).symm]
    exact φ.commutes a
  have hφp (g : K[X]) : φ (algebraMap K[X] (RatFunc K) g) = aeval x g := by
    induction g using Polynomial.induction_on' with
    | add g h hg hh => simp only [map_add, hg, hh]
    | monomial i a =>
      rw [← C_mul_X_pow_eq_monomial]
      simp only [map_mul, map_pow, hφX, hφC, aeval_C, aeval_X]
  have hmap := IntermediateField.relfinrank_map_map
    K⟮algebraMap K[X] (RatFunc K) f⟯ (⊤ : IntermediateField K (RatFunc K)) φ
  rw [IntermediateField.adjoin_map, Set.image_singleton,
    ← AlgHom.fieldRange_eq_map, hφrange, hφp, IntermediateField.relfinrank_top_right] at hmap
  exact hmap.trans (rationalPolynomialSubfield_finrank f)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
