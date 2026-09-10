import GaloisForLFunctions.HTGeometry.GomesMissingPolynomialShearAutomorphism
import GaloisForLFunctions.HTGeometry.SuperPoincarePolynomialReflection

/-!
# Exact generation and missing automorphisms for the actual supertranslation model

The corpus's polynomial derivative and functional-equation reflection generate,
together with all even formal functions, exactly the momentum symmetries that
preserve constants. The actual momentum has additional invertible shears, and the
bicommutant forgets precisely this preserved line.
-/

noncomputable section
open Polynomial
namespace GaloisForLFunctions.HTGeometry

/-- The generated algebra uses the corpus's literal derivative and reflection endomorphisms. -/
def gomesActualSupertranslationGeneratedAlgebra : Subalgebra ℂ (Module.End ℂ ℂ[X]) :=
  Algebra.adjoin ℂ ({polynomialDerivativeEnd, reflectPolyEnd} ∪
    Set.range (gomesEvenFormalPolynomialOperator ℂ))

/-- The actual corpus generators identify with the completely classified center-one model. -/
theorem gomesActualSupertranslationGeneratedAlgebra_eq :
    gomesActualSupertranslationGeneratedAlgebra = gomesPolynomialDerivativeReflectionAdjoin ℂ 1 := by
  have hD : polynomialDerivativeEnd = (Polynomial.derivative : Module.End ℂ ℂ[X]) := by
    apply LinearMap.ext
    intro P
    rfl
  have hR : gomesPolynomialReflectionEnd ℂ 1 = reflectPolyEnd := by
    apply LinearMap.ext
    intro P
    rw [gomesPolynomialReflectionEnd_apply]
    change P.comp (C 1 - X) = P.comp (1 - X)
    rw [map_one]
  rw [gomesActualSupertranslationGeneratedAlgebra, gomesPolynomialDerivativeReflectionAdjoin, hD, hR]

/-- Exact generation for the actual supertranslation model is momentum commutation plus constant preservation. -/
theorem gomesActualSupertranslationGeneratedAlgebra_mem_iff (E : Module.End ℂ ℂ[X]) :
    E ∈ gomesActualSupertranslationGeneratedAlgebra ↔
      Commute E polynomialReflectionD1N2Split.momentum0 ∧
        ∀ a : ℂ, (E (C a)).derivative = 0 := by
  rw [gomesActualSupertranslationGeneratedAlgebra_eq]
  exact gomesPolynomialDerivativeReflectionAdjoin_mem_iff ℂ 1 E

/-- The actual supertranslation momentum has strictly more symmetries than the specified generators produce. -/
theorem gomesActualSupertranslationGeneratedAlgebra_lt_fullMomentumCommutant :
    gomesActualSupertranslationGeneratedAlgebra <
      Subalgebra.centralizer ℂ {polynomialReflectionD1N2Split.momentum0} := by
  rw [gomesActualSupertranslationGeneratedAlgebra_eq]
  exact gomesPolynomialDerivativeReflectionAdjoin_lt_fullCommutant ℂ 1

/-- An explicit invertible momentum symmetry is absent, witnessed by its action on the constant polynomial. -/
theorem gomesActualSupertranslation_missing_automorphism :
    ∃ U : (Module.End ℂ ℂ[X])ˣ,
      Commute U.val polynomialReflectionD1N2Split.momentum0 ∧
        U.val ∉ gomesActualSupertranslationGeneratedAlgebra ∧ U.val 1 = 1 + X := by
  rw [gomesActualSupertranslationGeneratedAlgebra_eq]
  exact gomesPolynomialReflectionGenerated_missing_automorphism ℂ 1

/-- The actual model's bicommutant recovers the full momentum commutant and loses constant preservation. -/
theorem gomesActualSupertranslationGeneratedAlgebra_doubleCentralizer :
    Subalgebra.centralizer ℂ
      (Subalgebra.centralizer ℂ (gomesActualSupertranslationGeneratedAlgebra : Set (Module.End ℂ ℂ[X])) :
        Set (Module.End ℂ ℂ[X])) = Subalgebra.centralizer ℂ {polynomialReflectionD1N2Split.momentum0} := by
  rw [gomesActualSupertranslationGeneratedAlgebra_eq]
  exact gomesPolynomialDerivativeReflectionAdjoin_doubleCentralizer ℂ 1

end GaloisForLFunctions.HTGeometry
