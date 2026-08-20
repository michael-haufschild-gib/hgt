import GaloisForLFunctions.HTGeometry.SuperPoincareAlgebra
import GaloisForLFunctions.HTGeometry.MeromorphicReflection

noncomputable section

open scoped Differential

namespace GaloisForLFunctions

open Bottcher

/-- Global meromorphic fraction field on the complex plane. -/
abbrev GlobalMeroField := meroField (Set.univ : Set ℂ)

/-- Meromorphic functional-equation reflection as an integer-linear endomorphism. -/
noncomputable def globalMeroReflectionEnd (c : ℂ) :
    Module.End ℤ GlobalMeroField :=
  (complexReflectionMeroEquiv c).toAddMonoidHom.toIntLinearMap

/-- Quotient-rule meromorphic differentiation as an integer-linear endomorphism. -/
noncomputable def globalMeroDerivativeEnd :
    Module.End ℤ GlobalMeroField := by
  letI := Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty
  letI := meroFieldDifferential isOpen_univ isPreconnected_univ
    Set.univ_nonempty
  exact Differential.deriv.toAddMonoidHom.toIntLinearMap

/-- Meromorphic reflection and differentiation form a split supertranslation sector. -/
noncomputable def globalMeroReflectionD1N2Split (c : ℂ) :
    SuperPoincare.D1N2Split (Module.End ℤ GlobalMeroField) := by
  letI := Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty
  letI := meroFieldDifferential isOpen_univ isPreconnected_univ
    Set.univ_nonempty
  exact SuperPoincare.D1N2Split.ofEqNeg
    (globalMeroReflectionEnd c) globalMeroDerivativeEnd (by
      apply LinearMap.ext
      intro z
      change complexReflectionMeroEquiv c z′ =
        -((complexReflectionMeroEquiv c z)′)
      exact complexReflectionMeroEquiv_deriv c z)

end GaloisForLFunctions
