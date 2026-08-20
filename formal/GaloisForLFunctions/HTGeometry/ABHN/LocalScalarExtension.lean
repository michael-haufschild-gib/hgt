import GaloisForLFunctions.HTGeometry.ABHN.Places
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionPlaces
import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtension

/-!
# Local scalar-extension carriers for Albert--Brauer--Hasse--Noether

This connects the two global-place packages with the raw scalar extension of a central simple
algebra.  At every actual completion Lean now has the correct local algebra, its canonical map,
finite dimensionality, and centrality.  Simplicity of this tensor product remains the sole
obstruction to packaging the object as a local `CSA` and hence to defining the global-to-local
Brauer map.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v

/-- Raw scalar extension of a number-field central simple algebra at a chosen place. -/
noncomputable def numberFieldLocalScalarExtensionAlg (K : Type u) [Field K] [NumberField K]
    (v : NumberFieldPlace K) (A : CSA.{u, v} K) : AlgCat (completion K v) :=
  scalarExtensionAlg (L := completion K v) A

/-- Canonical map into a number-field local scalar extension. -/
noncomputable def numberFieldLocalScalarExtensionMap (K : Type u) [Field K] [NumberField K]
    (v : NumberFieldPlace K) (A : CSA.{u, v} K) :
    A.carrier →ₐ[K] completion K v ⊗[K] A.carrier :=
  scalarExtensionMap (L := completion K v) A

/-- The canonical map into a number-field local scalar extension is injective. -/
theorem numberFieldLocalScalarExtensionMap_injective (K : Type u) [Field K] [NumberField K]
    (v : NumberFieldPlace K) (A : CSA.{u, v} K) :
    Function.Injective (numberFieldLocalScalarExtensionMap K v A) := by
  exact scalarExtensionMap_injective (L := completion K v) A

/-- Number-field local scalar extension is finite dimensional. -/
theorem numberFieldLocalScalarExtension_finiteDimensional (K : Type u) [Field K] [NumberField K]
    (v : NumberFieldPlace K) (A : CSA.{u, v} K) :
    FiniteDimensional (completion K v) (completion K v ⊗[K] A.carrier) := by
  exact scalarExtensionAlg_finiteDimensional (L := completion K v) A

/-- Number-field local scalar extension is central over its completion. -/
theorem numberFieldLocalScalarExtension_isCentral (K : Type u) [Field K] [NumberField K]
    (v : NumberFieldPlace K) (A : CSA.{u, v} K) :
    Algebra.IsCentral (completion K v) (completion K v ⊗[K] A.carrier) := by
  exact scalarExtensionAlg_isCentral (L := completion K v) A

/-- Raw scalar extension of a central simple algebra over the rational global function field. -/
noncomputable def rationalFunctionLocalScalarExtensionAlg (F : Type u) [Field F] [Finite F]
    (v : RationalFunctionPlace F) (A : CSA.{u, v} (RatFunc F)) :
    AlgCat (rationalFunctionCompletion F v) :=
  scalarExtensionAlg (L := rationalFunctionCompletion F v) A

/-- Canonical map into a rational-function-field local scalar extension. -/
noncomputable def rationalFunctionLocalScalarExtensionMap (F : Type u) [Field F] [Finite F]
    (v : RationalFunctionPlace F) (A : CSA.{u, v} (RatFunc F)) :
    A.carrier →ₐ[RatFunc F] rationalFunctionCompletion F v ⊗[RatFunc F] A.carrier :=
  scalarExtensionMap (L := rationalFunctionCompletion F v) A

/-- The canonical map into a rational-function-field local scalar extension is injective. -/
theorem rationalFunctionLocalScalarExtensionMap_injective (F : Type u) [Field F] [Finite F]
    (v : RationalFunctionPlace F) (A : CSA.{u, v} (RatFunc F)) :
    Function.Injective (rationalFunctionLocalScalarExtensionMap F v A) := by
  exact scalarExtensionMap_injective (L := rationalFunctionCompletion F v) A

/-- Rational-function-field local scalar extension is finite dimensional. -/
theorem rationalFunctionLocalScalarExtension_finiteDimensional (F : Type u) [Field F] [Finite F]
    (v : RationalFunctionPlace F) (A : CSA.{u, v} (RatFunc F)) :
    FiniteDimensional (rationalFunctionCompletion F v)
      (rationalFunctionCompletion F v ⊗[RatFunc F] A.carrier) := by
  exact scalarExtensionAlg_finiteDimensional (L := rationalFunctionCompletion F v) A

/-- Rational-function-field local scalar extension is central over its completion. -/
theorem rationalFunctionLocalScalarExtension_isCentral (F : Type u) [Field F] [Finite F]
    (v : RationalFunctionPlace F) (A : CSA.{u, v} (RatFunc F)) :
    Algebra.IsCentral (rationalFunctionCompletion F v)
      (rationalFunctionCompletion F v ⊗[RatFunc F] A.carrier) := by
  exact scalarExtensionAlg_isCentral (L := rationalFunctionCompletion F v) A

end GaloisForLFunctions.HTGeometry.ABHN
