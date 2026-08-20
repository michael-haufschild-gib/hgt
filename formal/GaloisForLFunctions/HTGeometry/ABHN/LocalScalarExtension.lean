import GaloisForLFunctions.HTGeometry.ABHN.Places
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionPlaces
import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtension
import GaloisForLFunctions.HTGeometry.ABHN.AzumayaBaseChange
import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtensionBrauer
import GaloisForLFunctions.HTGeometry.ABHN.ScalarExtensionTensorProduct

/-!
# Local scalar-extension carriers for Albert--Brauer--Hasse--Noether

This connects the two global-place packages with the raw scalar extension of a central simple
algebra.  At every actual completion Lean now has the correct local algebra, its canonical map,
finite dimensionality, centrality, and simplicity.  Thus every global central simple representative
has a genuine local central simple representative at every actual completion.
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

/-- The central simple algebra obtained from a number-field central simple algebra at a place. -/
noncomputable def numberFieldLocalCSA (K : Type u) [Field K] [NumberField K]
    (v : NumberFieldPlace K) (A : CSA.{u, v} K) : CSA.{u, max u v} (completion K v) where
  carrier := completion K v ⊗[K] A.carrier
  isCentral := numberFieldLocalScalarExtension_isCentral K v A
  isSimple := by
    letI : IsAzumaya K A.carrier := csa_isAzumaya A
    letI : IsAzumaya (completion K v) (completion K v ⊗[K] A.carrier) :=
      isAzumaya_scalarExtension (K := K) (L := completion K v) (A := A.carrier)
    exact isSimpleRing_of_isAzumaya (K := completion K v) _
  fin_dim := numberFieldLocalScalarExtension_finiteDimensional K v A

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

/-- The central simple algebra obtained from a rational-function-field central simple algebra at
a place. -/
noncomputable def rationalFunctionLocalCSA (F : Type u) [Field F] [Finite F]
    (v : RationalFunctionPlace F) (A : CSA.{u, v} (RatFunc F)) :
    CSA.{u, max u v} (rationalFunctionCompletion F v) where
  carrier := rationalFunctionCompletion F v ⊗[RatFunc F] A.carrier
  isCentral := rationalFunctionLocalScalarExtension_isCentral F v A
  isSimple := by
    letI : IsAzumaya (RatFunc F) A.carrier := csa_isAzumaya A
    letI : IsAzumaya (rationalFunctionCompletion F v)
        (rationalFunctionCompletion F v ⊗[RatFunc F] A.carrier) :=
      isAzumaya_scalarExtension (K := RatFunc F) (L := rationalFunctionCompletion F v)
        (A := A.carrier)
    exact isSimpleRing_of_isAzumaya (K := rationalFunctionCompletion F v) _
  fin_dim := rationalFunctionLocalScalarExtension_finiteDimensional F v A

/-- Local Brauer classes of one number-field central simple representative.  This is the
representative-level precursor to the global-to-local quotient map. -/
noncomputable def numberFieldLocalBrauerClasses (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, v} K) : localBrauerClasses K := fun v ↦
  brauerClass (numberFieldLocalCSA K v A)

/-- Local Brauer classes of one rational-function-field central simple representative. -/
noncomputable def rationalFunctionLocalBrauerClassesOfCSA (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, v} (RatFunc F)) : rationalFunctionLocalBrauerClasses F := fun v ↦
  brauerClass (rationalFunctionLocalCSA F v A)

/-- The number-field global-to-local map on Brauer quotients.  The finite ramification theorem
needed to land in `RestrictedLocalBrauerClasses` is a later ABHN input. -/
noncomputable def numberFieldLocalBrauerMap (K : Type u) [Field K] [NumberField K] :
    BrauerGroup.{u, u} K → localBrauerClasses K := fun x v ↦
  scalarExtensionBrauerMap K (completion K v) x

/-- The quotient-level number-field global-to-local map agrees with its representative-level
construction. -/
theorem numberFieldLocalBrauerMap_brauerClass (K : Type u) [Field K] [NumberField K]
    (A : CSA.{u, u} K) :
    numberFieldLocalBrauerMap K (brauerClass A) = numberFieldLocalBrauerClasses K A := by
  funext v
  rfl

/-- The number-field global-to-local map sends the split global class to the everywhere-split
local family. -/
theorem numberFieldLocalBrauerMap_split (K : Type u) [Field K] [NumberField K] :
    numberFieldLocalBrauerMap K (brauerSplitClass K) =
      (restrictedSplitClass K).toLocalBrauerClasses := by
  funext v
  change scalarExtensionBrauerMap K (completion K v) (brauerSplitClass K) =
    brauerSplitClass (completion K v)
  exact scalarExtensionBrauerMap_split K (completion K v)

/-- Number-field localization preserves tensor-product addition pointwise at every place. -/
theorem numberFieldLocalBrauerMap_tensorAdd (K : Type u) [Field K] [NumberField K]
    (x y : BrauerGroup.{u, u} K) :
    numberFieldLocalBrauerMap K (brauerTensorAdd K x y) = fun v ↦
      brauerTensorAdd (completion K v) (numberFieldLocalBrauerMap K x v)
        (numberFieldLocalBrauerMap K y v) := by
  funext v
  exact scalarExtensionBrauerMap_tensorAdd K (completion K v) x y

/-- The number-field global-to-local Brauer map as an additive homomorphism.  This is the
unrestricted product map; finite ramification is the remaining step to the ABHN local term. -/
noncomputable def numberFieldLocalBrauerAddHom (K : Type u) [Field K] [NumberField K] :
    BrauerGroup.{u, u} K →+ localBrauerClasses K where
  toFun := numberFieldLocalBrauerMap K
  map_zero' := numberFieldLocalBrauerMap_split K
  map_add' := numberFieldLocalBrauerMap_tensorAdd K

/-- The rational-function-field global-to-local map on Brauer quotients.  Its upgrade to finite
support is likewise precisely the finite ramification part of ABHN. -/
noncomputable def rationalFunctionLocalBrauerMap (F : Type u) [Field F] [Finite F] :
    BrauerGroup.{u, u} (RatFunc F) → rationalFunctionLocalBrauerClasses F := fun x v ↦
  scalarExtensionBrauerMap (RatFunc F) (rationalFunctionCompletion F v) x

/-- The quotient-level rational-function-field global-to-local map agrees with its
representative-level construction. -/
theorem rationalFunctionLocalBrauerMap_brauerClass (F : Type u) [Field F] [Finite F]
    (A : CSA.{u, u} (RatFunc F)) :
    rationalFunctionLocalBrauerMap F (brauerClass A) =
      rationalFunctionLocalBrauerClassesOfCSA F A := by
  funext v
  rfl

/-- The rational-function-field global-to-local map sends the split global class to the
everywhere-split local family. -/
theorem rationalFunctionLocalBrauerMap_split (F : Type u) [Field F] [Finite F] :
    rationalFunctionLocalBrauerMap F (brauerSplitClass (RatFunc F)) =
      (rationalFunctionRestrictedSplitClass F).toLocalBrauerClasses := by
  funext v
  change scalarExtensionBrauerMap (RatFunc F) (rationalFunctionCompletion F v)
      (brauerSplitClass (RatFunc F)) = brauerSplitClass (rationalFunctionCompletion F v)
  exact scalarExtensionBrauerMap_split (RatFunc F) (rationalFunctionCompletion F v)

/-- Rational-function-field localization preserves tensor-product addition pointwise at every
place. -/
theorem rationalFunctionLocalBrauerMap_tensorAdd (F : Type u) [Field F] [Finite F]
    (x y : BrauerGroup.{u, u} (RatFunc F)) :
    rationalFunctionLocalBrauerMap F (brauerTensorAdd (RatFunc F) x y) = fun v ↦
      brauerTensorAdd (rationalFunctionCompletion F v)
        (rationalFunctionLocalBrauerMap F x v) (rationalFunctionLocalBrauerMap F y v) := by
  funext v
  exact scalarExtensionBrauerMap_tensorAdd (RatFunc F) (rationalFunctionCompletion F v) x y

/-- The rational-function-field global-to-local Brauer map as an additive homomorphism. -/
noncomputable def rationalFunctionLocalBrauerAddHom (F : Type u) [Field F] [Finite F] :
    BrauerGroup.{u, u} (RatFunc F) →+ rationalFunctionLocalBrauerClasses F where
  toFun := rationalFunctionLocalBrauerMap F
  map_zero' := rationalFunctionLocalBrauerMap_split F
  map_add' := rationalFunctionLocalBrauerMap_tensorAdd F

/-- At every number-field place, the local scalar extension of a split matrix representative is
definitionally the standard scalar extension of that split matrix algebra. -/
theorem numberFieldLocalCSA_matrixFinScalar_eq (K : Type u) [Field K] [NumberField K]
    (v : NumberFieldPlace K) (n : ℕ) [NeZero n] :
    numberFieldLocalCSA K v (matrixFinCSA (scalarCSA K) n) =
      scalarExtensionMatrixFinScalarCSA K (completion K v) n := by
  rfl

/-- Every split matrix representative has split local class at every number-field place. -/
theorem numberFieldLocalBrauerClass_matrixFinScalar_eq_split (K : Type u) [Field K]
    [NumberField K] (v : NumberFieldPlace K) (n : ℕ) [NeZero n] :
    brauerClass (numberFieldLocalCSA K v (matrixFinCSA (scalarCSA K) n)) =
      brauerSplitClass (completion K v) := by
  rw [numberFieldLocalCSA_matrixFinScalar_eq]
  exact brauerClass_scalarExtensionMatrixFinScalar_eq (K := K) (L := completion K v) n

/-- Representative-level local classes send every split matrix representative to the everywhere
split number-field local family. -/
theorem numberFieldLocalBrauerClasses_matrixFinScalar_eq_split (K : Type u) [Field K]
    [NumberField K] (n : ℕ) [NeZero n] :
    numberFieldLocalBrauerClasses K (matrixFinCSA (scalarCSA K) n) =
      (restrictedSplitClass K).toLocalBrauerClasses := by
  funext v
  change brauerClass (numberFieldLocalCSA K v (matrixFinCSA (scalarCSA K) n)) =
    brauerSplitClass (completion K v)
  exact numberFieldLocalBrauerClass_matrixFinScalar_eq_split K v n

/-- At every rational-function-field place, the local scalar extension of a split matrix
representative is the standard scalar extension of that split matrix algebra. -/
theorem rationalFunctionLocalCSA_matrixFinScalar_eq (F : Type u) [Field F] [Finite F]
    (v : RationalFunctionPlace F) (n : ℕ) [NeZero n] :
    rationalFunctionLocalCSA F v (matrixFinCSA (scalarCSA (RatFunc F)) n) =
      scalarExtensionMatrixFinScalarCSA (RatFunc F) (rationalFunctionCompletion F v) n := by
  rfl

/-- Every split matrix representative has split local class at every rational-function-field
place. -/
theorem rationalFunctionLocalBrauerClass_matrixFinScalar_eq_split (F : Type u) [Field F]
    [Finite F] (v : RationalFunctionPlace F) (n : ℕ) [NeZero n] :
    brauerClass (rationalFunctionLocalCSA F v (matrixFinCSA (scalarCSA (RatFunc F)) n)) =
      brauerSplitClass (rationalFunctionCompletion F v) := by
  rw [rationalFunctionLocalCSA_matrixFinScalar_eq]
  exact brauerClass_scalarExtensionMatrixFinScalar_eq
    (K := RatFunc F) (L := rationalFunctionCompletion F v) n

/-- Representative-level local classes send every split matrix representative to the everywhere
split rational-function-field local family. -/
theorem rationalFunctionLocalBrauerClasses_matrixFinScalar_eq_split (F : Type u) [Field F]
    [Finite F] (n : ℕ) [NeZero n] :
    rationalFunctionLocalBrauerClassesOfCSA F (matrixFinCSA (scalarCSA (RatFunc F)) n) =
      (rationalFunctionRestrictedSplitClass F).toLocalBrauerClasses := by
  funext v
  change brauerClass (rationalFunctionLocalCSA F v (matrixFinCSA (scalarCSA (RatFunc F)) n)) =
    brauerSplitClass (rationalFunctionCompletion F v)
  exact rationalFunctionLocalBrauerClass_matrixFinScalar_eq_split F v n

end GaloisForLFunctions.HTGeometry.ABHN
