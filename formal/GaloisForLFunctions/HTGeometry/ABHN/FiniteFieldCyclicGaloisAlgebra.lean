/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.FiniteFieldCohomology
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2Split

/-!
# Finite-field cyclic algebras are split

For a finite cyclic Galois extension of finite fields, the unit norm is surjective.  The cyclic
degree-two cohomology parameter therefore vanishes, and its raw cyclic algebra is isomorphic to
the split cyclic algebra.  This turns the finite-field cohomology calculation into an actual
central-simple and Brauer-class statement, without assuming a general cohomology--Brauer
comparison.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open CategoryTheory groupCohomology Rep Rep.FiniteCyclicGroup

attribute [local instance] IsCyclic.commGroup

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsCyclic Gal(L/K)]

/-- Every cyclic degree-two base-unit parameter over a finite coefficient field is zero in
cohomology. -/
theorem finiteField_cyclicGaloisH2BaseProjection_eq_zero
    [FiniteDimensional K L] [IsGalois K L] [Finite L] (a : Additive Kˣ) :
    cyclicGaloisH2BaseProjection K L a = 0 :=
  finiteField_H2_eq_zero (cyclicGaloisH2BaseProjection K L a)

/-- A cyclic degree-two base parameter over a finite coefficient field is an actual field norm. -/
theorem finiteField_cyclicGaloisH2BaseParameter_exists_norm
    [FiniteDimensional K L] [IsGalois K L] [Finite L] (a : Additive Kˣ) :
    ∃ c : Lˣ, (a.toMul : K) = Algebra.norm K (c : L) :=
  cyclicGaloisH2BaseProjection_eq_zero_exists_norm K L a
    (finiteField_cyclicGaloisH2BaseProjection_eq_zero K L a)

/-- A selected norm witness for a finite-field cyclic degree-two parameter. -/
noncomputable def finiteField_cyclicGaloisNormWitness
    [FiniteDimensional K L] [IsGalois K L] [Finite L] (a : Additive Kˣ) : Lˣ :=
  (finiteField_cyclicGaloisH2BaseParameter_exists_norm K L a).choose

/-- The selected finite-field norm witness realizes its base parameter. -/
theorem finiteField_cyclicGaloisNormWitness_spec
    [FiniteDimensional K L] [IsGalois K L] [Finite L] (a : Additive Kˣ) :
    (a.toMul : K) = Algebra.norm K (finiteField_cyclicGaloisNormWitness K L a : L) :=
  (finiteField_cyclicGaloisH2BaseParameter_exists_norm K L a).choose_spec

/-- A finite-field cyclic algebra is explicitly isomorphic to its split parameter-one algebra. -/
noncomputable def finiteField_cyclicGaloisAlgebraSplitAlgEquiv
    [FiniteDimensional K L] [IsGalois K L] [Finite L] (a : Additive Kˣ) :
    cyclicGaloisAlgebra K L (a.toMul : K) ≃ₐ[K] cyclicGaloisAlgebra K L 1 :=
  cyclicGaloisAlgebraNormScaleAlgEquiv K L (a.toMul : K) 1
    (finiteField_cyclicGaloisNormWitness K L a) (by
      simpa using finiteField_cyclicGaloisNormWitness_spec K L a)

/-- Every raw cyclic algebra over a finite cyclic Galois extension of finite fields is simple. -/
theorem finiteField_isSimpleRing_cyclicGaloisAlgebra
    [FiniteDimensional K L] [IsGalois K L] [Finite L] (a : Additive Kˣ) :
    IsSimpleRing (cyclicGaloisAlgebra K L (a.toMul : K)) :=
  IsSimpleRing.of_ringEquiv
    (finiteField_cyclicGaloisAlgebraSplitAlgEquiv K L a).symm.toRingEquiv
    (isSimpleRing_cyclicGaloisAlgebra_split K L)

/-- The raw cyclic algebra of every finite-field cyclic parameter is a finite-dimensional
central simple algebra. -/
noncomputable def finiteField_cyclicGaloisAlgebraCSA
    [FiniteDimensional K L] [IsGalois K L] [Finite L] (a : Additive Kˣ) : CSA K :=
  cyclicGaloisAlgebraNormCSA K L (a.toMul : K)
    (finiteField_cyclicGaloisNormWitness K L a)
    (finiteField_cyclicGaloisNormWitness_spec K L a)

/-- Every cyclic algebra over a finite cyclic Galois extension represents the split Brauer
class.  This is the algebra-level form of finite-field degree-two cohomology vanishing. -/
theorem finiteField_brauerClass_cyclicGaloisAlgebraCSA_eq_split
    [FiniteDimensional K L] [IsGalois K L] [Finite L] (a : Additive Kˣ) :
    brauerClass (finiteField_cyclicGaloisAlgebraCSA K L a) = brauerSplitClass K :=
  brauerClass_cyclicGaloisAlgebraNormCSA_eq_split K L (a.toMul : K)
    (finiteField_cyclicGaloisNormWitness K L a)
    (finiteField_cyclicGaloisNormWitness_spec K L a)

end GaloisForLFunctions.HTGeometry.ABHN
