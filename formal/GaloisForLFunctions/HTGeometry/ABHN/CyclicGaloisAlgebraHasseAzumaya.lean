/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisAlgebraCompanionRepresentation
import GaloisForLFunctions.HTGeometry.ABHN.HasseAzumaya

/-!
# Hasse-local Azumaya structure of cyclic Galois algebras

A nonzero cyclic Galois algebra is a central simple algebra, hence Azumaya.  The Hasse–Azumaya
criterion then transfers this structural property exactly to the completed scalar extensions of
number fields and global function fields.  These results preserve Azumaya/Morita structure at
places; they do not assert that the local algebra is split or assign a local Brauer invariant.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

/-- A cyclic Galois algebra with nonzero parameter is Azumaya over its base field. -/
theorem cyclicGaloisAlgebra_isAzumaya_of_nonzero
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) :
    IsAzumaya K (cyclicGaloisAlgebra K L a) :=
  csa_isAzumaya (cyclicGaloisAlgebraCSA K L a ha)

/-- For a cyclic Galois algebra over a number field, Azumaya-ness is equivalent to Azumaya-ness
at every completion. -/
theorem numberField_cyclicGaloisAlgebra_isAzumaya_iff_forall_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] (a : K) :
    IsAzumaya K (cyclicGaloisAlgebra K L a) ↔ ∀ p : NumberFieldPlace K,
      IsAzumaya (completion K p) (completion K p ⊗[K] cyclicGaloisAlgebra K L a) :=
  numberField_isAzumaya_iff_forall_place K

/-- For a cyclic Galois algebra over a global function field, Azumaya-ness is equivalent to
Azumaya-ness at every completion. -/
theorem rationalFunction_cyclicGaloisAlgebra_isAzumaya_iff_forall_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) :
    IsAzumaya (RatFunc F) (cyclicGaloisAlgebra (RatFunc F) L a) ↔
      ∀ p : RationalFunctionPlace F,
        IsAzumaya (rationalFunctionCompletion F p)
          (rationalFunctionCompletion F p ⊗[RatFunc F] cyclicGaloisAlgebra (RatFunc F) L a) :=
  rationalFunction_isAzumaya_iff_forall_place F

/-- For a cyclic Galois algebra over a number field, one completed scalar extension is Azumaya
exactly when the global algebra is Azumaya. -/
theorem numberField_cyclicGaloisAlgebra_isAzumaya_iff_exists_place
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L] (a : K) :
    IsAzumaya K (cyclicGaloisAlgebra K L a) ↔ ∃ p : NumberFieldPlace K,
      IsAzumaya (completion K p) (completion K p ⊗[K] cyclicGaloisAlgebra K L a) :=
  numberField_isAzumaya_iff_exists_place K

/-- For a cyclic Galois algebra over a global function field, one completed scalar extension is
Azumaya exactly when the global algebra is Azumaya. -/
theorem rationalFunction_cyclicGaloisAlgebra_isAzumaya_iff_exists_place
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) :
    IsAzumaya (RatFunc F) (cyclicGaloisAlgebra (RatFunc F) L a) ↔
      ∃ p : RationalFunctionPlace F,
        IsAzumaya (rationalFunctionCompletion F p)
          (rationalFunctionCompletion F p ⊗[RatFunc F] cyclicGaloisAlgebra (RatFunc F) L a) :=
  rationalFunction_isAzumaya_iff_exists_place F

/-- Every completed scalar extension of a nonzero cyclic Galois algebra over a number field is
Azumaya. -/
theorem numberField_cyclicGaloisAlgebra_isAzumaya_at_all_places
    (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
    [IsCyclic Gal(L/K)] [FiniteDimensional K L] [IsGalois K L]
    (a : K) (ha : a ≠ 0) :
    ∀ p : NumberFieldPlace K,
      IsAzumaya (completion K p) (completion K p ⊗[K] cyclicGaloisAlgebra K L a) :=
  (numberField_cyclicGaloisAlgebra_isAzumaya_iff_forall_place K L a).mp
    (cyclicGaloisAlgebra_isAzumaya_of_nonzero K L a ha)

/-- Every completed scalar extension of a nonzero cyclic Galois algebra over a global function
field is Azumaya. -/
theorem rationalFunction_cyclicGaloisAlgebra_isAzumaya_at_all_places
    (F L : Type) [Field F] [Finite F] [Field L] [Algebra (RatFunc F) L]
    [IsCyclic Gal(L / RatFunc F)] [FiniteDimensional (RatFunc F) L] [IsGalois (RatFunc F) L]
    (a : RatFunc F) (ha : a ≠ 0) :
    ∀ p : RationalFunctionPlace F,
      IsAzumaya (rationalFunctionCompletion F p)
        (rationalFunctionCompletion F p ⊗[RatFunc F] cyclicGaloisAlgebra (RatFunc F) L a) :=
  (rationalFunction_cyclicGaloisAlgebra_isAzumaya_iff_forall_place F L a).mp
    (cyclicGaloisAlgebra_isAzumaya_of_nonzero (RatFunc F) L a ha)

end GaloisForLFunctions.HTGeometry.ABHN
