/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CSAOrderAzumayaLocus
import GaloisForLFunctions.HTGeometry.ABHN.NumberFieldFiniteLocalField
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionFiniteLocalField

/-!
# Principal-open Azumaya models over global-field coordinate rings

The generic finite-order theorem specializes without further mathematical assumptions to the ring
of integers of a number field and to the affine-line coordinate ring of a rational function field.
For the latter, this module supplies the explicit central restriction-of-scalars algebra structure
on a central simple algebra.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped NumberField

universe u

noncomputable section

/-- Restrict the scalar structure of a rational-function-field CSA to its polynomial ring.
The image remains central because the original scalar field lies in the center. -/
noncomputable abbrev rationalFunctionCSARestrictScalarsAlgebra
    (F : Type u) [Field F] (A : CSA (RatFunc F)) : Algebra (Polynomial F) A.carrier :=
  let f : (Polynomial F) →+* A.carrier :=
    (algebraMap (RatFunc F) A.carrier).comp (algebraMap (Polynomial F) (RatFunc F))
  f.toAlgebra' (by
    intro c x
    change algebraMap (RatFunc F) A.carrier (algebraMap (Polynomial F) (RatFunc F) c) * x =
      x * algebraMap (RatFunc F) A.carrier (algebraMap (Polynomial F) (RatFunc F) c)
    exact Algebra.commutes _ _)

/-- Every CSA over a number field has a finite order that is Azumaya after two nonzero
principal localizations of the ring of integers. -/
theorem numberField_exists_iterated_principalOpen_isAzumayaModel_of_csa
    (K : Type u) [Field K] [NumberField K] (A : CSA K) :
    ∃ (O : Subalgebra (𝓞 K) A.carrier) (_ : TensorProduct (𝓞 K) K O ≃ₐ[K] A.carrier)
      (r : 𝓞 K), r ≠ 0 ∧
      Module.Finite (𝓞 K) O ∧ ∃ s : Localization (Submonoid.powers r), s ≠ 0 ∧
        IsAzumaya (Localization (Submonoid.powers s))
          (TensorProduct (Localization (Submonoid.powers r)) (Localization (Submonoid.powers s))
            (TensorProduct (𝓞 K) (Localization (Submonoid.powers r)) O)) := by
  exact exists_iterated_principalOpen_isAzumayaModel_of_csa (𝓞 K) K A

/-- Every CSA over a finite-coefficient rational function field has a finite polynomial order
that is Azumaya after two nonzero principal localizations. -/
theorem rationalFunction_exists_iterated_principalOpen_isAzumayaModel_of_csa
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F)) :
    letI : Algebra (Polynomial F) A.carrier := rationalFunctionCSARestrictScalarsAlgebra F A
    letI : IsScalarTower (Polynomial F) (RatFunc F) A.carrier :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    ∃ (O : Subalgebra (Polynomial F) A.carrier)
      (_ : TensorProduct (Polynomial F) (RatFunc F) O ≃ₐ[RatFunc F] A.carrier)
      (r : Polynomial F), r ≠ 0 ∧
      Module.Finite (Polynomial F) O ∧ ∃ s : Localization (Submonoid.powers r), s ≠ 0 ∧
        IsAzumaya (Localization (Submonoid.powers s))
          (TensorProduct (Localization (Submonoid.powers r)) (Localization (Submonoid.powers s))
            (TensorProduct (Polynomial F) (Localization (Submonoid.powers r)) O)) := by
  letI : Algebra (Polynomial F) A.carrier := rationalFunctionCSARestrictScalarsAlgebra F A
  letI : IsScalarTower (Polynomial F) (RatFunc F) A.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact exists_iterated_principalOpen_isAzumayaModel_of_csa (Polynomial F) (RatFunc F) A

end

end GaloisForLFunctions.HTGeometry.ABHN
