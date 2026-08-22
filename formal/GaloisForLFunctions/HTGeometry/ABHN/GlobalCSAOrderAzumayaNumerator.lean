/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.GlobalCSAOrderAzumayaLocus
import GaloisForLFunctions.HTGeometry.ABHN.PrincipalOpenFinitePlaces

/-!
# Base-ring numerators for global CSA Azumaya loci

The second principal-localization witness in the generic Azumaya-locus theorem has a nonzero
numerator in the original global-field coordinate ring.  Together with the first localization
element, this supplies two explicit finite candidate sets of exceptional places.  This does not
yet compare the resulting completed generic fibers with local Brauer classes.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped NumberField

universe u

noncomputable section

/-- The second principal-localization witness for a number-field CSA Azumaya model has a
nonzero numerator in the ring of integers. -/
theorem numberField_exists_iterated_principalOpen_isAzumayaModel_of_csa_with_numerator
    (K : Type u) [Field K] [NumberField K] (A : CSA K) :
    ∃ (O : Subalgebra (𝓞 K) A.carrier) (_ : TensorProduct (𝓞 K) K O ≃ₐ[K] A.carrier)
      (r : 𝓞 K), r ≠ 0 ∧ Module.Finite (𝓞 K) O ∧
      ∃ (s : Localization (Submonoid.powers r)) (n : ℕ) (a : 𝓞 K), s ≠ 0 ∧ a ≠ 0 ∧
        s * (algebraMap (𝓞 K) (Localization (Submonoid.powers r)) r) ^ n =
          algebraMap (𝓞 K) (Localization (Submonoid.powers r)) a ∧
        IsAzumaya (Localization (Submonoid.powers s))
          (TensorProduct (Localization (Submonoid.powers r)) (Localization (Submonoid.powers s))
            (TensorProduct (𝓞 K) (Localization (Submonoid.powers r)) O)) := by
  obtain ⟨O, e, r, hr, hfin, s, hs, has⟩ :=
    numberField_exists_iterated_principalOpen_isAzumayaModel_of_csa K A
  obtain ⟨n, a, ha, hsa⟩ :=
    exists_nonzero_numerator_of_nonzero_principalLocalization (𝓞 K) r hr s hs
  exact ⟨O, e, r, hr, hfin, s, n, a, hs, ha, hsa, has⟩

/-- The second principal-localization witness for a rational-function-field CSA Azumaya model
has a nonzero polynomial numerator. -/
theorem rationalFunction_exists_iterated_principalOpen_isAzumayaModel_of_csa_with_numerator
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F)) :
    letI : Algebra (Polynomial F) A.carrier := rationalFunctionCSARestrictScalarsAlgebra F A
    letI : IsScalarTower (Polynomial F) (RatFunc F) A.carrier :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    ∃ (O : Subalgebra (Polynomial F) A.carrier)
      (_ : TensorProduct (Polynomial F) (RatFunc F) O ≃ₐ[RatFunc F] A.carrier)
      (r : Polynomial F), r ≠ 0 ∧ Module.Finite (Polynomial F) O ∧
      ∃ (s : Localization (Submonoid.powers r)) (n : ℕ) (a : Polynomial F), s ≠ 0 ∧ a ≠ 0 ∧
        s * (algebraMap (Polynomial F) (Localization (Submonoid.powers r)) r) ^ n =
          algebraMap (Polynomial F) (Localization (Submonoid.powers r)) a ∧
        IsAzumaya (Localization (Submonoid.powers s))
          (TensorProduct (Localization (Submonoid.powers r)) (Localization (Submonoid.powers s))
            (TensorProduct (Polynomial F) (Localization (Submonoid.powers r)) O)) := by
  letI : Algebra (Polynomial F) A.carrier := rationalFunctionCSARestrictScalarsAlgebra F A
  letI : IsScalarTower (Polynomial F) (RatFunc F) A.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨O, e, r, hr, hfin, s, hs, has⟩ :=
    rationalFunction_exists_iterated_principalOpen_isAzumayaModel_of_csa F A
  obtain ⟨n, a, ha, hsa⟩ :=
    exists_nonzero_numerator_of_nonzero_principalLocalization (Polynomial F) r hr s hs
  exact ⟨O, e, r, hr, hfin, s, n, a, hs, ha, hsa, has⟩

end

end GaloisForLFunctions.HTGeometry.ABHN
