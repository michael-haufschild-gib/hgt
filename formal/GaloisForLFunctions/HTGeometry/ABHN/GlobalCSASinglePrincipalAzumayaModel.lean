/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.GlobalCSAOrderAzumayaNumerator
import GaloisForLFunctions.HTGeometry.ABHN.TwoPrincipalOpenAzumayaTransport

/-!
# Single-principal Azumaya scalar-extension models for global CSAs

The two principal-open witnesses of the generic CSA model can be combined, at the cost of scalar
extending the resulting Azumaya algebra, into a model over a single localization by `r * a`.
The divisors of this product are the finite candidate exceptional places.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped NumberField TensorProduct

universe u

noncomputable section

/-- Every number-field CSA has an Azumaya scalar-extension model over one principal
localization of the ring of integers. -/
theorem numberField_exists_singlePrincipalOpen_azumayaScalarExtensionModel_of_csa
    (K : Type u) [Field K] [NumberField K] (A : CSA K) :
    ∃ (O : Subalgebra (𝓞 K) A.carrier) (_ : TensorProduct (𝓞 K) K O ≃ₐ[K] A.carrier)
      (r a : 𝓞 K) (n : ℕ) (s : Localization (Submonoid.powers r)), r ≠ 0 ∧ a ≠ 0 ∧ s ≠ 0 ∧
        Module.Finite (𝓞 K) O ∧
        ∃ hsa : s * (algebraMap (𝓞 K) (Localization (Submonoid.powers r)) r) ^ n =
          algebraMap (𝓞 K) (Localization (Submonoid.powers r)) a,
          let S := Localization (Submonoid.powers r)
          let T := Localization (Submonoid.powers (r * a))
          let U := Localization (Submonoid.powers s)
          let f : S →+* T := IsLocalization.Away.awayToAwayRight r a
          letI : Algebra S U := inferInstance
          letI : Semiring (S ⊗[(𝓞 K)] O) := inferInstance
          letI : Semiring (U ⊗[S] (S ⊗[(𝓞 K)] O)) := inferInstance
          letI : Algebra U (U ⊗[S] (S ⊗[(𝓞 K)] O)) := inferInstance
          letI : Algebra S T := f.toAlgebra
          letI : Algebra U T :=
            (IsLocalization.Away.lift s
              (principalLocalization_numeratorRelation_map_isUnit (𝓞 K) r a n s hsa)).toAlgebra
          IsAzumaya T (T ⊗[U]
            (U ⊗[S] (S ⊗[(𝓞 K)] O))) := by
  obtain ⟨O, e, r, hr, hfin, s, n, a, hs, ha, hsa, has⟩ :=
    numberField_exists_iterated_principalOpen_isAzumayaModel_of_csa_with_numerator K A
  refine ⟨O, e, r, a, n, s, hr, ha, hs, hfin, hsa, ?_⟩
  let S := Localization (Submonoid.powers r)
  let T := Localization (Submonoid.powers (r * a))
  let U := Localization (Submonoid.powers s)
  let f : S →+* T := IsLocalization.Away.awayToAwayRight r a
  letI : Algebra S U := inferInstance
  letI : Semiring (S ⊗[(𝓞 K)] O) := inferInstance
  letI : Semiring (U ⊗[S] (S ⊗[(𝓞 K)] O)) := inferInstance
  letI : Algebra U (U ⊗[S] (S ⊗[(𝓞 K)] O)) := inferInstance
  letI : Algebra S T := f.toAlgebra
  have hunit : IsUnit (f s) := by
    dsimp [f]
    exact principalLocalization_numeratorRelation_map_isUnit (𝓞 K) r a n s hsa
  letI : Algebra U T := (IsLocalization.Away.lift s hunit).toAlgebra
  exact isAzumaya_twoPrincipalOpen_scalarExtension (𝓞 K) r a n s
    (U ⊗[S] (S ⊗[(𝓞 K)] O)) hsa

/-- Every finite-coefficient rational-function-field CSA has an Azumaya scalar-extension model
over one polynomial principal localization. -/
theorem rationalFunction_exists_singlePrincipalOpen_azumayaScalarExtensionModel_of_csa
    (F : Type u) [Field F] [Finite F] (A : CSA (RatFunc F)) :
    letI : Algebra (Polynomial F) A.carrier := rationalFunctionCSARestrictScalarsAlgebra F A
    letI : IsScalarTower (Polynomial F) (RatFunc F) A.carrier :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    ∃ (O : Subalgebra (Polynomial F) A.carrier)
      (_ : TensorProduct (Polynomial F) (RatFunc F) O ≃ₐ[RatFunc F] A.carrier)
      (r a : Polynomial F) (n : ℕ) (s : Localization (Submonoid.powers r)),
      r ≠ 0 ∧ a ≠ 0 ∧ s ≠ 0 ∧ Module.Finite (Polynomial F) O ∧
      ∃ hsa : s * (algebraMap (Polynomial F) (Localization (Submonoid.powers r)) r) ^ n =
          algebraMap (Polynomial F) (Localization (Submonoid.powers r)) a,
        let S := Localization (Submonoid.powers r)
        let T := Localization (Submonoid.powers (r * a))
        let U := Localization (Submonoid.powers s)
        let f : S →+* T := IsLocalization.Away.awayToAwayRight r a
        letI : Algebra S U := inferInstance
        letI : Semiring (S ⊗[(Polynomial F)] O) := inferInstance
        letI : Semiring (U ⊗[S] (S ⊗[(Polynomial F)] O)) := inferInstance
        letI : Algebra U (U ⊗[S] (S ⊗[(Polynomial F)] O)) := inferInstance
        letI : Algebra S T := f.toAlgebra
        letI : Algebra U T :=
          (IsLocalization.Away.lift s
            (principalLocalization_numeratorRelation_map_isUnit (Polynomial F) r a n s hsa)).toAlgebra
        IsAzumaya T (T ⊗[U]
          (U ⊗[S] (S ⊗[(Polynomial F)] O))) := by
  letI : Algebra (Polynomial F) A.carrier := rationalFunctionCSARestrictScalarsAlgebra F A
  letI : IsScalarTower (Polynomial F) (RatFunc F) A.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨O, e, r, hr, hfin, s, n, a, hs, ha, hsa, has⟩ :=
    rationalFunction_exists_iterated_principalOpen_isAzumayaModel_of_csa_with_numerator F A
  refine ⟨O, e, r, a, n, s, hr, ha, hs, hfin, hsa, ?_⟩
  let S := Localization (Submonoid.powers r)
  let T := Localization (Submonoid.powers (r * a))
  let U := Localization (Submonoid.powers s)
  let f : S →+* T := IsLocalization.Away.awayToAwayRight r a
  letI : Algebra S U := inferInstance
  letI : Semiring (S ⊗[(Polynomial F)] O) := inferInstance
  letI : Semiring (U ⊗[S] (S ⊗[(Polynomial F)] O)) := inferInstance
  letI : Algebra U (U ⊗[S] (S ⊗[(Polynomial F)] O)) := inferInstance
  letI : Algebra S T := f.toAlgebra
  have hunit : IsUnit (f s) := by
    dsimp [f]
    exact principalLocalization_numeratorRelation_map_isUnit (Polynomial F) r a n s hsa
  letI : Algebra U T := (IsLocalization.Away.lift s hunit).toAlgebra
  exact isAzumaya_twoPrincipalOpen_scalarExtension (Polynomial F) r a n s
    (U ⊗[S] (S ⊗[(Polynomial F)] O)) hsa

end

end GaloisForLFunctions.HTGeometry.ABHN
