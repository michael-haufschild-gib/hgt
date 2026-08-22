/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.GlobalCSASinglePrincipalAzumayaModel
import GaloisForLFunctions.HTGeometry.ABHN.PrincipalOpenAzumayaResidueSupport

/-!
# Finite residue ramification of global CSA models

Every central simple algebra over a number field or a finite-coefficient rational function field
has a two-principal Azumaya scalar-extension model.  Its height-one valuation residue fibers are
split outside the finite divisor set of the two principal numerators.

This is the complete finite-ramification statement available from the present Azumaya and finite
residue infrastructure.  It deliberately concerns residue fibers of the constructed model, not
the Brauer classes of completed generic fibers; their comparison remains the local
class-field-theory bridge.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped NumberField TensorProduct

universe u

noncomputable section

/-- Every number-field CSA has a two-principal Azumaya scalar-extension model whose height-one
residue Brauer fibers are split away from a finite exceptional divisor set. -/
theorem numberField_csa_exists_twoPrincipalOpen_azumayaResidueFiniteRamification
    (K : Type u) [Field K] [NumberField K] (A : CSA K) :
    ∃ (O : Subalgebra (𝓞 K) A.carrier) (_ : TensorProduct (𝓞 K) K O ≃ₐ[K] A.carrier)
      (r a : 𝓞 K) (n : ℕ) (s : Localization (Submonoid.powers r)),
      r ≠ 0 ∧ a ≠ 0 ∧ s ≠ 0 ∧ Module.Finite (𝓞 K) O ∧
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
        let B := T ⊗[U] (U ⊗[S] (S ⊗[(𝓞 K)] O))
        ∃ hAz : IsAzumaya T B,
          letI : IsAzumaya T B := hAz
          (twoPrincipalOpenAzumayaResidueBadHeightOnePrimes (𝓞 K) r a).Finite ∧
            ∀ (P : HeightOneSpectrum (𝓞 K))
              (hP : P ∉ twoPrincipalOpenAzumayaResidueBadHeightOnePrimes (𝓞 K) r a),
              twoPrincipalOpenAzumayaHeightOneResidueBrauerClass (𝓞 K) K P r a
                (by simpa [twoPrincipalOpenAzumayaResidueBadHeightOnePrimes] using hP) B =
                brauerSplitClass (IsLocalRing.ResidueField ((P.valuation K).valuationSubring)) := by
  obtain ⟨O, e, r, a, n, s, hr, ha, hs, hfin, hsa, has⟩ :=
    numberField_exists_singlePrincipalOpen_azumayaScalarExtensionModel_of_csa K A
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
  letI : Algebra U T :=
    (IsLocalization.Away.lift s
      (principalLocalization_numeratorRelation_map_isUnit (𝓞 K) r a n s hsa)).toAlgebra
  letI : IsAzumaya T (T ⊗[U] (U ⊗[S] (S ⊗[(𝓞 K)] O))) := has
  refine ⟨has, finite_twoPrincipalOpenAzumayaResidueBadHeightOnePrimes (𝓞 K) r a hr ha, ?_⟩
  intro P hP
  exact numberField_twoPrincipalOpenAzumayaHeightOneResidueBrauerClass_eq_split_of_not_mem
    K P r a hP (T ⊗[U] (U ⊗[S] (S ⊗[(𝓞 K)] O)))

/-- Every finite-coefficient rational-function-field CSA has a two-principal Azumaya
scalar-extension model whose finite height-one residue Brauer fibers are split away from a finite
exceptional divisor set. -/
theorem rationalFunction_csa_exists_twoPrincipalOpen_azumayaResidueFiniteRamification
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
        let B := T ⊗[U] (U ⊗[S] (S ⊗[(Polynomial F)] O))
        ∃ hAz : IsAzumaya T B,
          letI : IsAzumaya T B := hAz
          (twoPrincipalOpenAzumayaResidueBadHeightOnePrimes (Polynomial F) r a).Finite ∧
            ∀ (P : HeightOneSpectrum (Polynomial F))
              (hP : P ∉ twoPrincipalOpenAzumayaResidueBadHeightOnePrimes (Polynomial F) r a),
              twoPrincipalOpenAzumayaHeightOneResidueBrauerClass (Polynomial F) (RatFunc F)
                P r a
                (by simpa [twoPrincipalOpenAzumayaResidueBadHeightOnePrimes] using hP) B =
                brauerSplitClass
                  (IsLocalRing.ResidueField ((P.valuation (RatFunc F)).valuationSubring)) := by
  letI : Algebra (Polynomial F) A.carrier := rationalFunctionCSARestrictScalarsAlgebra F A
  letI : IsScalarTower (Polynomial F) (RatFunc F) A.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨O, e, r, a, n, s, hr, ha, hs, hfin, hsa, has⟩ :=
    rationalFunction_exists_singlePrincipalOpen_azumayaScalarExtensionModel_of_csa F A
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
  letI : Algebra U T :=
    (IsLocalization.Away.lift s
      (principalLocalization_numeratorRelation_map_isUnit (Polynomial F) r a n s hsa)).toAlgebra
  letI : IsAzumaya T (T ⊗[U] (U ⊗[S] (S ⊗[(Polynomial F)] O))) := has
  refine ⟨has,
    finite_twoPrincipalOpenAzumayaResidueBadHeightOnePrimes (Polynomial F) r a hr ha, ?_⟩
  intro P hP
  exact rationalFunction_twoPrincipalOpenAzumayaHeightOneResidueBrauerClass_eq_split_of_not_mem
    F P r a hP (T ⊗[U] (U ⊗[S] (S ⊗[(Polynomial F)] O)))

end

end GaloisForLFunctions.HTGeometry.ABHN
