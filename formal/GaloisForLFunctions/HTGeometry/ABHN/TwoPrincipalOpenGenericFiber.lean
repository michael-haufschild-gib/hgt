/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CSAOrderAzumayaLocus
import GaloisForLFunctions.HTGeometry.ABHN.TwoPrincipalOpenAzumayaTransport

/-!
# Generic fibers of two-principal Azumaya models

The Azumaya model used for finite residue support is obtained by three successive scalar
extensions. This file proves that all three extensions cancel after passing to any common generic
field. It supplies the algebraic provenance needed before a completed-local-field or
Connes/Tate specialization can compare the model with a source-side local algebra.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

noncomputable section

/-- The generic fiber of a two-principal scalar-extension model is the generic fiber of its
original order. The hypotheses deliberately expose the compatible maps to the common field: a
future local-completion comparison must prove exactly these tower compatibilities. -/
noncomputable def twoPrincipalOpen_scalarExtension_genericFiber_equiv
    {R S U T K O : Type*}
    [CommRing R] [CommRing S] [CommRing U] [CommRing T] [CommRing K]
    [Algebra R S] [Algebra S U] [Algebra U T]
    [Algebra R K] [Algebra S K] [Algebra U K] [Algebra T K]
    [IsScalarTower R S K] [IsScalarTower S U K] [IsScalarTower U T K]
    [Ring O] [Algebra R O] :
    letI : Semiring (S ⊗[R] O) :=
      Algebra.TensorProduct.instSemiring (R := R) (A := S) (B := O)
    letI : Semiring (U ⊗[S] (S ⊗[R] O)) :=
      Algebra.TensorProduct.instSemiring (R := S) (A := U) (B := S ⊗[R] O)
    letI : Semiring (T ⊗[U] (U ⊗[S] (S ⊗[R] O))) :=
      Algebra.TensorProduct.instSemiring (R := U) (A := T) (B := U ⊗[S] (S ⊗[R] O))
    letI : Semiring (K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O)))) :=
      Algebra.TensorProduct.instSemiring (R := T) (A := K)
        (B := T ⊗[U] (U ⊗[S] (S ⊗[R] O)))
    letI : Algebra K (K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O)))) :=
      Algebra.TensorProduct.leftAlgebra (R := T) (S := K) (A := K)
        (B := T ⊗[U] (U ⊗[S] (S ⊗[R] O)))
    K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O))) ≃ₐ[K] K ⊗[R] O := by
  letI : Semiring (S ⊗[R] O) :=
    Algebra.TensorProduct.instSemiring (R := R) (A := S) (B := O)
  letI : Semiring (U ⊗[S] (S ⊗[R] O)) :=
    Algebra.TensorProduct.instSemiring (R := S) (A := U) (B := S ⊗[R] O)
  letI : Semiring (T ⊗[U] (U ⊗[S] (S ⊗[R] O))) :=
    Algebra.TensorProduct.instSemiring (R := U) (A := T) (B := U ⊗[S] (S ⊗[R] O))
  letI : Semiring (K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O)))) :=
    Algebra.TensorProduct.instSemiring (R := T) (A := K)
      (B := T ⊗[U] (U ⊗[S] (S ⊗[R] O)))
  letI : Algebra K (K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O)))) :=
    Algebra.TensorProduct.leftAlgebra (R := T) (S := K) (A := K)
      (B := T ⊗[U] (U ⊗[S] (S ⊗[R] O)))
  exact (AzumayaScalarExtension.cancelBaseChangeNoncommutative
    (R := U) (S := T) (A := U ⊗[S] (S ⊗[R] O)) (T := K)).trans
      ((AzumayaScalarExtension.cancelBaseChangeNoncommutative
        (R := S) (S := U) (A := S ⊗[R] O) (T := K)).trans
          (AzumayaScalarExtension.cancelBaseChangeNoncommutative
            (R := R) (S := S) (A := O) (T := K)))

/-- A two-principal Azumaya model has the prescribed generic algebra whenever the original
order does. This is the form consumed by a future local-place comparison. -/
noncomputable def twoPrincipalOpen_scalarExtension_genericFiber_equiv_of_base_equiv
    {R S U T K O A : Type*}
    [CommRing R] [CommRing S] [CommRing U] [CommRing T] [CommRing K]
    [Algebra R S] [Algebra S U] [Algebra U T]
    [Algebra R K] [Algebra S K] [Algebra U K] [Algebra T K]
    [IsScalarTower R S K] [IsScalarTower S U K] [IsScalarTower U T K]
    [Ring O] [Algebra R O] [Ring A] [Algebra K A]
    (e : K ⊗[R] O ≃ₐ[K] A) :
    letI : Semiring (S ⊗[R] O) :=
      Algebra.TensorProduct.instSemiring (R := R) (A := S) (B := O)
    letI : Semiring (U ⊗[S] (S ⊗[R] O)) :=
      Algebra.TensorProduct.instSemiring (R := S) (A := U) (B := S ⊗[R] O)
    letI : Semiring (T ⊗[U] (U ⊗[S] (S ⊗[R] O))) :=
      Algebra.TensorProduct.instSemiring (R := U) (A := T) (B := U ⊗[S] (S ⊗[R] O))
    letI : Semiring (K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O)))) :=
      Algebra.TensorProduct.instSemiring (R := T) (A := K)
        (B := T ⊗[U] (U ⊗[S] (S ⊗[R] O)))
    letI : Algebra K (K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O)))) :=
      Algebra.TensorProduct.leftAlgebra (R := T) (S := K) (A := K)
        (B := T ⊗[U] (U ⊗[S] (S ⊗[R] O)))
    K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O))) ≃ₐ[K] A := by
  letI : Semiring (S ⊗[R] O) :=
    Algebra.TensorProduct.instSemiring (R := R) (A := S) (B := O)
  letI : Semiring (U ⊗[S] (S ⊗[R] O)) :=
    Algebra.TensorProduct.instSemiring (R := S) (A := U) (B := S ⊗[R] O)
  letI : Semiring (T ⊗[U] (U ⊗[S] (S ⊗[R] O))) :=
    Algebra.TensorProduct.instSemiring (R := U) (A := T) (B := U ⊗[S] (S ⊗[R] O))
  letI : Semiring (K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O)))) :=
    Algebra.TensorProduct.instSemiring (R := T) (A := K)
      (B := T ⊗[U] (U ⊗[S] (S ⊗[R] O)))
  letI : Algebra K (K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O)))) :=
    Algebra.TensorProduct.leftAlgebra (R := T) (S := K) (A := K)
      (B := T ⊗[U] (U ⊗[S] (S ⊗[R] O)))
  exact (twoPrincipalOpen_scalarExtension_genericFiber_equiv
    (R := R) (S := S) (U := U) (T := T) (K := K) (O := O)).trans e

/-
/-- The final one-principal transport map of a two-principal model commutes with the canonical
map to the fraction field. This is the map-level compatibility needed to retain the original
generic fiber after the final scalar extension. -/
theorem twoPrincipalOpen_fractionField_uToT_commutes
    (R : Type u) [CommRing R] [IsDomain R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (r a : R) (hr : r ≠ 0) (ha : a ≠ 0) (n : ℕ)
    (s : Localization (Submonoid.powers r)) (hs : s ≠ 0)
    (hsa : s * (algebraMap R (Localization (Submonoid.powers r)) r) ^ n =
      algebraMap R (Localization (Submonoid.powers r)) a) :
    let S := Localization (Submonoid.powers r)
    let T := Localization (Submonoid.powers (r * a))
    let U := Localization (Submonoid.powers s)
    let f : S →+* T := IsLocalization.Away.awayToAwayRight r a
    letI : IsDomain S :=
      IsLocalization.isDomain_of_le_nonZeroDivisors S
        (powers_le_nonZeroDivisors_of_noZeroDivisors hr)
    letI : Algebra S K :=
      IsLocalization.localizationAlgebraOfSubmonoidLe S K (Submonoid.powers r)
        (nonZeroDivisors R) (powers_le_nonZeroDivisors_of_noZeroDivisors hr)
    letI : IsScalarTower R S K :=
      IsLocalization.localization_isScalarTower_of_submonoid_le S K (Submonoid.powers r)
        (nonZeroDivisors R) (powers_le_nonZeroDivisors_of_noZeroDivisors hr)
    letI : IsFractionRing S K :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers r) S K
    letI : Algebra T K :=
      IsLocalization.localizationAlgebraOfSubmonoidLe T K (Submonoid.powers (r * a))
        (nonZeroDivisors R) (powers_le_nonZeroDivisors_of_noZeroDivisors (mul_ne_zero hr ha))
    letI : IsScalarTower R T K :=
      IsLocalization.localization_isScalarTower_of_submonoid_le T K (Submonoid.powers (r * a))
        (nonZeroDivisors R) (powers_le_nonZeroDivisors_of_noZeroDivisors (mul_ne_zero hr ha))
    letI : Algebra S U := inferInstance
    letI : Algebra S T := f.toAlgebra
    letI : Algebra U T :=
      (IsLocalization.Away.lift s
        (principalLocalization_numeratorRelation_map_isUnit R r a n s hsa)).toAlgebra
    letI : Algebra U K :=
      IsLocalization.localizationAlgebraOfSubmonoidLe U K (Submonoid.powers s)
        (nonZeroDivisors S) (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
    letI : IsScalarTower S U K :=
      IsLocalization.localization_isScalarTower_of_submonoid_le U K (Submonoid.powers s)
        (nonZeroDivisors S) (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
    (algebraMap T K).comp (algebraMap U T) = algebraMap U K := by
  let S := Localization (Submonoid.powers r)
  let T := Localization (Submonoid.powers (r * a))
  let U := Localization (Submonoid.powers s)
  let f : S →+* T := IsLocalization.Away.awayToAwayRight r a
  have hpowr : Submonoid.powers r ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hr
  have hpowra : Submonoid.powers (r * a) ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (mul_ne_zero hr ha)
  letI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hpowr
  letI : Algebra S K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe S K (Submonoid.powers r)
      (nonZeroDivisors R) hpowr
  letI : IsScalarTower R S K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le S K (Submonoid.powers r)
      (nonZeroDivisors R) hpowr
  letI : IsFractionRing S K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers r) S K
  letI : Algebra T K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe T K (Submonoid.powers (r * a))
      (nonZeroDivisors R) hpowra
  letI : IsScalarTower R T K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le T K (Submonoid.powers (r * a))
      (nonZeroDivisors R) hpowra
  letI : Algebra S U := inferInstance
  letI : Algebra S T := f.toAlgebra
  have hunit : IsUnit (f s) := by
    dsimp [f]
    exact principalLocalization_numeratorRelation_map_isUnit R r a n s hsa
  letI : Algebra U T := (IsLocalization.Away.lift s hunit).toAlgebra
  have hpows : Submonoid.powers s ≤ nonZeroDivisors S :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hs
  letI : Algebra U K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe U K (Submonoid.powers s)
      (nonZeroDivisors S) hpows
  letI : IsScalarTower S U K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le U K (Submonoid.powers s)
      (nonZeroDivisors S) hpows
  have hST : (algebraMap T K).comp (algebraMap S T) = algebraMap S K := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    apply RingHom.ext
    intro x
    change algebraMap T K (f (algebraMap R S x)) = algebraMap S K (algebraMap R S x)
    rw [IsLocalization.Away.awayToAwayRight_eq]
    simp
  apply IsLocalization.ringHom_ext (Submonoid.powers s)
  apply RingHom.ext
  intro x
  change algebraMap T K ((IsLocalization.Away.lift s hunit) (algebraMap S U x)) =
    algebraMap U K (algebraMap S U x)
  rw [IsLocalization.Away.lift_eq]
  rw [← RingHom.comp_apply, hST]
  exact (IsScalarTower.algebraMap_apply S U K x).symm
-/

/-- A fraction-field central simple algebra has a two-stage principal-open Azumaya model whose
generic fiber is again the original algebra. This records the non-residual provenance of the
model used in finite residue-support arguments; no completed-local-field or Brauer comparison is
asserted here. -/
theorem exists_iterated_principalOpen_isAzumayaModel_of_csa_with_genericFiber
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (A : CSA.{v, w} K) [Algebra R A.carrier] [IsScalarTower R K A.carrier] :
    ∃ (O : Subalgebra R A.carrier) (_ : K ⊗[R] O ≃ₐ[K] A.carrier) (r : R), ∃ hr : r ≠ 0,
      Module.Finite R O ∧ ∃ s : Localization (Submonoid.powers r), ∃ hs : s ≠ 0,
        let S := Localization (Submonoid.powers r)
        let U := Localization (Submonoid.powers s)
        letI : Algebra S U := inferInstance
        letI : IsDomain S :=
          IsLocalization.isDomain_of_le_nonZeroDivisors S
            (powers_le_nonZeroDivisors_of_noZeroDivisors hr)
        letI : Algebra S K :=
          IsLocalization.localizationAlgebraOfSubmonoidLe S K (Submonoid.powers r)
            (nonZeroDivisors R) (powers_le_nonZeroDivisors_of_noZeroDivisors hr)
        letI : IsScalarTower R S K :=
          IsLocalization.localization_isScalarTower_of_submonoid_le S K (Submonoid.powers r)
            (nonZeroDivisors R) (powers_le_nonZeroDivisors_of_noZeroDivisors hr)
        letI : IsFractionRing S K :=
          IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers r) S K
        letI : Algebra U K :=
          IsLocalization.localizationAlgebraOfSubmonoidLe U K (Submonoid.powers s)
            (nonZeroDivisors S) (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
        letI : IsScalarTower S U K :=
          IsLocalization.localization_isScalarTower_of_submonoid_le U K (Submonoid.powers s)
            (nonZeroDivisors S) (powers_le_nonZeroDivisors_of_noZeroDivisors hs)
        letI : Semiring (S ⊗[R] O) :=
          Algebra.TensorProduct.instSemiring (R := R) (A := S) (B := O)
        letI : Semiring (U ⊗[S] (S ⊗[R] O)) :=
          Algebra.TensorProduct.instSemiring (R := S) (A := U) (B := S ⊗[R] O)
        letI : Algebra U (U ⊗[S] (S ⊗[R] O)) :=
          Algebra.TensorProduct.leftAlgebra (R := S) (S := U) (A := U) (B := S ⊗[R] O)
        letI : Semiring (K ⊗[U] (U ⊗[S] (S ⊗[R] O))) :=
          Algebra.TensorProduct.instSemiring (R := U) (A := K) (B := U ⊗[S] (S ⊗[R] O))
        letI : Algebra K (K ⊗[U] (U ⊗[S] (S ⊗[R] O))) :=
          Algebra.TensorProduct.leftAlgebra (R := U) (S := K) (A := K)
            (B := U ⊗[S] (S ⊗[R] O))
        ∃ _ : K ⊗[U] (U ⊗[S] (S ⊗[R] O)) ≃ₐ[K] A.carrier,
          IsAzumaya U (U ⊗[S] (S ⊗[R] O)) := by
  obtain ⟨O, e, hfinite⟩ := exists_fractionFieldOrder_of_csa R K A
  letI : Module.Finite R O := hfinite
  letI : Module.FinitePresentation R O := Module.finitePresentation_of_finite R O
  obtain ⟨r, hr, hfree⟩ :=
    exists_nonzero_away_free_of_fractionField_baseChange R K O
  let S := Localization (Submonoid.powers r)
  have hpow : Submonoid.powers r ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hr
  letI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hpow
  letI : Algebra S K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe S K (Submonoid.powers r)
      (nonZeroDivisors R) hpow
  letI : IsScalarTower R S K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le S K (Submonoid.powers r)
      (nonZeroDivisors R) hpow
  letI : IsFractionRing S K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers r) S K
  letI : Module.Free S (LocalizedModule.Away r O) := hfree
  letI : Module.Free S (S ⊗[R] O) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers r) O)
  letI : Module.Finite S (S ⊗[R] O) := inferInstance
  have eS : K ⊗[S] (S ⊗[R] O) ≃ₐ[K] A.carrier :=
    (AzumayaScalarExtension.cancelBaseChangeNoncommutative
      (R := R) (S := S) (A := O) (T := K)).trans e
  obtain ⟨s, hs, hAz⟩ :=
    exists_nonzero_away_isAzumaya_of_fractionFieldModel_of_free S K A (S ⊗[R] O) eS
  refine ⟨O, e, r, hr, hfinite, s, hs, ?_⟩
  let U := Localization (Submonoid.powers s)
  letI : Algebra S U := inferInstance
  have hpows : Submonoid.powers s ≤ nonZeroDivisors S :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hs
  letI : Algebra U K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe U K (Submonoid.powers s)
      (nonZeroDivisors S) hpows
  letI : IsScalarTower S U K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le U K (Submonoid.powers s)
      (nonZeroDivisors S) hpows
  letI : Semiring (S ⊗[R] O) :=
    Algebra.TensorProduct.instSemiring (R := R) (A := S) (B := O)
  letI : Semiring (U ⊗[S] (S ⊗[R] O)) :=
    Algebra.TensorProduct.instSemiring (R := S) (A := U) (B := S ⊗[R] O)
  letI : Algebra U (U ⊗[S] (S ⊗[R] O)) :=
    Algebra.TensorProduct.leftAlgebra (R := S) (S := U) (A := U) (B := S ⊗[R] O)
  letI : Semiring (K ⊗[U] (U ⊗[S] (S ⊗[R] O))) :=
    Algebra.TensorProduct.instSemiring (R := U) (A := K) (B := U ⊗[S] (S ⊗[R] O))
  letI : Algebra K (K ⊗[U] (U ⊗[S] (S ⊗[R] O))) :=
    Algebra.TensorProduct.leftAlgebra (R := U) (S := K) (A := K)
      (B := U ⊗[S] (S ⊗[R] O))
  refine ⟨?_, hAz⟩
  exact (AzumayaScalarExtension.cancelBaseChangeNoncommutative
    (R := S) (S := U) (A := S ⊗[R] O) (T := K)).trans eS

end

end GaloisForLFunctions.HTGeometry.ABHN
