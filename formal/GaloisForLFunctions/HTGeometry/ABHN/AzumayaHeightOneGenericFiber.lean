import GaloisForLFunctions.HTGeometry.ABHN.AzumayaHeightOneValuationSubring
import GaloisForLFunctions.HTGeometry.ABHN.TwoPrincipalOpenGenericFiber

/-!
# Generic fibers at height-one localizations

Localizing a final principal-open Azumaya model at a height-one prime away from its numerator
does not change its fraction-field generic fiber.  Together with the split residue-fiber result,
this supplies the full uncompleted valuation-ring model needed by the Henselian Brauer comparison
in the local ABHN bridge.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct
open IsDedekindDomain

universe u

noncomputable section

/-- The generic fiber of a principal-open model is unchanged after localization at a height-one
prime away from the inverted numerator. -/
noncomputable def localizationAtHeightOne_genericFiber_equiv
    (R : Type u) [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (P : HeightOneSpectrum R) (d : R) (hd : d ∉ P.asIdeal)
    (B : Type u) [Ring B] [Algebra (Localization (Submonoid.powers d)) B] :
    let T := Localization (Submonoid.powers d)
    let Q := Localization.AtPrime P.asIdeal
    let f : T →+* Q := IsLocalization.Away.lift d
      (IsLocalization.map_units Q ⟨d, show d ∈ P.asIdeal.primeCompl from hd⟩)
    letI : Algebra T K :=
      IsLocalization.localizationAlgebraOfSubmonoidLe T K (Submonoid.powers d)
        (nonZeroDivisors R) (powers_le_nonZeroDivisors_of_noZeroDivisors (by
          intro hzero
          apply hd
          rw [hzero]
          exact P.asIdeal.zero_mem))
    letI : IsScalarTower R T K :=
      IsLocalization.localization_isScalarTower_of_submonoid_le T K (Submonoid.powers d)
        (nonZeroDivisors R) (powers_le_nonZeroDivisors_of_noZeroDivisors (by
          intro hzero
          apply hd
          rw [hzero]
          exact P.asIdeal.zero_mem))
    letI : Algebra Q K :=
      IsLocalization.localizationAlgebraOfSubmonoidLe Q K P.asIdeal.primeCompl
        (nonZeroDivisors R) P.asIdeal.primeCompl_le_nonZeroDivisors
    letI : IsScalarTower R Q K :=
      IsLocalization.localization_isScalarTower_of_submonoid_le Q K P.asIdeal.primeCompl
        (nonZeroDivisors R) P.asIdeal.primeCompl_le_nonZeroDivisors
    letI : Algebra T Q := f.toAlgebra
    letI : IsScalarTower T Q K := by
      apply IsScalarTower.of_algebraMap_eq'
      apply Eq.symm
      apply IsLocalization.ringHom_ext (Submonoid.powers d)
      apply RingHom.ext
      intro x
      change algebraMap Q K (f (algebraMap R T x)) = algebraMap T K (algebraMap R T x)
      rw [IsLocalization.Away.lift_eq]
      rw [← IsScalarTower.algebraMap_apply R Q K x]
      rw [← IsScalarTower.algebraMap_apply R T K x]
    letI : Semiring (Q ⊗[T] B) :=
      Algebra.TensorProduct.instSemiring (R := T) (A := Q) (B := B)
    letI : Algebra Q (Q ⊗[T] B) :=
      Algebra.TensorProduct.leftAlgebra (R := T) (S := Q) (A := Q) (B := B)
    letI : Semiring (K ⊗[Q] (Q ⊗[T] B)) :=
      Algebra.TensorProduct.instSemiring (R := Q) (A := K) (B := Q ⊗[T] B)
    letI : Algebra K (K ⊗[Q] (Q ⊗[T] B)) :=
      Algebra.TensorProduct.leftAlgebra (R := Q) (S := K) (A := K) (B := Q ⊗[T] B)
    letI : Semiring (K ⊗[T] B) :=
      Algebra.TensorProduct.instSemiring (R := T) (A := K) (B := B)
    letI : Algebra K (K ⊗[T] B) :=
      Algebra.TensorProduct.leftAlgebra (R := T) (S := K) (A := K) (B := B)
    K ⊗[Q] (Q ⊗[T] B) ≃ₐ[K] K ⊗[T] B := by
  let T := Localization (Submonoid.powers d)
  let Q := Localization.AtPrime P.asIdeal
  have hdne : d ≠ 0 := by
    intro hzero
    apply hd
    rw [hzero]
    exact P.asIdeal.zero_mem
  have hpowd : Submonoid.powers d ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hdne
  letI : Algebra T K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe T K (Submonoid.powers d)
      (nonZeroDivisors R) hpowd
  letI : IsScalarTower R T K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le T K (Submonoid.powers d)
      (nonZeroDivisors R) hpowd
  letI : Algebra Q K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe Q K P.asIdeal.primeCompl
      (nonZeroDivisors R) P.asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsScalarTower R Q K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le Q K P.asIdeal.primeCompl
      (nonZeroDivisors R) P.asIdeal.primeCompl_le_nonZeroDivisors
  have hunit : IsUnit (algebraMap R Q d) :=
    IsLocalization.map_units Q ⟨d, show d ∈ P.asIdeal.primeCompl from hd⟩
  let f : T →+* Q := IsLocalization.Away.lift d hunit
  letI : Algebra T Q := f.toAlgebra
  letI : IsScalarTower T Q K := by
    apply IsScalarTower.of_algebraMap_eq'
    apply Eq.symm
    apply IsLocalization.ringHom_ext (Submonoid.powers d)
    apply RingHom.ext
    intro x
    change algebraMap Q K (f (algebraMap R T x)) = algebraMap T K (algebraMap R T x)
    rw [IsLocalization.Away.lift_eq]
    rw [← IsScalarTower.algebraMap_apply R Q K x]
    rw [← IsScalarTower.algebraMap_apply R T K x]
  letI : Semiring (Q ⊗[T] B) :=
    Algebra.TensorProduct.instSemiring (R := T) (A := Q) (B := B)
  letI : Algebra Q (Q ⊗[T] B) :=
    Algebra.TensorProduct.leftAlgebra (R := T) (S := Q) (A := Q) (B := B)
  letI : Semiring (K ⊗[Q] (Q ⊗[T] B)) :=
    Algebra.TensorProduct.instSemiring (R := Q) (A := K) (B := Q ⊗[T] B)
  letI : Algebra K (K ⊗[Q] (Q ⊗[T] B)) :=
    Algebra.TensorProduct.leftAlgebra (R := Q) (S := K) (A := K) (B := Q ⊗[T] B)
  letI : Semiring (K ⊗[T] B) :=
    Algebra.TensorProduct.instSemiring (R := T) (A := K) (B := B)
  letI : Algebra K (K ⊗[T] B) :=
    Algebra.TensorProduct.leftAlgebra (R := T) (S := K) (A := K) (B := B)
  exact AzumayaScalarExtension.cancelBaseChangeNoncommutative
    (R := T) (S := Q) (A := B) (T := K)

end

/-- After transport to the height-one valuation subring, the local Azumaya model still has the
same fraction-field generic fiber.  This is the generic-fiber counterpart of the valuation-ring
residue model; it deliberately stops before the unavailable Henselian Brauer comparison. -/
noncomputable def valuationSubringAtHeightOne_genericFiber_equiv
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (P : HeightOneSpectrum R) (d : R) (hd : d ∉ P.asIdeal)
    (B : Type u) [Ring B] [Algebra (Localization (Submonoid.powers d)) B] :
    let T := Localization (Submonoid.powers d)
    let Q := Localization.AtPrime P.asIdeal
    let W := ((P.valuation K).valuationSubring)
    let f : T →+* Q := IsLocalization.Away.lift d
      (IsLocalization.map_units Q ⟨d, show d ∈ P.asIdeal.primeCompl from hd⟩)
    letI : Algebra T K :=
      IsLocalization.localizationAlgebraOfSubmonoidLe T K (Submonoid.powers d)
        (nonZeroDivisors R) (powers_le_nonZeroDivisors_of_noZeroDivisors (by
          intro hzero
          apply hd
          rw [hzero]
          exact P.asIdeal.zero_mem))
    letI : IsScalarTower R T K :=
      IsLocalization.localization_isScalarTower_of_submonoid_le T K (Submonoid.powers d)
        (nonZeroDivisors R) (powers_le_nonZeroDivisors_of_noZeroDivisors (by
          intro hzero
          apply hd
          rw [hzero]
          exact P.asIdeal.zero_mem))
    letI : Algebra Q K :=
      IsLocalization.localizationAlgebraOfSubmonoidLe Q K P.asIdeal.primeCompl
        (nonZeroDivisors R) P.asIdeal.primeCompl_le_nonZeroDivisors
    letI : IsScalarTower R Q K :=
      IsLocalization.localization_isScalarTower_of_submonoid_le Q K P.asIdeal.primeCompl
        (nonZeroDivisors R) P.asIdeal.primeCompl_le_nonZeroDivisors
    letI : Algebra T Q := f.toAlgebra
    letI : IsScalarTower T Q K := by
      apply IsScalarTower.of_algebraMap_eq'
      apply Eq.symm
      apply IsLocalization.ringHom_ext (Submonoid.powers d)
      apply RingHom.ext
      intro x
      change algebraMap Q K (f (algebraMap R T x)) = algebraMap T K (algebraMap R T x)
      rw [IsLocalization.Away.lift_eq]
      rw [← IsScalarTower.algebraMap_apply R Q K x]
      rw [← IsScalarTower.algebraMap_apply R T K x]
    letI : Semiring (Q ⊗[T] B) :=
      Algebra.TensorProduct.instSemiring (R := T) (A := Q) (B := B)
    letI : Algebra Q (Q ⊗[T] B) :=
      Algebra.TensorProduct.leftAlgebra (R := T) (S := Q) (A := Q) (B := B)
    let e : Q ≃+* W :=
      (GaloisForLFunctions.HTGeometry.placeLocalizationAlgEquiv K P).toRingEquiv.trans
        (GaloisForLFunctions.HTGeometry.placeValuationSubringCongr K P)
    letI : Algebra Q W := e.toRingHom.toAlgebra
    letI : IsScalarTower Q W K := by
      apply IsScalarTower.of_algebraMap_eq'
      apply Eq.symm
      apply IsLocalization.ringHom_ext P.asIdeal.primeCompl
      apply RingHom.ext
      intro x
      change (algebraMap W K) (e (algebraMap R Q x)) =
        algebraMap Q K (algebraMap R Q x)
      rw [← IsScalarTower.algebraMap_apply R Q K x]
      change ((GaloisForLFunctions.HTGeometry.placeValuationSubringCongr K P
          ((GaloisForLFunctions.HTGeometry.placeLocalizationAlgEquiv K P)
            (algebraMap R Q x)) : W) : K) = algebraMap R K x
      rw [GaloisForLFunctions.HTGeometry.placeValuationSubringCongr_coe]
      rw [AlgEquiv.commutes]
      rfl
    letI : Semiring (W ⊗[Q] (Q ⊗[T] B)) :=
      Algebra.TensorProduct.instSemiring (R := Q) (A := W) (B := Q ⊗[T] B)
    letI : Algebra W (W ⊗[Q] (Q ⊗[T] B)) :=
      Algebra.TensorProduct.leftAlgebra (R := Q) (S := W) (A := W) (B := Q ⊗[T] B)
    letI : Semiring (K ⊗[W] (W ⊗[Q] (Q ⊗[T] B))) :=
      Algebra.TensorProduct.instSemiring (R := W) (A := K) (B := W ⊗[Q] (Q ⊗[T] B))
    letI : Algebra K (K ⊗[W] (W ⊗[Q] (Q ⊗[T] B))) :=
      Algebra.TensorProduct.leftAlgebra (R := W) (S := K) (A := K)
        (B := W ⊗[Q] (Q ⊗[T] B))
    letI : Semiring (K ⊗[T] B) :=
      Algebra.TensorProduct.instSemiring (R := T) (A := K) (B := B)
    letI : Algebra K (K ⊗[T] B) :=
      Algebra.TensorProduct.leftAlgebra (R := T) (S := K) (A := K) (B := B)
    K ⊗[W] (W ⊗[Q] (Q ⊗[T] B)) ≃ₐ[K] K ⊗[T] B := by
  let T := Localization (Submonoid.powers d)
  let Q := Localization.AtPrime P.asIdeal
  let W := ((P.valuation K).valuationSubring)
  have hdne : d ≠ 0 := by
    intro hzero
    apply hd
    rw [hzero]
    exact P.asIdeal.zero_mem
  have hpowd : Submonoid.powers d ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hdne
  letI : Algebra T K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe T K (Submonoid.powers d)
      (nonZeroDivisors R) hpowd
  letI : IsScalarTower R T K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le T K (Submonoid.powers d)
      (nonZeroDivisors R) hpowd
  letI : Algebra Q K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe Q K P.asIdeal.primeCompl
      (nonZeroDivisors R) P.asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsScalarTower R Q K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le Q K P.asIdeal.primeCompl
      (nonZeroDivisors R) P.asIdeal.primeCompl_le_nonZeroDivisors
  have hunit : IsUnit (algebraMap R Q d) :=
    IsLocalization.map_units Q ⟨d, show d ∈ P.asIdeal.primeCompl from hd⟩
  let f : T →+* Q := IsLocalization.Away.lift d hunit
  letI : Algebra T Q := f.toAlgebra
  letI : IsScalarTower T Q K := by
    apply IsScalarTower.of_algebraMap_eq'
    apply Eq.symm
    apply IsLocalization.ringHom_ext (Submonoid.powers d)
    apply RingHom.ext
    intro x
    change algebraMap Q K (f (algebraMap R T x)) = algebraMap T K (algebraMap R T x)
    rw [IsLocalization.Away.lift_eq]
    rw [← IsScalarTower.algebraMap_apply R Q K x]
    rw [← IsScalarTower.algebraMap_apply R T K x]
  letI : Semiring (Q ⊗[T] B) :=
    Algebra.TensorProduct.instSemiring (R := T) (A := Q) (B := B)
  letI : Algebra Q (Q ⊗[T] B) :=
    Algebra.TensorProduct.leftAlgebra (R := T) (S := Q) (A := Q) (B := B)
  let e : Q ≃+* W :=
    (GaloisForLFunctions.HTGeometry.placeLocalizationAlgEquiv K P).toRingEquiv.trans
      (GaloisForLFunctions.HTGeometry.placeValuationSubringCongr K P)
  letI : Algebra Q W := e.toRingHom.toAlgebra
  letI : IsScalarTower Q W K := by
    apply IsScalarTower.of_algebraMap_eq'
    apply Eq.symm
    apply IsLocalization.ringHom_ext P.asIdeal.primeCompl
    apply RingHom.ext
    intro x
    change (algebraMap W K) (e (algebraMap R Q x)) =
      algebraMap Q K (algebraMap R Q x)
    rw [← IsScalarTower.algebraMap_apply R Q K x]
    change ((GaloisForLFunctions.HTGeometry.placeValuationSubringCongr K P
        ((GaloisForLFunctions.HTGeometry.placeLocalizationAlgEquiv K P)
          (algebraMap R Q x)) : W) : K) = algebraMap R K x
    rw [GaloisForLFunctions.HTGeometry.placeValuationSubringCongr_coe]
    rw [AlgEquiv.commutes]
    rfl
  letI : Semiring (W ⊗[Q] (Q ⊗[T] B)) :=
    Algebra.TensorProduct.instSemiring (R := Q) (A := W) (B := Q ⊗[T] B)
  letI : Algebra W (W ⊗[Q] (Q ⊗[T] B)) :=
    Algebra.TensorProduct.leftAlgebra (R := Q) (S := W) (A := W) (B := Q ⊗[T] B)
  letI : Semiring (K ⊗[W] (W ⊗[Q] (Q ⊗[T] B))) :=
    Algebra.TensorProduct.instSemiring (R := W) (A := K) (B := W ⊗[Q] (Q ⊗[T] B))
  letI : Algebra K (K ⊗[W] (W ⊗[Q] (Q ⊗[T] B))) :=
    Algebra.TensorProduct.leftAlgebra (R := W) (S := K) (A := K)
      (B := W ⊗[Q] (Q ⊗[T] B))
  letI : Semiring (K ⊗[T] B) :=
    Algebra.TensorProduct.instSemiring (R := T) (A := K) (B := B)
  letI : Algebra K (K ⊗[T] B) :=
    Algebra.TensorProduct.leftAlgebra (R := T) (S := K) (A := K) (B := B)
  exact (AzumayaScalarExtension.cancelBaseChangeNoncommutative
    (R := Q) (S := W) (A := Q ⊗[T] B) (T := K)).trans
      (localizationAtHeightOne_genericFiber_equiv R K P d hd B)

end GaloisForLFunctions.HTGeometry.ABHN
