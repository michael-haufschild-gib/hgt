import GaloisForLFunctions.HTGeometry.ABHN.TwoPrincipalOpenGenericFiberCompatibility

/-!
# Final generic fiber of a two-principal Azumaya model

The canonical fraction-field maps commute with the final localization of a two-principal
Azumaya construction.  Consequently, scalar extension of the final model to the original
fraction field is the prescribed generic algebra.  This is model provenance for finite
ramification; it does not compare that generic fiber with a completed local Brauer class.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w

noncomputable section

/-- The final principal-localization model of an order has its prescribed fraction-field generic
fiber. -/
noncomputable def twoPrincipalOpen_finalFractionField_genericFiber_equiv
    (R : Type u) [CommRing R] [IsDomain R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (O : Type w) [Ring O] [Algebra R O]
    (A : Type w) [Ring A] [Algebra K A] (e : K ⊗[R] O ≃ₐ[K] A)
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
    letI : Semiring (S ⊗[R] O) :=
      Algebra.TensorProduct.instSemiring (R := R) (A := S) (B := O)
    letI : Semiring (U ⊗[S] (S ⊗[R] O)) :=
      Algebra.TensorProduct.instSemiring (R := S) (A := U) (B := S ⊗[R] O)
    letI : Semiring (T ⊗[U] (U ⊗[S] (S ⊗[R] O))) :=
      Algebra.TensorProduct.instSemiring (R := U) (A := T) (B := U ⊗[S] (S ⊗[R] O))
    letI : Algebra T (T ⊗[U] (U ⊗[S] (S ⊗[R] O))) :=
      Algebra.TensorProduct.leftAlgebra (R := U) (S := T) (A := T)
        (B := U ⊗[S] (S ⊗[R] O))
    letI : Semiring (K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O)))) :=
      Algebra.TensorProduct.instSemiring (R := T) (A := K)
        (B := T ⊗[U] (U ⊗[S] (S ⊗[R] O)))
    letI : Algebra K (K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O)))) :=
      Algebra.TensorProduct.leftAlgebra (R := T) (S := K) (A := K)
        (B := T ⊗[U] (U ⊗[S] (S ⊗[R] O)))
    K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O))) ≃ₐ[K] A := by
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
  letI : Semiring (S ⊗[R] O) :=
    Algebra.TensorProduct.instSemiring (R := R) (A := S) (B := O)
  letI : Semiring (U ⊗[S] (S ⊗[R] O)) :=
    Algebra.TensorProduct.instSemiring (R := S) (A := U) (B := S ⊗[R] O)
  letI : Semiring (T ⊗[U] (U ⊗[S] (S ⊗[R] O))) :=
    Algebra.TensorProduct.instSemiring (R := U) (A := T) (B := U ⊗[S] (S ⊗[R] O))
  letI : Algebra T (T ⊗[U] (U ⊗[S] (S ⊗[R] O))) :=
    Algebra.TensorProduct.leftAlgebra (R := U) (S := T) (A := T)
      (B := U ⊗[S] (S ⊗[R] O))
  letI : Semiring (K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O)))) :=
    Algebra.TensorProduct.instSemiring (R := T) (A := K)
      (B := T ⊗[U] (U ⊗[S] (S ⊗[R] O)))
  letI : Algebra K (K ⊗[T] (T ⊗[U] (U ⊗[S] (S ⊗[R] O)))) :=
    Algebra.TensorProduct.leftAlgebra (R := T) (S := K) (A := K)
      (B := T ⊗[U] (U ⊗[S] (S ⊗[R] O)))
  have hUTK : (algebraMap T K).comp (algebraMap U T) = algebraMap U K :=
    twoPrincipalOpen_fractionField_uToT_commutes R K r a hr ha n s hs hsa
  exact twoPrincipalOpen_scalarExtension_genericFiber_equiv_of_map_commutes hUTK e

end

end GaloisForLFunctions.HTGeometry.ABHN
