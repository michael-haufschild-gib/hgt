import GaloisForLFunctions.HTGeometry.ABHN.TwoPrincipalOpenAzumayaTransport

/-!
# Fraction-field compatibility for two-principal Azumaya transport

The final localization in the two-principal Azumaya construction is compatible with the
canonical map to the original fraction field.  This keeps the finite-residue model attached to
its original generic central simple algebra; it does not assert a completed-local-field or Brauer
comparison.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v

noncomputable section

/-- The final one-principal transport map of a two-principal model commutes with the canonical
map to the fraction field. -/
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
    rw [← IsScalarTower.algebraMap_apply R T K x]
    rw [← IsScalarTower.algebraMap_apply R S K x]
  apply IsLocalization.ringHom_ext (Submonoid.powers s)
  apply RingHom.ext
  intro x
  change algebraMap T K ((IsLocalization.Away.lift s hunit) (algebraMap S U x)) =
    algebraMap U K (algebraMap S U x)
  rw [IsLocalization.Away.lift_eq]
  change ((algebraMap T K).comp (algebraMap S T)) x =
    ((algebraMap U K).comp (algebraMap S U)) x
  rw [hST]
  simpa only [RingHom.comp_apply] using IsScalarTower.algebraMap_apply S U K x

end

end GaloisForLFunctions.HTGeometry.ABHN
