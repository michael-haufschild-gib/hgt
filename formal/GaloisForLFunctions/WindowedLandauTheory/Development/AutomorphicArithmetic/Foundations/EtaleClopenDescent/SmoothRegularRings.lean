import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Ideal.GoingDown

/-! Smooth algebras over regular rings are regular. -/

noncomputable section

namespace GlobalTheory.SchemeCohomology

open IsLocalRing

private theorem regularLocalRing_of_etale (A B : Type) [CommRing A] [IsRegularRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : Ideal B) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let p := q.under A
  letI : p.IsPrime := Ideal.IsPrime.under A q
  letI : q.LiesOver p := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver p q
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  haveI : IsRegularLocalRing (Localization.AtPrime p) := inferInstance
  have hm : p.map (algebraMap A (Localization.AtPrime q)) = maximalIdeal (Localization.AtPrime q) :=
    ((Algebra.isUnramifiedAt_iff_map_eq A p q).mp inferInstance).2
  have hmap : maximalIdeal (Localization.AtPrime q) =
      (maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    rw [← hm, ← IsLocalization.AtPrime.map_eq_maximalIdeal p, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  have hgen : (maximalIdeal (Localization.AtPrime q)).spanFinrank ≤
      (maximalIdeal (Localization.AtPrime p)).spanFinrank := by
    rw [hmap]
    exact Ideal.spanFinrank_map_le_of_fg _ (maximalIdeal _).fg_of_isNoetherianRing
  have hht : p.height ≤ q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q]
    exact le_self_add
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc
    ((maximalIdeal (Localization.AtPrime q)).spanFinrank : WithBot ℕ∞) ≤
        ((maximalIdeal (Localization.AtPrime p)).spanFinrank : WithBot ℕ∞) := by exact_mod_cast hgen
    _ = ringKrullDim (Localization.AtPrime p) := IsRegularLocalRing.spanFinrank_maximalIdeal
    _ = (p.height : WithBot ℕ∞) := IsLocalization.AtPrime.ringKrullDim_eq_height p _
    _ ≤ (q.height : WithBot ℕ∞) := by exact_mod_cast hht
    _ = ringKrullDim (Localization.AtPrime q) := (IsLocalization.AtPrime.ringKrullDim_eq_height q _).symm

/-- Regularity ascends along étale morphisms. -/
theorem isRegularRing_of_etale (A B : Type) [CommRing A] [IsRegularRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] : IsRegularRing B := by
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  exact isRegularRing_iff.mpr fun q _ => regularLocalRing_of_etale A B q

/-- Regularity ascends along smooth morphisms, using local étale
coordinates over a polynomial algebra. -/
theorem isRegularRing_of_smooth (A B : Type) [CommRing A] [IsRegularRing A]
    [CommRing B] [Algebra A B] [Algebra.Smooth A B] : IsRegularRing B := by
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  refine isRegularRing_iff.mpr fun q _ => ?_
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := q)
  let T := Localization.Away f
  letI : IsRegularRing T := isRegularRing_of_etale (MvPolynomial (Fin n) A) T
  have hd : Disjoint (Submonoid.powers f : Set B) (q : Set B) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
  let q' := Ideal.map (algebraMap B T) q
  letI : q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers f) T q inferInstance hd
  have hc : q'.comap (algebraMap B T) = q :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers f) T inferInstance hd
  have hl := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (.powers f) (Localization.AtPrime q') q'
  letI : IsLocalization.AtPrime (Localization.AtPrime q') q := by
    simpa only [Ideal.under, hc] using hl
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv q.primeCompl
    (Localization.AtPrime q') (Localization.AtPrime q)).toRingEquiv

end GlobalTheory.SchemeCohomology
