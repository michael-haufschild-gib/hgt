import GaloisForLFunctions.HTGeometry.FiniteFreeUfdPurity
import GaloisForLFunctions.HTGeometry.FormallyUnramifiedLocalGlobal
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization

/-!
# Purity of the branch locus for finite flat algebras over a Noetherian UFD

Let `A` be a Noetherian unique factorization domain and `A ⊆ B` a finite flat extension of domains.
This module proves that `B` is formally unramified over `A` as soon as it is formally unramified
generically and at every height-one prime of `A`. The proof checks unramifiedness at each maximal
ideal `m`: the localization `B_m` is free over the local ring `A_m`, its discriminant is nonzero by
the generic hypothesis, and a prime factor `q` of a non-unit discriminant in the UFD `A_m`
contracts to a height-one prime `P` of `A`, where the local hypothesis forces `q` to be a unit.

## Main results

- `formallyUnramified_of_flat_fraction_formallyUnramified_of_height_one_localizations`: for a finite
  flat extension of domains `A ⊆ B` with `A` a Noetherian UFD, formal unramifiedness of the generic
  fibre and of `B_P` over `A_P` for every height-one prime `P` implies `B` is formally unramified
  over `A`.

## Hypotheses

No analytic inputs. The main theorem is an implication whose substantive algebraic hypotheses are:
formal unramifiedness of the generic fibre `Localization (algebraMapSubmonoid B A⁰)` over
`FractionRing A` (an instance argument), and `hprime`: formal unramifiedness of `B_P` over `A_P`
for every prime `P` of height one.
-/

open scoped TensorProduct

namespace Algebra

open nonZeroDivisors

universe u v

/-- Purity of the branch locus over a Noetherian UFD `A`: a finite flat extension of domains
`A ⊆ B` is formally unramified, assuming its generic fibre is formally unramified over `Frac A` and
(`hprime`) `B_P` is formally unramified over `A_P` for every height-one prime `P`. -/
theorem formallyUnramified_of_flat_fraction_formallyUnramified_of_height_one_localizations
    {A : Type u} {B : Type v} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] [IsNoetherianRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B]
    [Module.Flat A B] [Module.Finite A B]
    [FormallyUnramified (FractionRing A)
      (Localization (Algebra.algebraMapSubmonoid B A⁰))]
    (hprime : ∀ (P : Ideal A) [P.IsPrime], P.height = 1 →
      FormallyUnramified
        (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid B P.primeCompl))) :
    FormallyUnramified A B := by
  classical
  apply formallyUnramified_of_localization_maximal
  intro m hm
  letI : m.IsMaximal := hm
  let Ap := Localization.AtPrime m
  let Bp := Localization (Algebra.algebraMapSubmonoid B m.primeCompl)
  haveI : Module.Flat A Bp := inferInstance
  letI : Module.Flat Ap Bp :=
    (Module.flat_iff_of_isLocalization Ap m.primeCompl Bp).mpr inferInstance
  letI : Module.Free Ap Bp := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis Ap Bp
  let ι := Module.Free.ChooseBasisIndex Ap Bp
  letI : Fintype ι := Fintype.ofFinite ι
  letI : DecidableEq ι := Classical.decEq ι
  have hdiscr : discr Ap b ≠ 0 := by
    let F := FractionRing A
    let BF := Localization (Algebra.algebraMapSubmonoid B A⁰)
    have hsub : m.primeCompl ≤ A⁰ := by
      intro x hx
      rw [mem_nonZeroDivisors_iff_ne_zero]
      intro hzero
      apply hx
      simpa [hzero] using m.zero_mem
    letI : Algebra Ap F :=
      IsLocalization.localizationAlgebraOfSubmonoidLe Ap F m.primeCompl A⁰ hsub
    letI : IsScalarTower A Ap F :=
      IsLocalization.localization_isScalarTower_of_submonoid_le Ap F
        m.primeCompl A⁰ hsub
    have hsubB : Algebra.algebraMapSubmonoid B m.primeCompl ≤
        Algebra.algebraMapSubmonoid B A⁰ := Set.image_mono hsub
    letI : Algebra Bp BF :=
      IsLocalization.localizationAlgebraOfSubmonoidLe Bp BF
        (Algebra.algebraMapSubmonoid B m.primeCompl)
        (Algebra.algebraMapSubmonoid B A⁰) hsubB
    letI : IsScalarTower B Bp BF :=
      IsLocalization.localization_isScalarTower_of_submonoid_le Bp BF
        (Algebra.algebraMapSubmonoid B m.primeCompl)
        (Algebra.algebraMapSubmonoid B A⁰) hsubB
    letI : IsScalarTower A Bp BF := IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply A B Bp,
        ← IsScalarTower.algebraMap_apply B Bp BF]
      rfl
    letI : Algebra Ap BF :=
      ((algebraMap F BF).comp (algebraMap Ap F)).toAlgebra
    letI : IsScalarTower Ap F BF := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower A Ap BF := IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap A BF x =
        algebraMap F BF (algebraMap Ap F (algebraMap A Ap x))
      rw [← IsScalarTower.algebraMap_apply A Ap F,
        IsScalarTower.algebraMap_apply A F BF]
    have hApBp : (algebraMap Bp BF).comp (algebraMap Ap Bp) = algebraMap Ap BF := by
      apply IsLocalization.ringHom_ext m.primeCompl
      apply RingHom.ext
      intro x
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← IsScalarTower.algebraMap_apply A Ap Bp,
        ← IsScalarTower.algebraMap_apply A Bp BF,
        ← IsScalarTower.algebraMap_apply A Ap BF]
    letI : IsScalarTower Ap Bp BF :=
      IsScalarTower.of_algebraMap_eq fun x => (DFunLike.congr_fun hApBp x).symm
    let T : Submonoid Ap := A⁰.map (algebraMap A Ap)
    letI : IsLocalization T F :=
      IsLocalization.isLocalization_of_submonoid_le Ap F
        m.primeCompl A⁰ hsub
    have hlocBF0 : IsLocalization
        ((Algebra.algebraMapSubmonoid B A⁰).map (algebraMap B Bp)) BF :=
      IsLocalization.isLocalization_of_submonoid_le Bp BF
        (Algebra.algebraMapSubmonoid B m.primeCompl)
        (Algebra.algebraMapSubmonoid B A⁰) hsubB
    have hmonoid : Algebra.algebraMapSubmonoid Bp T =
        (Algebra.algebraMapSubmonoid B A⁰).map (algebraMap B Bp) := by
      ext z
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨algebraMap A B a, ⟨a, ha, rfl⟩, by
          rw [← IsScalarTower.algebraMap_apply A Ap Bp,
            ← IsScalarTower.algebraMap_apply A B Bp]⟩
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨algebraMap A Ap a, ⟨a, ha, rfl⟩, by
          rw [← IsScalarTower.algebraMap_apply A B Bp,
            ← IsScalarTower.algebraMap_apply A Ap Bp]⟩
    letI : IsLocalization (Algebra.algebraMapSubmonoid Bp T) BF :=
      hmonoid ▸ hlocBF0
    let bF : Module.Basis ι F BF := b.localizationLocalization F T BF
    letI : Module.Free F BF := Module.Free.of_basis bF
    have hunit : IsUnit (discr F bF) := isUnit_discr_of_formallyUnramified bF
    have hbase : discr F bF = algebraMap Ap F (discr Ap b) := by
      exact discr_localizationLocalization Ap T BF b
    intro hzero
    rw [hbase, hzero, map_zero] at hunit
    exact not_isUnit_zero hunit
  apply formallyUnramified_of_isUnit_discr b
  by_contra hunit
  obtain ⟨q, hqirreducible, hqdiv⟩ :=
    WfDvdMonoid.exists_irreducible_factor hunit hdiscr
  have hqprime : Prime q :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hqirreducible
  let Q : Ideal Ap := Ideal.span {q}
  letI hQ : Q.IsPrime := by
    dsimp only [Q]
    exact (Ideal.span_singleton_prime hqprime.ne_zero).mpr hqprime
  let P : Ideal A := Q.under A
  letI hP : P.IsPrime := Ideal.IsPrime.under A Q
  have hPheight : P.height = 1 := by
    change (Q.under A).height = 1
    rw [IsLocalization.height_under m.primeCompl]
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hqprime.ne_zero) hqprime.not_unit
  let AP := Localization.AtPrime P
  let BP := Localization (Algebra.algebraMapSubmonoid B P.primeCompl)
  letI : Algebra AP BP := localizationAlgebra P.primeCompl B
  letI : IsScalarTower A AP BP :=
    isScalarTower_localizationAlgebra P.primeCompl B
  haveI hfu : FormallyUnramified AP BP := hprime P hPheight
  have hPm : P ≤ m := by
    exact (IsLocalization.AtPrime.orderIsoOfPrime Ap m ⟨Q, hQ⟩).property.2
  have hsub : m.primeCompl ≤ P.primeCompl := by
    intro x hx hxp
    exact hx (hPm hxp)
  letI : Algebra Ap AP :=
    IsLocalization.localizationAlgebraOfSubmonoidLe Ap AP
      m.primeCompl P.primeCompl hsub
  letI : IsScalarTower A Ap AP :=
    IsLocalization.localization_isScalarTower_of_submonoid_le Ap AP
      m.primeCompl P.primeCompl hsub
  have hsubB : Algebra.algebraMapSubmonoid B m.primeCompl ≤
      Algebra.algebraMapSubmonoid B P.primeCompl := Set.image_mono hsub
  letI : Algebra Bp BP :=
    IsLocalization.localizationAlgebraOfSubmonoidLe Bp BP
      (Algebra.algebraMapSubmonoid B m.primeCompl)
      (Algebra.algebraMapSubmonoid B P.primeCompl) hsubB
  letI : IsScalarTower B Bp BP :=
    IsLocalization.localization_isScalarTower_of_submonoid_le Bp BP
      (Algebra.algebraMapSubmonoid B m.primeCompl)
      (Algebra.algebraMapSubmonoid B P.primeCompl) hsubB
  letI : IsScalarTower A Bp BP := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply A B Bp,
      ← IsScalarTower.algebraMap_apply B Bp BP]
    rfl
  letI : Algebra Ap BP :=
    ((algebraMap AP BP).comp (algebraMap Ap AP)).toAlgebra
  letI : IsScalarTower Ap AP BP := IsScalarTower.of_algebraMap_eq' rfl
  have hApBp : (algebraMap Bp BP).comp (algebraMap Ap Bp) = algebraMap Ap BP := by
    apply IsLocalization.ringHom_ext m.primeCompl
    apply RingHom.ext
    intro x
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← IsScalarTower.algebraMap_apply A Ap Bp,
      ← IsScalarTower.algebraMap_apply A Bp BP]
    change algebraMap A BP x =
      algebraMap AP BP (algebraMap Ap AP (algebraMap A Ap x))
    rw [← IsScalarTower.algebraMap_apply A Ap AP,
      ← IsScalarTower.algebraMap_apply A AP BP]
  letI : IsScalarTower Ap Bp BP :=
    IsScalarTower.of_algebraMap_eq fun x => (DFunLike.congr_fun hApBp x).symm
  let T : Submonoid Ap := P.primeCompl.map (algebraMap A Ap)
  letI : IsLocalization T AP :=
    IsLocalization.isLocalization_of_submonoid_le Ap AP
      m.primeCompl P.primeCompl hsub
  have hlocBP0 : IsLocalization
      ((Algebra.algebraMapSubmonoid B P.primeCompl).map (algebraMap B Bp)) BP :=
    IsLocalization.isLocalization_of_submonoid_le Bp BP
      (Algebra.algebraMapSubmonoid B m.primeCompl)
      (Algebra.algebraMapSubmonoid B P.primeCompl) hsubB
  have hmonoid : Algebra.algebraMapSubmonoid Bp T =
      (Algebra.algebraMapSubmonoid B P.primeCompl).map (algebraMap B Bp) := by
    ext z
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨algebraMap A B a, ⟨a, ha, rfl⟩, by
        rw [← IsScalarTower.algebraMap_apply A Ap Bp,
          ← IsScalarTower.algebraMap_apply A B Bp]⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨algebraMap A Ap a, ⟨a, ha, rfl⟩, by
        rw [← IsScalarTower.algebraMap_apply A B Bp,
          ← IsScalarTower.algebraMap_apply A Ap Bp]⟩
  letI : IsLocalization (Algebra.algebraMapSubmonoid Bp T) BP :=
    hmonoid ▸ hlocBP0
  let bP : Module.Basis ι AP BP := b.localizationLocalization AP T BP
  letI : Module.Free AP BP := Module.Free.of_basis bP
  have hbPunit : IsUnit (discr AP bP) := isUnit_discr_of_formallyUnramified bP
  have hbase : discr AP bP = algebraMap Ap AP (discr Ap b) := by
    exact discr_localizationLocalization Ap T BP b
  rw [hbase] at hbPunit
  obtain ⟨c, hc⟩ := hqdiv
  have hqmapunit : IsUnit (algebraMap Ap AP q) := by
    rw [hc, map_mul, IsUnit.mul_iff] at hbPunit
    exact hbPunit.1
  have hTQ : T ≤ Q.primeCompl := by
    rintro _ ⟨a, ha, rfl⟩ hmem
    exact ha hmem
  have hQT : ∀ y ∈ Q.primeCompl, ∃ t ∈ T, y ∣ t := by
    intro y hy
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj m.primeCompl y
    have ha : a ∉ P := by
      intro haP
      have hmapa : algebraMap A Ap a ∈ Q := haP
      have hmaps : algebraMap A Ap (s : A) ∉ Q := by
        intro hsQ
        exact s.property (hPm hsQ)
      have : y ∈ Q := by
        apply (hQ.mem_or_mem ?_).resolve_right hmaps
        rw [hs]
        exact hmapa
      exact hy this
    refine ⟨algebraMap A Ap a, ⟨a, ha, rfl⟩, ?_⟩
    exact ⟨algebraMap A Ap (s : A), hs.symm⟩
  have hlocT : IsLocalization T AP := inferInstance
  letI : IsLocalization Q.primeCompl AP :=
    (IsLocalization.iff_of_le_of_exists_dvd (S := AP) (M := T)
      Q.primeCompl hTQ hQT).mp hlocT
  have hqmem : algebraMap Ap AP q ∈ IsLocalRing.maximalIdeal AP := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff AP Q]
    exact Ideal.mem_span_singleton_self q
  exact ((IsLocalRing.mem_maximalIdeal _).mp hqmem) hqmapunit

end Algebra
