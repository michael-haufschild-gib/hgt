import GaloisForLFunctions.HTGeometry.ValuationSubringInertiaDictionary
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# `|inertia| = e` for a valuation subring, over any base field

`ValuationSubringInertiaDictionary` identifies the valuation-theoretic inertia group of a valuation
subring `W ⊆ L` with the ideal-theoretic inertia group of the prime it cuts out on a Dedekind domain
with fraction field `L`.  Feeding mathlib's `Ideal.card_inertia_eq_ramificationIdxIn` through that
identification gives the fundamental identity in the form the horizon needs:

```text
integralClosure_mem_of_base_mem          the integral closure of the base sits inside W
natCard_inertiaSubgroup_eq_ramificationIdxIn
    ** Nat.card (W.inertiaSubgroup F) = ramificationIdxIn (maximalIdeal R) (integralClosure R L) **
```

The point of the statement is that `F` is an *arbitrary* base field over which `L` is Galois — not
necessarily the bottom of the tower.  Applied to an intermediate field `M` it computes the order of
the stabiliser of `M` inside the inertia group of the bottom field, which is what turns a bound on
ramification indices into a bound on the orbits of the inertia action on the sheets of a cover.

Hypotheses are minimal: a Dedekind domain `R` with fraction field `F`, a finite Galois extension
`L/F`, a maximal ideal `p` of `R`, and a valuation subring `W` of `L` containing the image of `R`,
not the whole of `L`, whose nonunits meet `R` exactly in `p`.  The base ring is Dedekind rather than
discrete precisely so that mathlib's `Ideal.ramificationIdx_tower` can be applied between two
applications of this theorem, at the bottom field and at an intermediate one.

Two implementation notes worth keeping.  The action of `Gal(L/F)` on the integral closure must be
introduced with `letI`, not `haveI`: `algebraMap_galRestrict_apply` is stated about `galRestrict`,
and only a `let`-bound instance unfolds `g • x` to it.  And `Module.Flat R (integralClosure R L)`
needs the torsion-free instance first, which comes from injectivity of `R → integralClosure R L`.
-/

namespace GaloisForLFunctions.HTGeometry
namespace ValuationInertia

noncomputable section

open IsLocalRing
open scoped Pointwise

/-- Every element integral over a base ring lies in any valuation subring containing that base. -/
theorem integralClosure_mem_of_base_mem {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (W : ValuationSubring L) (hRW : ∀ r : R, algebraMap R L r ∈ W)
    (x : integralClosure R L) : (x : L) ∈ W := by
  haveI : IsIntegrallyClosedIn W.toSubring L := by
    rw [Subring.isIntegrallyClosedIn_iff]
    intro y hy
    exact Subring.isIntegrallyClosed_iff.mp (inferInstance : IsIntegrallyClosed W) hy
  exact (Subring.integralClosure_le_iff (T := W.toSubring)).mpr hRW x.property

/-- Every element of `L` integral over the base lies in a valuation subring containing it. -/
theorem mem_of_isIntegral {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (W : ValuationSubring L) (hRW : ∀ r : R, algebraMap R L r ∈ W)
    {y : L} (hy : IsIntegral R y) : y ∈ W :=
  integralClosure_mem_of_base_mem W hRW ⟨y, hy⟩

/-- The centre of the valuation lies over the prescribed maximal ideal of the base. -/
theorem liesOver_centerPrime
    {R T L : Type*} [CommRing R] [CommRing T] [IsDedekindDomain T]
    [Field L] [Algebra T L] [IsFractionRing T L] [Algebra R T] [Algebra R L]
    [IsScalarTower R T L]
    (p : Ideal R)
    (W : ValuationSubring L) (hRW : ∀ r : R, algebraMap R L r ∈ W)
    (hSW : ∀ x : T, algebraMap T L x ∈ W)
    (hcent : ∀ r : R, (¬ IsUnit (⟨algebraMap R L r, hRW r⟩ : W)) ↔ r ∈ p) :
    (centerPrime W hSW).LiesOver p := by
  constructor
  refine Ideal.ext fun r => ?_
  have hcoe : toValuationSubring W hSW (algebraMap R T r) = (⟨algebraMap R L r, hRW r⟩ : W) := by
    apply Subtype.ext
    show algebraMap T L (algebraMap R T r) = algebraMap R L r
    rw [← IsScalarTower.algebraMap_apply]
  constructor
  · intro hr
    show algebraMap R T r ∈ centerPrime W hSW
    show toValuationSubring W hSW (algebraMap R T r) ∈ IsLocalRing.maximalIdeal W
    rw [hcoe, IsLocalRing.mem_maximalIdeal]
    exact (hcent r).mpr hr
  · intro hr
    have hmem : toValuationSubring W hSW (algebraMap R T r) ∈ IsLocalRing.maximalIdeal W := hr
    rw [hcoe, IsLocalRing.mem_maximalIdeal] at hmem
    exact (hcent r).mp hmem

/-- **The inertia group of a valuation subring has order the ramification index**, over any base
field of the normal extension and any Dedekind base ring. -/
theorem natCard_inertiaSubgroup_eq_ramificationIdxIn
    {R T L : Type*} [CommRing R] [IsDedekindDomain R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]
    [Field L] [Algebra F L] [Algebra R L] [IsScalarTower R F L]
    [FiniteDimensional F L] [IsGalois F L]
    [CommRing T] [IsDomain T] [Algebra R T] [Algebra T L] [IsScalarTower R T L]
    [IsIntegralClosure T R L]
    (p : Ideal R) [p.IsMaximal] [PerfectField p.ResidueField]
    (W : ValuationSubring L) (hW : W ≠ ⊤) (hRW : ∀ r : R, algebraMap R L r ∈ W)
    (hcent : ∀ r : R, (¬ IsUnit (⟨algebraMap R L r, hRW r⟩ : W)) ↔ r ∈ p) :
    Nat.card (W.inertiaSubgroup F) = Ideal.ramificationIdxIn p T := by
  classical
  haveI : IsDedekindDomain T := IsIntegralClosure.isDedekindDomain R F L T
  haveI : Module.Finite R T := IsIntegralClosure.finite R F L T
  haveI : IsFractionRing T L := IsIntegralClosure.isFractionRing_of_finite_extension R F L T
  letI : MulSemiringAction (L ≃ₐ[F] L) T := IsIntegralClosure.MulSemiringAction R F L T
  have hSW : ∀ x : T, algebraMap T L x ∈ W :=
    fun x => mem_of_isIntegral W hRW ((IsIntegralClosure.isIntegral R L x).map (IsScalarTower.toAlgHom R T L))
  have hact : ∀ (g : L ≃ₐ[F] L) (x : T),
      algebraMap T L (g • x) = g • algebraMap T L x := by
    intro g x
    exact algebraMap_galRestrict_apply R g x
  rw [← natCard_inertia_eq_natCard_inertiaSubgroup W hSW hact hW]
  haveI : IsGaloisGroup (L ≃ₐ[F] L) R T := IsGaloisGroup.of_isFractionRing _ _ _ F L
  haveI : Finite (L ≃ₐ[F] L) := inferInstance
  have hinjRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective R F)
  have hinjRS : Function.Injective (algebraMap R T) := by
    intro x y hxy
    have := congrArg (algebraMap T L) hxy
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    exact hinjRL this
  haveI : Module.IsTorsionFree R T := (Module.isTorsionFree_iff_algebraMap_injective).mpr hinjRS
  haveI : Module.Flat R T := inferInstance
  haveI : (centerPrime W hSW).LiesOver p := liesOver_centerPrime p W hRW hSW hcent
  exact Ideal.card_inertia_eq_ramificationIdxIn _ _

/-- **The Galois ramification index is multiplicative through a possibly non-normal middle
extension.**  `Ideal.ramificationIdxIn_mul_ramificationIdxIn` cannot be used here: it asks for the
middle extension to be Galois, which is exactly what fails for the source field of a cover. -/
theorem ramificationIdxIn_tower
    {A B T : Type*} [CommRing A] [CommRing B] [CommRing T]
    [Algebra A B] [Algebra A T] [Algebra B T] [IsScalarTower A B T]
    (p : Ideal A) (Q : Ideal B) (P : Ideal T)
    [Q.IsPrime] [Q.LiesOver p] [P.IsPrime] [P.LiesOver Q] [Module.Flat B T]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G T] [IsGaloisGroup G A T]
    (G' : Type*) [Group G'] [Finite G'] [MulSemiringAction G' T] [IsGaloisGroup G' B T] :
    Ideal.ramificationIdxIn p T = Q.ramificationIdx A * Ideal.ramificationIdxIn Q T := by
  haveI : P.LiesOver p := Ideal.LiesOver.trans (𝔓 := P) (P := Q) (p := p)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P G,
      Ideal.ramificationIdxIn_eq_ramificationIdx Q P G',
      Ideal.ramificationIdx_tower Q P]

/-- **The orbit formula.**  Two applications of `natCard_inertiaSubgroup_eq_ramificationIdxIn`,
one at the bottom field and one at an intermediate field, joined by `ramificationIdxIn_tower`. -/
theorem natCard_inertiaSubgroup_eq_ramificationIdx_mul
    {A B T L : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
    [CommRing T] [IsDomain T]
    (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F]
    (M : Type*) [Field M] [Algebra B M] [IsFractionRing B M]
    [Field L] [Algebra F L] [Algebra M L] [Algebra A L] [Algebra B L]
    [Algebra A B] [Algebra A T] [Algebra B T] [Algebra T L]
    [IsScalarTower A F L] [IsScalarTower B M L] [IsScalarTower A T L] [IsScalarTower B T L]
    [IsScalarTower A B T]
    [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional M L] [IsGalois M L]
    [IsIntegralClosure T A L] [IsIntegralClosure T B L]
    (p : Ideal A) [p.IsMaximal] [PerfectField p.ResidueField]
    (Q : Ideal B) [Q.IsMaximal] [Q.LiesOver p] [PerfectField Q.ResidueField]
    (W : ValuationSubring L) (hW : W ≠ ⊤)
    (hAW : ∀ a : A, algebraMap A L a ∈ W) (hBW : ∀ b : B, algebraMap B L b ∈ W)
    (hcentA : ∀ a : A, (¬ IsUnit (⟨algebraMap A L a, hAW a⟩ : W)) ↔ a ∈ p)
    (hcentB : ∀ b : B, (¬ IsUnit (⟨algebraMap B L b, hBW b⟩ : W)) ↔ b ∈ Q) :
    Nat.card (W.inertiaSubgroup F) = Q.ramificationIdx A * Nat.card (W.inertiaSubgroup M) := by
  classical
  haveI : IsDedekindDomain T := IsIntegralClosure.isDedekindDomain A F L T
  haveI : Module.Finite A T := IsIntegralClosure.finite A F L T
  haveI : Module.Finite B T := IsIntegralClosure.finite B M L T
  haveI : IsFractionRing T L := IsIntegralClosure.isFractionRing_of_finite_extension A F L T
  have hSW : ∀ x : T, algebraMap T L x ∈ W :=
    fun x => mem_of_isIntegral W hAW ((IsIntegralClosure.isIntegral A L x).map
      (IsScalarTower.toAlgHom A T L))
  haveI : (centerPrime W hSW).LiesOver p := liesOver_centerPrime p W hAW hSW hcentA
  haveI : (centerPrime W hSW).LiesOver Q := liesOver_centerPrime Q W hBW hSW hcentB
  have hinjBT : Function.Injective (algebraMap B T) := by
    intro x y hxy
    have h := congrArg (algebraMap T L) hxy
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
    have hBL : Function.Injective (algebraMap B L) := by
      rw [IsScalarTower.algebraMap_eq B M L]
      exact (algebraMap M L).injective.comp (IsFractionRing.injective B M)
    exact hBL h
  haveI : Module.IsTorsionFree B T := (Module.isTorsionFree_iff_algebraMap_injective).mpr hinjBT
  haveI : Module.Flat B T := inferInstance
  rw [natCard_inertiaSubgroup_eq_ramificationIdxIn (T := T) F p W hW hAW hcentA,
    natCard_inertiaSubgroup_eq_ramificationIdxIn (T := T) M Q W hW hBW hcentB]
  letI : MulSemiringAction (L ≃ₐ[F] L) T := IsIntegralClosure.MulSemiringAction A F L T
  letI : MulSemiringAction (L ≃ₐ[M] L) T := IsIntegralClosure.MulSemiringAction B M L T
  haveI : IsGaloisGroup (L ≃ₐ[F] L) A T := IsGaloisGroup.of_isFractionRing _ _ _ F L
  haveI : IsGaloisGroup (L ≃ₐ[M] L) B T := IsGaloisGroup.of_isFractionRing _ _ _ M L
  haveI : Finite (L ≃ₐ[F] L) := inferInstance
  haveI : Finite (L ≃ₐ[M] L) := inferInstance
  exact ramificationIdxIn_tower p Q (centerPrime W hSW) (L ≃ₐ[F] L) (L ≃ₐ[M] L)

end

end ValuationInertia
end GaloisForLFunctions.HTGeometry
