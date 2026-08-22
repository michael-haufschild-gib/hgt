import GaloisForLFunctions.HTGeometry.ValuationInertiaRamificationIndex
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# The orbit formula at an intermediate field

`ValuationInertiaRamificationIndex` computes the inertia group of a valuation subring over any base
ring; this module supplies the base ring for an *intermediate field* — the integral closure of the
bottom base in it — and assembles the two computations into the orbit formula.

```text
intermediateBaseToTop       the intermediate base sits inside the top integral closure
intermediateBase_mem, intermediateToW, intermediateCentre
mem_intermediateCentre_iff
liesOver_intermediateCentre, intermediateCentre_ne_bot
natCard_inertiaSubgroup_eq_intermediate_mul
    ** |W.inertiaSubgroup F| = e(Q_M / p) · |W.inertiaSubgroup M| **
```

`IsIntegralClosure.tower_top` is what makes the top integral closure serve as the integral closure of
the intermediate base as well, and that is exactly the hypothesis `ramificationIdxIn_tower` needs on
its upper step.  Nothing here assumes the intermediate extension is normal — which is the point,
since the source field of a cover is precisely the non-normal step.

`IntermediateField.algebra'` and its scalar towers supply almost every instance for free; the two
that must be produced by hand are the scalar tower `A → ↥M → L` and the corestriction of the
intermediate base into the top integral closure.
-/

namespace GaloisForLFunctions.HTGeometry
namespace ValuationInertia

noncomputable section

open IsLocalRing
open scoped Pointwise

variable {A L : Type*} [CommRing A] [IsDedekindDomain A]
variable {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
variable [Field L] [Algebra F L] [Algebra A L] [IsScalarTower A F L]
variable [FiniteDimensional F L] [IsGalois F L]
variable (M : IntermediateField F L)

instance : Algebra.IsSeparable F M :=
  Algebra.isSeparable_tower_bot_of_isSeparable F M L

instance : IsScalarTower A M L := IsScalarTower.of_algebraMap_eq fun _ => rfl


/-- The integral closure of the base in an intermediate field maps into the integral closure in the
top field. -/
def intermediateBaseToTop : integralClosure A M →+* integralClosure A L :=
  RingHom.codRestrict
    ((algebraMap (M : Type _) L).comp (algebraMap (integralClosure A M) M))
    (integralClosure A L).toSubring
    (fun x => by
      have hx : IsIntegral A ((x : M) : L) :=
        (x.property).map (IsScalarTower.toAlgHom A M L)
      exact hx)

instance : Algebra (integralClosure A M) (integralClosure A L) :=
  (intermediateBaseToTop (A := A) (L := L) M).toAlgebra

instance : IsScalarTower A (integralClosure A M) (integralClosure A L) :=
  IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl

instance : IsScalarTower (integralClosure A M) (integralClosure A L) L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance : IsIntegralClosure (integralClosure A L) (integralClosure A M) L :=
  IsIntegralClosure.tower_top (R := A)

variable (W : ValuationSubring L) (hAW : ∀ a : A, algebraMap A L a ∈ W)

omit [IsDedekindDomain A] [IsFractionRing A F] [FiniteDimensional F L] [IsGalois F L] in
include hAW in
/-- Every element of the intermediate base lies in the valuation subring. -/
theorem intermediateBase_mem (b : integralClosure A M) :
    algebraMap (integralClosure A M) L b ∈ W :=
  mem_of_isIntegral W hAW (b.property.map (IsScalarTower.toAlgHom A M L))

/-- The intermediate base, landed inside the valuation subring. -/
def intermediateToW : integralClosure A M →+* W :=
  RingHom.codRestrict (algebraMap (integralClosure A M) L) W.toSubring
    (intermediateBase_mem M W hAW)

/-- The prime of the intermediate base cut out by the valuation. -/
def intermediateCentre : Ideal (integralClosure A M) :=
  (IsLocalRing.maximalIdeal W).comap (intermediateToW M W hAW)

omit [IsDedekindDomain A] [IsFractionRing A F] [FiniteDimensional F L] [IsGalois F L] in
instance intermediateCentre_isPrime : (intermediateCentre M W hAW).IsPrime :=
  Ideal.comap_isPrime _ _

omit [IsDedekindDomain A] [IsFractionRing A F] [FiniteDimensional F L] [IsGalois F L] in
theorem mem_intermediateCentre_iff (b : integralClosure A M) :
    b ∈ intermediateCentre M W hAW ↔
      ¬ IsUnit (⟨algebraMap (integralClosure A M) L b, intermediateBase_mem M W hAW b⟩ : W) := by
  show intermediateToW M W hAW b ∈ IsLocalRing.maximalIdeal W ↔ _
  rw [IsLocalRing.mem_maximalIdeal]
  rfl

omit [IsDedekindDomain A] [IsFractionRing A F] [FiniteDimensional F L] [IsGalois F L] in
theorem algebraMap_intermediateBase_apply (a : A) :
    algebraMap (integralClosure A M) L (algebraMap A (integralClosure A M) a)
      = algebraMap A L a := by
  rw [← IsScalarTower.algebraMap_apply]

omit [IsDedekindDomain A] [FiniteDimensional F L] [IsGalois F L] in
theorem injective_algebraMap_intermediateBase :
    Function.Injective (algebraMap A (integralClosure A M)) := by
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective A F)
  intro x y hxy
  apply hAL
  rw [← algebraMap_intermediateBase_apply M x, ← algebraMap_intermediateBase_apply M y, hxy]

variable (p : Ideal A)

omit [IsDedekindDomain A] [IsFractionRing A F] [FiniteDimensional F L] [IsGalois F L] in
include hAW in
theorem liesOver_intermediateCentre
    (hcentA : ∀ a : A, (¬ IsUnit (⟨algebraMap A L a, hAW a⟩ : W)) ↔ a ∈ p) :
    (intermediateCentre M W hAW).LiesOver p := by
  constructor
  refine Ideal.ext fun a => ?_
  have hcoe : (⟨algebraMap (integralClosure A M) L (algebraMap A (integralClosure A M) a),
      intermediateBase_mem M W hAW _⟩ : W) = (⟨algebraMap A L a, hAW a⟩ : W) := by
    apply Subtype.ext
    exact algebraMap_intermediateBase_apply M a
  constructor
  · intro ha
    show algebraMap A (integralClosure A M) a ∈ intermediateCentre M W hAW
    rw [mem_intermediateCentre_iff, hcoe]
    exact (hcentA a).mpr ha
  · intro ha
    have h : algebraMap A (integralClosure A M) a ∈ intermediateCentre M W hAW := ha
    rw [mem_intermediateCentre_iff, hcoe] at h
    exact (hcentA a).mp h

omit [IsDedekindDomain A] [FiniteDimensional F L] [IsGalois F L] in
include hAW in
theorem intermediateCentre_ne_bot (hp0 : p ≠ ⊥)
    (hcentA : ∀ a : A, (¬ IsUnit (⟨algebraMap A L a, hAW a⟩ : W)) ↔ a ∈ p) :
    intermediateCentre M W hAW ≠ ⊥ := by
  obtain ⟨a, hap, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
  intro hbot
  haveI := liesOver_intermediateCentre M W hAW p hcentA
  have hmem : algebraMap A (integralClosure A M) a ∈ intermediateCentre M W hAW := by
    rw [mem_intermediateCentre_iff]
    have hcoe : (⟨algebraMap (integralClosure A M) L (algebraMap A (integralClosure A M) a),
        intermediateBase_mem M W hAW _⟩ : W) = (⟨algebraMap A L a, hAW a⟩ : W) := by
      apply Subtype.ext
      exact algebraMap_intermediateBase_apply M a
    rw [hcoe]
    exact (hcentA a).mpr hap
  rw [hbot, Ideal.mem_bot] at hmem
  exact ha0 (injective_algebraMap_intermediateBase M (by rw [hmem, map_zero]))

include hAW in
/-- **The orbit formula at an intermediate field.**  The inertia group of the base is the inertia
group of the intermediate field times the ramification index of the intermediate place. -/
theorem natCard_inertiaSubgroup_eq_intermediate_mul
    (hW : W ≠ ⊤) (hp0 : p ≠ ⊥) [p.IsMaximal] [PerfectField p.ResidueField]
    (hcentA : ∀ a : A, (¬ IsUnit (⟨algebraMap A L a, hAW a⟩ : W)) ↔ a ∈ p)
    [PerfectField (intermediateCentre M W hAW).ResidueField] :
    Nat.card (W.inertiaSubgroup F)
      = (intermediateCentre M W hAW).ramificationIdx A * Nat.card (W.inertiaSubgroup M) := by
  haveI : IsDedekindDomain (integralClosure A M) :=
    IsIntegralClosure.isDedekindDomain A F M (integralClosure A M)
  haveI : IsFractionRing (integralClosure A M) M :=
    IsIntegralClosure.isFractionRing_of_finite_extension A F M (integralClosure A M)
  haveI := liesOver_intermediateCentre M W hAW p hcentA
  haveI : (intermediateCentre M W hAW).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance (intermediateCentre_ne_bot M W hAW p hp0 hcentA)
  exact natCard_inertiaSubgroup_eq_ramificationIdx_mul
    (A := A) (B := integralClosure A M) (T := integralClosure A L)
    F M p (intermediateCentre M W hAW) W hW hAW
    (intermediateBase_mem M W hAW) hcentA
    (fun b => (mem_intermediateCentre_iff M W hAW b).symm)

end

end ValuationInertia
end GaloisForLFunctions.HTGeometry
