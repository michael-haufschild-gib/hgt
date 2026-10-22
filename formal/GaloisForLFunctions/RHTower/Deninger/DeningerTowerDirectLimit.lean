import GaloisForLFunctions.RHTower.Deninger.DeningerTowerCocycle
import GaloisForLFunctions.RHTower.Deninger.DeningerTowerInjective
import Mathlib.Algebra.Colimit.Module

/-!
# The direct limit of the tower: the test space of the Allcock–Vaaler space

An embedding of number fields carries the transition map of the tower, weighting the pullback of a
test function by the local degree.  The identity embedding gives the identity map — the local
degrees over the identity are one, because they are positive and their fibre sums are `[K : K] =
1` — and composing embeddings composes the transition maps.  So a tower of number fields gives a
directed system of test spaces, and its direct limit is the test space of the place space of the
union, the Allcock–Vaaler space.

The logarithmic Kummer functions live in that limit: the Kummer function of an element, computed
in any field containing it, is one and the same element of the direct limit.

* `deningerTowerPullHom` : the transition map of an embedding.
* `deningerTowerPullHom_id`, `deningerTowerPullHom_comp` : it is functorial.
* `deningerTowerSystem_directed` : **a tower of number fields is a directed system of test
  spaces.**
* `DeningerTowerLimit` : **the direct limit — the test space of the Allcock–Vaaler space.**
* `deningerKummer_limit_compatible` : **the Kummer functions define one element of the limit.**
-/

namespace RHTower

open NumberField Module

section PullHom

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]

/-- **The transition map attached to an embedding of number fields.** -/
noncomputable def deningerTowerPullHom (σ : K →+* L) :
    DeningerTestSpace (DeningerPlace K) →ₗ[ℝ] DeningerTestSpace (DeningerPlace L) :=
  letI : Algebra K L := σ.toAlgebra
  deningerTowerPull K L

/-- **The transition map of the identity embedding is the identity.** -/
theorem deningerTowerPullHom_id (f : DeningerTestSpace (DeningerPlace K)) :
    deningerTowerPullHom (RingHom.id K) f = f := by
  letI : Algebra K K := (RingHom.id K).toAlgebra
  have hrestrict : ∀ w : DeningerPlace K, deningerPlaceRestrict K K w = w := by
    intro w
    cases w with
    | inl w => exact congrArg Sum.inl (InfinitePlace.comap_id w)
    | inr w =>
      refine congrArg Sum.inr ?_
      show FinitePlace.mk (deningerUnderSpectrum (K := K) w.maximalIdeal) = w
      have hideal : deningerUnderSpectrum (K := K) w.maximalIdeal = w.maximalIdeal :=
        IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun _ => Iff.rfl)
      rw [hideal, FinitePlace.mk_maximalIdeal]
  have hdeg : ∀ w : DeningerPlace K, deningerPlaceDegreeOver K K w = 1 := by
    intro w
    cases w with
    | inl w =>
      show w.mult / (w.comap (algebraMap K K)).mult = 1
      have hid : (algebraMap K K : K →+* K) = RingHom.id K := rfl
      rw [hid, InfinitePlace.comap_id, Nat.div_self InfinitePlace.mult_pos]
    | inr w =>
      show deningerFiniteDegreeOver (K := K) w = 1
      have hres : deningerRestrictPlace (K := K) w = w := Sum.inr_injective (hrestrict (Sum.inr w))
      have hmem : w ∈ deningerPlacesOver (L := K) w :=
        (deningerMem_placesOver (L := K) w w).mpr hres
      have hsum := deningerFiniteDegree_fibre_sum (K := K) (L := K) w
      rw [Module.finrank_self] at hsum
      have hle : deningerFiniteDegreeOver (K := K) w ≤ 1 := by
        rw [← hsum]
        exact Finset.single_le_sum (f := fun u => deningerFiniteDegreeOver (K := K) u)
          (fun u _ => Nat.zero_le _) hmem
      have hge : 1 ≤ deningerFiniteDegreeOver (K := K) w := deningerFiniteDegreeOver_pos w
      omega
  refine Subtype.ext (funext fun w => ?_)
  show (deningerPlaceDegreeOver K K w : ℝ)
      * (f : DeningerPlace K → ℝ) (deningerPlaceRestrict K K w)
    = (f : DeningerPlace K → ℝ) w
  rw [hdeg, hrestrict, Nat.cast_one, one_mul]

/-- **The transition maps compose.** -/
theorem deningerTowerPullHom_comp {M : Type*} [Field M] [NumberField M] (σ : K →+* L)
    (τ : L →+* M) (f : DeningerTestSpace (DeningerPlace K)) :
    deningerTowerPullHom τ (deningerTowerPullHom σ f) = deningerTowerPullHom (τ.comp σ) f := by
  letI : Algebra K L := σ.toAlgebra
  letI : Algebra L M := τ.toAlgebra
  letI : Algebra K M := (τ.comp σ).toAlgebra
  haveI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact deningerTowerPull_trans K L M f

/-- **The transition map carries the Kummer function of an element to the Kummer function of its
image.** -/
theorem deningerKummerTest_towerPull (σ : K →+* L) {α : K} (hα : α ≠ 0) (hσα : σ α ≠ 0) :
    deningerTowerPullHom σ (deningerKummerTest K hα) = deningerKummerTest L hσα := by
  letI : Algebra K L := σ.toAlgebra
  refine Subtype.ext (funext fun w => ?_)
  show (deningerPlaceDegreeOver K L w : ℝ)
      * deningerKummerFun K α (deningerPlaceRestrict K L w)
    = deningerKummerFun L (σ α) w
  exact (deningerKummerFun_tower K L α w).symm

end PullHom

section Limit

variable {ι : Type*} [Preorder ι] [DecidableEq ι] (F : ι → Type*) [∀ i, Field (F i)]
  [∀ i, NumberField (F i)] (φ : ∀ i j, i ≤ j → F i →+* F j)

/-- The directed system of test spaces attached to a tower of number fields. -/
noncomputable def deningerTowerSystem (i j : ι) (h : i ≤ j) :
    DeningerTestSpace (DeningerPlace (F i)) →ₗ[ℝ] DeningerTestSpace (DeningerPlace (F j)) :=
  deningerTowerPullHom (φ i j h)

omit [DecidableEq ι] in
/-- **A tower of number fields gives a directed system of test spaces.** -/
theorem deningerTowerSystem_directed
    (hid : ∀ i (h : i ≤ i), φ i i h = RingHom.id (F i))
    (hcomp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
      (φ j k hjk).comp (φ i j hij) = φ i k (hij.trans hjk)) :
    DirectedSystem (fun i => (DeningerTestSpace (DeningerPlace (F i)) : Type _))
      fun i j h => deningerTowerSystem F φ i j h := by
  constructor
  · intro i x
    show deningerTowerPullHom (φ i i le_rfl) x = x
    rw [hid i le_rfl]
    exact deningerTowerPullHom_id x
  · intro k j i hij hjk x
    show deningerTowerPullHom (φ j k hjk) (deningerTowerPullHom (φ i j hij) x)
      = deningerTowerPullHom (φ i k (hij.trans hjk)) x
    rw [deningerTowerPullHom_comp, hcomp]

/-- **The test space of the Allcock–Vaaler space of a tower**: the direct limit of the test spaces
of the place spaces along the transition maps. -/
noncomputable abbrev DeningerTowerLimit : Type _ :=
  Module.DirectLimit (fun i => DeningerTestSpace (DeningerPlace (F i)))
    fun i j h => deningerTowerSystem F φ i j h

/-- **The Kummer functions of a tower define a single element of the direct limit**: computing the
Kummer function of an element in a larger field does not change the element of the limit. -/
theorem deningerKummer_limit_compatible (i j : ι) (hij : i ≤ j) {α : F i} (hα : α ≠ 0)
    (hφα : φ i j hij α ≠ 0) :
    Module.DirectLimit.of ℝ ι (fun i => DeningerTestSpace (DeningerPlace (F i)))
        (fun i j h => deningerTowerSystem F φ i j h) j (deningerKummerTest (F j) hφα)
      = Module.DirectLimit.of ℝ ι (fun i => DeningerTestSpace (DeningerPlace (F i)))
        (fun i j h => deningerTowerSystem F φ i j h) i (deningerKummerTest (F i) hα) := by
  have hpull : deningerTowerSystem F φ i j hij (deningerKummerTest (F i) hα)
      = deningerKummerTest (F j) hφα :=
    deningerKummerTest_towerPull (φ i j hij) hα hφα
  rw [← hpull]
  exact Module.DirectLimit.of_f

end Limit

end RHTower
