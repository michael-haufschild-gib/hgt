import GaloisForLFunctions.RHTower.DeningerTowerDirectLimit
import GaloisForLFunctions.RHTower.DeningerKummerHomomorphism

/-!
# Global reciprocity in a tower of number fields

The logarithmic product formula cuts out the kernel of the place-sum map.  This file restricts
the place-transition maps to those reciprocity kernels.  Consequently the sum-zero local currents
form their own directed system, and a nonzero global element determines a compatible Kummer
current in its direct limit.

This is a product-formula analogue of the first, necessary part of a local--global sequence:
global Kummer currents satisfy the sole global reciprocity relation at every finite level.  It does
not assert the stronger Albert--Brauer--Hasse--Noether surjectivity statement.

* `deningerTowerPullHomKer` : field embeddings preserve reciprocity kernels.
* `deningerKummerReciprocityHom` : the global Kummer map lands in the reciprocity kernel.
* `deningerTowerKernelSystem` : the directed system of reciprocity kernels.
* `DeningerTowerReciprocityLimit` : its direct limit.
* `deningerKummerKernel_limit_compatible` : global Kummer currents persist in that limit.
-/

namespace RHTower

open NumberField Module

section PullHom

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]

/-- A field embedding carries local currents satisfying the logarithmic product formula to local
currents satisfying that formula. -/
noncomputable def deningerTowerPullHomKer (σ : K →+* L) :
    LinearMap.ker (deningerPlaceSum K) →ₗ[ℝ] LinearMap.ker (deningerPlaceSum L) :=
  ((deningerTowerPullHom σ).domRestrict (LinearMap.ker (deningerPlaceSum K))).codRestrict
    (LinearMap.ker (deningerPlaceSum L)) (fun f => by
    letI : Algebra K L := σ.toAlgebra
    change deningerPlaceSum L (deningerTowerPull K L f.1) = 0
    have hf : deningerPlaceSum K f.1 = 0 := f.property
    rw [deningerTowerPull_sum K L f.1, hf, mul_zero])

/-- Restriction to reciprocity kernels preserves the identity transition map. -/
theorem deningerTowerPullHomKer_id (f : LinearMap.ker (deningerPlaceSum K)) :
    deningerTowerPullHomKer (RingHom.id K) f = f := by
  apply Subtype.ext
  exact deningerTowerPullHom_id f.1

/-- Restriction to reciprocity kernels preserves composition of field embeddings. -/
theorem deningerTowerPullHomKer_comp {M : Type*} [Field M] [NumberField M]
    (σ : K →+* L) (τ : L →+* M) (f : LinearMap.ker (deningerPlaceSum K)) :
    deningerTowerPullHomKer τ (deningerTowerPullHomKer σ f) = deningerTowerPullHomKer (τ.comp σ) f := by
  apply Subtype.ext
  exact deningerTowerPullHom_comp σ τ f.1

/-- A nonzero global element, viewed as its logarithmic Kummer current, satisfies global
reciprocity. -/
noncomputable def deningerKummerKernelTest (K : Type*) [Field K] [NumberField K]
    {α : K} (hα : α ≠ 0) : LinearMap.ker (deningerPlaceSum K) :=
  ⟨deningerKummerTest K hα, deningerKummer_sum_eq_zero K hα⟩

/-- Kummer currents are functorial after imposing the global reciprocity relation. -/
theorem deningerKummerKernelTest_towerPull (σ : K →+* L) {α : K} (hα : α ≠ 0) (hσα : σ α ≠ 0) :
    deningerTowerPullHomKer σ (deningerKummerKernelTest K hα) = deningerKummerKernelTest L hσα := by
  apply Subtype.ext
  exact deningerKummerTest_towerPull σ hα hσα

/-- The logarithmic Kummer map, with the product formula built into its codomain.  Thus every
global multiplicative element gives a finite-support local current satisfying global reciprocity. -/
noncomputable def deningerKummerReciprocityHom (K : Type*) [Field K] [NumberField K] :
    Additive Kˣ →+ LinearMap.ker (deningerPlaceSum K) :=
  (deningerKummerHom K).codRestrict (LinearMap.ker (deningerPlaceSum K)) (fun u => by
    change deningerPlaceSum K (deningerKummerTest K (Units.ne_zero (Additive.toMul u))) = 0
    exact deningerKummer_sum_eq_zero K (Units.ne_zero (Additive.toMul u)))

/-- The reciprocity-valued Kummer homomorphism agrees with the pointwise bundled Kummer current. -/
theorem deningerKummerReciprocityHom_apply (K : Type*) [Field K] [NumberField K] (u : Kˣ) :
    deningerKummerReciprocityHom K (Additive.ofMul u) =
      deningerKummerKernelTest K (Units.ne_zero u) := by
  apply Subtype.ext
  rfl

/-- A reciprocity-valued Kummer current vanishes exactly for a root of unity.  Thus imposing the
product formula does not introduce any new kernel beyond the unavoidable global torsion. -/
theorem deningerKummerReciprocityHom_eq_zero_iff (K : Type*) [Field K] [NumberField K] (u : Kˣ) :
    deningerKummerReciprocityHom K (Additive.ofMul u) = 0 ↔ IsOfFinOrder ((u : K)) := by
  constructor
  · intro h
    exact (deningerKummerHom_eq_zero_iff K u).mp (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact (deningerKummerHom_eq_zero_iff K u).mpr h

/-- Two global units have the same local logarithmic current precisely when their quotient is a
root of unity.  Equivalently, the Kummer map to the product-formula kernel is injective modulo
global torsion. -/
theorem deningerKummerReciprocityHom_eq_iff (K : Type*) [Field K] [NumberField K] (u v : Kˣ) :
    deningerKummerReciprocityHom K (Additive.ofMul u) =
      deningerKummerReciprocityHom K (Additive.ofMul v) ↔
      IsOfFinOrder (((u * v⁻¹ : Kˣ) : K)) := by
  constructor
  · intro h
    apply (deningerKummerReciprocityHom_eq_zero_iff K (u * v⁻¹)).mp
    change deningerKummerReciprocityHom K (Additive.ofMul u + -Additive.ofMul v) = 0
    rw [map_add, map_neg]
    rw [h, add_neg_cancel]
  · intro h
    have hzero : deningerKummerReciprocityHom K (Additive.ofMul (u * v⁻¹)) = 0 :=
      (deningerKummerReciprocityHom_eq_zero_iff K (u * v⁻¹)).mpr h
    change deningerKummerReciprocityHom K (Additive.ofMul u + -Additive.ofMul v) = 0 at hzero
    rw [map_add, map_neg] at hzero
    apply add_right_cancel (b := -deningerKummerReciprocityHom K (Additive.ofMul v))
    rw [hzero]
    exact (add_neg_cancel (deningerKummerReciprocityHom K (Additive.ofMul v))).symm

/-- The range of the reciprocity-valued Kummer homomorphism is exactly the family of Kummer
currents regarded inside the product-formula kernel. -/
theorem deningerKummerReciprocityHom_range (K : Type*) [Field K] [NumberField K] :
    Set.range (deningerKummerReciprocityHom K) =
      {g | ∃ (α : K) (hα : α ≠ 0), g = deningerKummerKernelTest K hα} := by
  ext g
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨(Additive.toMul u : Kˣ), Units.ne_zero _,
      (deningerKummerReciprocityHom_apply K _).symm⟩
  · rintro ⟨α, hα, rfl⟩
    exact ⟨Additive.ofMul (Units.mk0 α hα), deningerKummerReciprocityHom_apply K _⟩

/-- Kummer currents commute with scalar extension after their codomains are restricted to the
reciprocity kernels. -/
theorem deningerKummerReciprocityHom_towerPull
    (σ : K →+* L) (u : Kˣ) :
    deningerTowerPullHomKer σ (deningerKummerReciprocityHom K (Additive.ofMul u)) =
      deningerKummerReciprocityHom L (Additive.ofMul (Units.map σ.toMonoidHom u)) := by
  rw [deningerKummerReciprocityHom_apply, deningerKummerReciprocityHom_apply]
  exact deningerKummerKernelTest_towerPull σ (Units.ne_zero u)
    ((map_ne_zero σ).mpr (Units.ne_zero u))

end PullHom

section Limit

variable {ι : Type*} [Preorder ι] [DecidableEq ι] (F : ι → Type*) [∀ i, Field (F i)]
  [∀ i, NumberField (F i)] (φ : ∀ i j, i ≤ j → F i →+* F j)

/-- The directed-system transition on the kernels of the product-formula maps. -/
noncomputable def deningerTowerKernelSystem (i j : ι) (h : i ≤ j) :
    LinearMap.ker (deningerPlaceSum (F i)) →ₗ[ℝ] LinearMap.ker (deningerPlaceSum (F j)) :=
  deningerTowerPullHomKer (φ i j h)

omit [DecidableEq ι] in
/-- The reciprocity kernels in a compatible tower form a directed system. -/
theorem deningerTowerKernelSystem_directed
    (hid : ∀ i (h : i ≤ i), φ i i h = RingHom.id (F i))
    (hcomp : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
      (φ j k hjk).comp (φ i j hij) = φ i k (hij.trans hjk)) :
    DirectedSystem (fun i => (LinearMap.ker (deningerPlaceSum (F i)) : Type _))
      fun i j h => deningerTowerKernelSystem F φ i j h := by
  constructor
  · intro i x
    show deningerTowerPullHomKer (φ i i le_rfl) x = x
    rw [hid i le_rfl]
    exact deningerTowerPullHomKer_id x
  · intro k j i hij hjk x
    show deningerTowerPullHomKer (φ j k hjk) (deningerTowerPullHomKer (φ i j hij) x)
      = deningerTowerPullHomKer (φ i k (hij.trans hjk)) x
    rw [deningerTowerPullHomKer_comp, hcomp]

/-- Direct limit of the product-formula kernels along a tower of number fields. -/
noncomputable abbrev DeningerTowerReciprocityLimit : Type _ :=
  Module.DirectLimit (fun i => LinearMap.ker (deningerPlaceSum (F i)))
    fun i j h => deningerTowerKernelSystem F φ i j h

/-- The product-formula Kummer current of a global element is independent of the finite tower
stage used to represent it. -/
theorem deningerKummerKernel_limit_compatible (i j : ι) (hij : i ≤ j) {α : F i} (hα : α ≠ 0)
    (hφα : φ i j hij α ≠ 0) :
    Module.DirectLimit.of ℝ ι (fun i => LinearMap.ker (deningerPlaceSum (F i)))
        (fun i j h => deningerTowerKernelSystem F φ i j h) j (deningerKummerKernelTest (F j) hφα)
      = Module.DirectLimit.of ℝ ι (fun i => LinearMap.ker (deningerPlaceSum (F i)))
        (fun i j h => deningerTowerKernelSystem F φ i j h) i (deningerKummerKernelTest (F i) hα) := by
  have hpull : deningerTowerKernelSystem F φ i j hij (deningerKummerKernelTest (F i) hα)
      = deningerKummerKernelTest (F j) hφα :=
    deningerKummerKernelTest_towerPull (φ i j hij) hα hφα
  rw [← hpull]
  exact Module.DirectLimit.of_f

end Limit

end RHTower
