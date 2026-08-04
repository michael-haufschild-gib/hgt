import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Algebra.Colimit.Module

/-!
# Exterior powers commute with direct limits of vector spaces

For a directed system of vector spaces with injective transition maps, the exterior power of the
direct limit is the direct limit of the exterior powers.  Surjectivity holds because the exterior
power is spanned by the products of tuples, and finitely many elements of a direct limit come from a
common stage; injectivity holds because an injective map of vector spaces splits, so its exterior
power is injective, and a limit of injective maps is injective.

* `exteriorPower_map_injective` : the exterior power of an injective map of vector spaces.
* `exteriorPowerDirectLimitEquiv` : the comparison is an isomorphism.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

section ExteriorPowerInjective

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- **The exterior power of an injective map of vector spaces is injective**, because such a map
has a linear left inverse. -/
theorem exteriorPower_map_injective (n : ℕ) {g : M →ₗ[K] N} (hg : Function.Injective g) :
    Function.Injective (exteriorPower.map n g) := by
  obtain ⟨s, hs⟩ := g.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hg)
  have hcomp : (exteriorPower.map n s).comp (exteriorPower.map n g) =
      LinearMap.id (R := K) (M := ⋀[K]^n M) := by
    rw [← exteriorPower.map_comp, hs, exteriorPower.map_id]
  intro x y hxy
  have hx := congrArg (fun L : ⋀[K]^n M →ₗ[K] ⋀[K]^n M => L x) hcomp
  have hy := congrArg (fun L : ⋀[K]^n M →ₗ[K] ⋀[K]^n M => L y) hcomp
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hx hy
  rw [← hx, ← hy, hxy]

end ExteriorPowerInjective

section DirectLimit

variable {K : Type*} [Field K] {ι : Type*} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  [DecidableEq ι] (G : ι → Type*) [∀ i, AddCommGroup (G i)] [∀ i, Module K (G i)]
  (f : ∀ i j, i ≤ j → G i →ₗ[K] G j)

/-- The maps of a directed system of exterior powers. -/
noncomputable def exteriorPowerSystem (n : ℕ) (i j : ι) (h : i ≤ j) :
    ⋀[K]^n (G i) →ₗ[K] ⋀[K]^n (G j) :=
  exteriorPower.map n (f i j h)

variable [DirectedSystem G fun i j h => f i j h]

/-- **The canonical map from the direct limit of the exterior powers to the exterior power of the
direct limit.** -/
noncomputable def exteriorPowerDirectLimitMap (n : ℕ) :
    DirectLimit (fun i => ⋀[K]^n (G i)) (exteriorPowerSystem G f n) →ₗ[K]
      ⋀[K]^n (DirectLimit G f) :=
  DirectLimit.lift K ι _ _ (fun i => exteriorPower.map n (DirectLimit.of K ι G f i))
    (fun i j hij x => by
      show exteriorPower.map n (DirectLimit.of K ι G f j)
        (exteriorPower.map n (f i j hij) x) = _
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
      congr 1
      refine congrArg (exteriorPower.map n) ?_
      refine LinearMap.ext fun y => ?_
      exact DirectLimit.of_f)

@[simp]
theorem exteriorPowerDirectLimitMap_of (n : ℕ) (i : ι) (x : ⋀[K]^n (G i)) :
    exteriorPowerDirectLimitMap G f n
        (DirectLimit.of K ι (fun i => ⋀[K]^n (G i)) (exteriorPowerSystem G f n) i x) =
      exteriorPower.map n (DirectLimit.of K ι G f i) x :=
  DirectLimit.lift_of _ _ _ _

/-- In a directed system of injective maps, the maps into the direct limit are injective. -/
theorem directLimit_of_injective (hinj : ∀ i j h, Function.Injective (f i j h)) (i : ι) :
    Function.Injective (DirectLimit.of K ι G f i) := by
  intro x y hxy
  have hzero : DirectLimit.of K ι G f i (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨j, hij, hfx⟩ := DirectLimit.of.zero_exact hzero
  have : x - y = 0 := hinj i j hij (by rw [hfx, map_zero])
  exact sub_eq_zero.1 this

/-- **Exterior powers commute with direct limits of vector spaces along injective maps.** -/
theorem exteriorPowerDirectLimitMap_bijective (n : ℕ)
    (hinj : ∀ i j h, Function.Injective (f i j h)) :
    Function.Bijective (exteriorPowerDirectLimitMap G f n) := by
  classical
  constructor
  · refine DirectLimit.lift_injective _ _ fun i => ?_
    exact exteriorPower_map_injective n (directLimit_of_injective G f hinj i)
  · rw [← LinearMap.range_eq_top]
    rw [← top_le_iff, ← exteriorPower.ιMulti_span]
    rw [Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    -- every tuple of the direct limit comes from a common stage
    have hlift : ∀ a : Fin n, ∃ i x, DirectLimit.of K ι G f i x = v a := fun a =>
      DirectLimit.exists_of _
    choose idx val hval using hlift
    obtain ⟨j, hj⟩ := Finset.exists_le (Finset.image idx Finset.univ)
    have hjmem : ∀ a : Fin n, idx a ≤ j := fun a =>
      hj (idx a) (Finset.mem_image.2 ⟨a, Finset.mem_univ a, rfl⟩)
    have hvj : ∀ a : Fin n,
        DirectLimit.of K ι G f j (f (idx a) j (hjmem a) (val a)) = v a := by
      intro a
      rw [DirectLimit.of_f]
      exact hval a
    refine ⟨DirectLimit.of K ι (fun i => ⋀[K]^n (G i)) (exteriorPowerSystem G f n) j
      (exteriorPower.ιMulti K n fun a => f (idx a) j (hjmem a) (val a)), ?_⟩
    rw [exteriorPowerDirectLimitMap_of, exteriorPower.map_apply_ιMulti]
    congr 1
    funext a
    exact hvj a

/-- **The exterior power of a direct limit of vector spaces along injective maps is the direct limit
of the exterior powers.** -/
noncomputable def exteriorPowerDirectLimitEquiv (n : ℕ)
    (hinj : ∀ i j h, Function.Injective (f i j h)) :
    DirectLimit (fun i => ⋀[K]^n (G i)) (exteriorPowerSystem G f n) ≃ₗ[K]
      ⋀[K]^n (DirectLimit G f) :=
  LinearEquiv.ofBijective _ (exteriorPowerDirectLimitMap_bijective G f n hinj)

end DirectLimit

end GaloisForLFunctions.HTGeometry
