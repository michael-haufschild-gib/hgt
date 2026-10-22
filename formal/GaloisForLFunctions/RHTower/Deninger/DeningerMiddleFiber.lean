import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# The canonical middle fibre of a coarse-to-derived comparison

A morphism whose endpoint cohomologies are isomorphisms and whose target has vanishing middle
cohomology has a fibre concentrated in degree one, where it is canonically the middle cohomology of
the source.  All of this is read off the long exact sequence of the fibre triangle: the connecting
morphism out of degree zero vanishes because the degree-zero comparison is onto, and the connecting
morphism out of degree two vanishes because the degree-two comparison is onto.

The statements below are the exactness content of that long exact sequence, so they apply verbatim
to the fibre of any morphism of cochain complexes.

* `deningerMiddleFiber_connecting_eq_zero` : a surjective comparison kills the connecting map.
* `deningerMiddleFiber_degree_zero`, `_degree_two`, `_degree_three` : the fibre vanishes outside
  degree one.
* `deningerMiddleFiber_degree_one_bijective` : in degree one the fibre is the source cohomology.
* `deningerMiddleFiber_symm_equivariant` : and the identification is equivariant.
-/

namespace RHTower

section MiddleFiber

variable {R : Type*} [Ring R]

/-- **A surjective comparison kills the connecting morphism.**  Exactness at the target places the
image of the comparison in the kernel of the connecting map. -/
theorem deningerMiddleFiber_connecting_eq_zero {C D M : Type*}
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D] [AddCommGroup M] [Module R M]
    (f : C →ₗ[R] D) (d : D →ₗ[R] M) (hexact : Function.Exact f d)
    (hf : Function.Surjective f) (y : D) : d y = 0 := by
  obtain ⟨x, rfl⟩ := hf y
  exact (hexact (f x)).mpr ⟨x, rfl⟩

/-- **The fibre vanishes in degree zero.**  The fibre injects into the source, and the comparison
is injective there. -/
theorem deningerMiddleFiber_degree_zero {M C D : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
    (m : M →ₗ[R] C) (f : C →ₗ[R] D) (hcomp : ∀ x, f (m x) = 0)
    (hm : Function.Injective m) (hf : Function.Injective f) (x : M) : x = 0 := by
  refine hm ?_
  rw [map_zero]
  refine hf ?_
  rw [hcomp, map_zero]

/-- **The fibre is injected into the source in degree one**, because the incoming connecting map
vanishes. -/
theorem deningerMiddleFiber_degree_one_injective {D M C : Type*}
    [AddCommGroup D] [Module R D] [AddCommGroup M] [Module R M] [AddCommGroup C] [Module R C]
    (d : D →ₗ[R] M) (m : M →ₗ[R] C) (hexact : Function.Exact d m)
    (hd : ∀ y, d y = 0) : Function.Injective m := by
  refine (injective_iff_map_eq_zero m).mpr fun x hx => ?_
  obtain ⟨y, hy⟩ := (hexact x).mp hx
  rw [← hy, hd y]

/-- **The fibre covers the source in degree one**, because the target has no middle cohomology. -/
theorem deningerMiddleFiber_degree_one_surjective {M C D : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
    (m : M →ₗ[R] C) (f : C →ₗ[R] D) (hexact : Function.Exact m f)
    (hD : ∀ z : D, z = 0) : Function.Surjective m := by
  intro c
  exact (hexact c).mp (hD (f c))

/-- **The canonical degree-one identification.** -/
theorem deningerMiddleFiber_degree_one_bijective {D M C D' : Type*}
    [AddCommGroup D] [Module R D] [AddCommGroup M] [Module R M] [AddCommGroup C] [Module R C]
    [AddCommGroup D'] [Module R D']
    (d : D →ₗ[R] M) (m : M →ₗ[R] C) (f : C →ₗ[R] D')
    (hexactM : Function.Exact d m) (hexactC : Function.Exact m f)
    (hd : ∀ y, d y = 0) (hD' : ∀ z : D', z = 0) : Function.Bijective m :=
  ⟨deningerMiddleFiber_degree_one_injective d m hexactM hd,
    deningerMiddleFiber_degree_one_surjective m f hexactC hD'⟩

/-- **The fibre vanishes in degree two.**  It injects into the source because the incoming
connecting map comes from a vanishing group, and the degree-two comparison is injective. -/
theorem deningerMiddleFiber_degree_two {D M C D' : Type*}
    [AddCommGroup D] [Module R D] [AddCommGroup M] [Module R M] [AddCommGroup C] [Module R C]
    [AddCommGroup D'] [Module R D']
    (d : D →ₗ[R] M) (m : M →ₗ[R] C) (f : C →ₗ[R] D')
    (hexactM : Function.Exact d m) (hD : ∀ y : D, y = 0)
    (hcomp : ∀ x, f (m x) = 0) (hf : Function.Injective f) (x : M) : x = 0 := by
  refine deningerMiddleFiber_degree_zero m f hcomp ?_ hf x
  refine deningerMiddleFiber_degree_one_injective d m hexactM fun y => ?_
  rw [hD y, map_zero]

/-- **The fibre vanishes in degree three.**  The connecting map out of degree two is onto the fibre
and is zero, because the degree-two comparison is onto. -/
theorem deningerMiddleFiber_degree_three {C D M : Type*}
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D] [AddCommGroup M] [Module R M]
    (f : C →ₗ[R] D) (d : D →ₗ[R] M) (hexact : Function.Exact f d)
    (hf : Function.Surjective f) (hd : Function.Surjective d) (x : M) : x = 0 := by
  obtain ⟨y, rfl⟩ := hd x
  exact deningerMiddleFiber_connecting_eq_zero f d hexact hf y

/-- The canonical degree-one identification as a linear equivalence. -/
noncomputable def deningerMiddleFiberEquiv {M C : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup C] [Module R C]
    (m : M →ₗ[R] C) (hm : Function.Bijective m) : M ≃ₗ[R] C :=
  LinearEquiv.ofBijective m hm

/-- **Equivariance.**  If the comparison intertwines endomorphisms — a flow, or a semigroup of
correspondences — then so does the inverse of the canonical degree-one identification. -/
theorem deningerMiddleFiber_symm_equivariant {M C : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup C] [Module R C]
    (m : M →ₗ[R] C) (hm : Function.Bijective m) (thetaM : M →ₗ[R] M) (thetaC : C →ₗ[R] C)
    (hcomm : ∀ x, m (thetaM x) = thetaC (m x)) (c : C) :
    (deningerMiddleFiberEquiv m hm).symm (thetaC c)
      = thetaM ((deningerMiddleFiberEquiv m hm).symm c) := by
  refine (deningerMiddleFiberEquiv m hm).injective ?_
  rw [LinearEquiv.apply_symm_apply]
  show thetaC c = m (thetaM ((deningerMiddleFiberEquiv m hm).symm c))
  rw [hcomm]
  congr 1
  show c = (deningerMiddleFiberEquiv m hm) ((deningerMiddleFiberEquiv m hm).symm c)
  rw [LinearEquiv.apply_symm_apply]

end MiddleFiber

end RHTower
