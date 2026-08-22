import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Difference-weighted double sums are exterior products of two sections

For any bilinear map `B` and finite families `C`, `D` indexed by `ι`, the double sum weighted by the
coefficient *difference* `a i - a j` collapses to the exterior combination of two one-particle
sections:

`∑_i ∑_j (a i - a j) • B (C i) (D j) = B (∑ a i • C i) (∑ D j) - B (∑ C i) (∑ a j • D j)`.

Specializing `B` to the tensor product of linear maps gives the exterior factorization of an
ordered pair section; specializing it to multiplication in an algebra gives the same statement for
a one-particle Gram coboundary, with no tensor product at all.  Both are pure bilinearity: the
diagonal coefficients vanish automatically and no positivity, ordering or finiteness of rank is
used.
-/

open scoped TensorProduct

namespace HTGeometry

section Bilinear

variable {R M N P ι : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P] [Fintype ι]

/-- **Exterior pair factorization.** -/
theorem sum_sub_smul_bilinear (B : M →ₗ[R] N →ₗ[R] P) (a : ι → R) (C : ι → M) (D : ι → N) :
    ∑ i, ∑ j, (a i - a j) • B (C i) (D j)
      = B (∑ i, a i • C i) (∑ j, D j) - B (∑ i, C i) (∑ j, a j • D j) := by
  have hrow : ∀ i : ι, ∑ j, (a i - a j) • B (C i) (D j)
      = (B (a i • C i)) (∑ j, D j) - (B (C i)) (∑ j, a j • D j) := by
    intro i
    rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sub_smul, map_smul, LinearMap.smul_apply, map_smul]
  have h1 : ∑ i, (B (a i • C i)) (∑ j, D j) = (B (∑ i, a i • C i)) (∑ j, D j) := by
    rw [map_sum B (fun i => a i • C i) Finset.univ, LinearMap.sum_apply]
  have h2 : ∑ i, (B (C i)) (∑ j, a j • D j) = (B (∑ i, C i)) (∑ j, a j • D j) := by
    rw [map_sum B (fun i => C i) Finset.univ, LinearMap.sum_apply]
  rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_sub_distrib, h1, h2]

end Bilinear

section TensorSpecialization

variable {R M N ι : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [Fintype ι]

/-- **The ordered pair section is a decomposable exterior tensor.**  With `A = ∑ a i • C i` and
`B = ∑ C i`, the difference-weighted ordered pair sum is `A ⊗ B - B ⊗ A`. -/
theorem sum_sub_smul_tensorMap (a : ι → R) (C : ι → (M →ₗ[R] N)) :
    ∑ i, ∑ j, (a i - a j) • TensorProduct.map (C i) (C j)
      = TensorProduct.map (∑ i, a i • C i) (∑ j, C j)
        - TensorProduct.map (∑ i, C i) (∑ j, a j • C j) := by
  have h := sum_sub_smul_bilinear (R := R)
    (TensorProduct.mapBilinear (RingHom.id R) M M N N) a C C
  simp only [TensorProduct.mapBilinear_apply] at h
  exact h

end TensorSpecialization

section AlgebraSpecialization

variable {R A ι : Type*} [CommRing R] [Ring A] [Algebra R A] [Fintype ι]

/-- **The one-particle Gram coboundary is an exterior combination.**  No tensor product is used:
the same identity holds for multiplication in any algebra. -/
theorem sum_sub_smul_mul (a : ι → R) (C D : ι → A) :
    ∑ i, ∑ j, (a i - a j) • (C i * D j)
      = (∑ i, a i • C i) * (∑ j, D j) - (∑ i, C i) * (∑ j, a j • D j) := by
  have h := sum_sub_smul_bilinear (R := R) (M := A) (N := A) (P := A)
    (LinearMap.mul R A) a C D
  simp only [LinearMap.mul_apply'] at h
  exact h

end AlgebraSpecialization

end HTGeometry
