import GaloisForLFunctions.HTGeometry.AffineGroupSchemeCoLie

/-!
# Inversion acts by `-1` on the co-Lie module

For a commutative Hopf algebra `A` over `R`, the antipode `S` is the coordinate ring of inversion
on the group scheme `Spec A`, and inversion acts on the tangent space at the identity by `-1`:

`d (S a) = - d a`,  equivalently  `S x ≡ -x  (mod I²)`  for `x ∈ I`.

The proof is the first antipode axiom `m ∘ (S ⊗ 1) ∘ Δ = η ∘ ε` combined with the Leibniz rule for
the universal differential `d` and `ε ∘ S = ε`: applying `d` to `∑ S(a₁) a₂ = ε(a) · 1` gives
`d a + d (S a) = 0`.

This is the statement that `Lie` of a group scheme is a module on which inversion is `-1`, used
implicitly throughout Sections 2 and 3 of Suzuki, *Duality invariance of Faltings heights, Hodge
line bundles and global periods* (arXiv:2504.04993).
-/

namespace GaloisForLFunctions.HTGeometry.AffineGroupScheme

open Coalgebra Bialgebra Ideal
open scoped TensorProduct

variable {R A : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]

/-- **The antipode acts by `-1` on the co-Lie module.** -/
theorem d_antipode (a : A) : d R A (HopfAlgebra.antipode R a) = - d R A a := by
  classical
  set rep := Coalgebra.Repr.arbitrary R a with hrep
  have hHopf : ∑ i ∈ rep.index,
      (HopfAlgebra.antipode R (rep.left i)) * (rep.right i) = algebraMap R A (counit a) := by
    have h := LinearMap.congr_fun
      (HopfAlgebra.mul_antipode_rTensor_comul (R := R) (A := A)) a
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply] at h
    rw [← rep.eq] at h
    simpa using h
  have hd : d R A (∑ i ∈ rep.index,
      (HopfAlgebra.antipode R (rep.left i)) * (rep.right i)) = 0 := by
    rw [hHopf, d_algebraMap]
  rw [map_sum] at hd
  have hterm : ∀ i ∈ rep.index, d R A ((HopfAlgebra.antipode R (rep.left i)) * (rep.right i))
      = (counit (rep.left i) : R) • d R A (rep.right i)
        + (counit (rep.right i) : R) • d R A (HopfAlgebra.antipode R (rep.left i)) := by
    intro i _
    rw [d_mul, HopfAlgebra.counit_antipode]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib] at hd
  have hs1 : ∑ i ∈ rep.index, (counit (rep.left i) : R) • d R A (rep.right i) = d R A a := by
    have h := Coalgebra.sum_counit_tmul_map_eq (R := R) (d R A) a (repr := rep)
    have h2 := congrArg (TensorProduct.lid R (coLie R A)) h
    simpa using h2
  have hs2 : ∑ i ∈ rep.index,
      (counit (rep.right i) : R) • d R A (HopfAlgebra.antipode R (rep.left i))
      = d R A (HopfAlgebra.antipode R a) := by
    have h := Coalgebra.sum_map_tmul_counit_eq (R := R)
      ((d R A).comp (HopfAlgebra.antipode R)) a (repr := rep)
    have h2 := congrArg (TensorProduct.rid R (coLie R A)) h
    simpa using h2
  rw [hs1, hs2, add_comm] at hd
  exact eq_neg_of_add_eq_zero_left hd

/-- `S x ≡ -x mod I²` for `x` in the augmentation ideal. -/
theorem antipode_add_mem_augIdeal_sq {x : A} (hx : x ∈ augIdeal R A) :
    HopfAlgebra.antipode R x + x ∈ (augIdeal R A) ^ 2 := by
  have hS : (counit (HopfAlgebra.antipode R x) : R) = 0 := by
    rw [HopfAlgebra.counit_antipode]; exact mem_augIdeal.mp hx
  have hzero : d R A (HopfAlgebra.antipode R x + x) = 0 := by
    rw [map_add, d_antipode, neg_add_cancel]
  rw [d_apply] at hzero
  have hmem := ((augIdeal R A).toCotangent_eq_zero _).mp hzero
  rw [toAug_coe, map_add, hS, mem_augIdeal.mp hx, add_zero, map_zero, sub_zero] at hmem
  exact hmem

end GaloisForLFunctions.HTGeometry.AffineGroupScheme
