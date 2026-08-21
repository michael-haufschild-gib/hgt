/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# Cyclic Hilbert 90 interface for ABHN

For a finite cyclic Galois extension, the norm-one elements are exactly the multiplicative
coboundaries `y / g(y)`.  This is the `H¹` input used in the construction and normalization of
cyclic algebras.  It does not construct the local reciprocity map or the `H²`--Brauer comparison
needed for the local invariant theorem.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

/-- A Galois automorphism preserves the field norm, by reindexing the finite product of all
conjugates. -/
theorem cyclicGalois_norm_gal_apply {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (g : Gal(L/K)) (y : L) :
    Algebra.norm K (g y) = Algebra.norm K y := by
  apply FaithfulSMul.algebraMap_injective K L
  rw [Algebra.norm_eq_prod_automorphisms, Algebra.norm_eq_prod_automorphisms]
  exact Fintype.prod_bijective (fun sigma : Gal(L/K) => sigma * g) (Group.mulRight_bijective g)
    (fun sigma => sigma (g y)) (fun tau => tau y) (by intro sigma; rfl)

/-- A multiplicative Galois coboundary has norm one. -/
theorem cyclicGalois_norm_div_apply {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (g : Gal(L/K)) (y : Lˣ) :
    Algebra.norm K ((y : L) / g y) = 1 := by
  rw [div_eq_mul_inv, map_mul, Algebra.norm_inv, cyclicGalois_norm_gal_apply]
  exact mul_inv_cancel₀ (Algebra.norm_ne_zero_iff.mpr y.ne_zero)

/-- **Cyclic Hilbert 90, norm form.** In a finite cyclic Galois extension, an element has norm
one exactly when it is `y / g(y)` for a unit `y`, where `g` generates the Galois group. -/
theorem cyclicGalois_norm_eq_one_iff_exists_div_apply {K L : Type} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    {g : Gal(L/K)} (hg : forall sigma, sigma ∈ Subgroup.zpowers g) (x : L) :
    Algebra.norm K x = 1 ↔ exists y : Lˣ, y / g y = x := by
  constructor
  · exact groupCohomology.exists_div_of_norm_eq_one hg
  · rintro ⟨y, rfl⟩
    exact cyclicGalois_norm_div_apply g y

end GaloisForLFunctions.HTGeometry.ABHN
