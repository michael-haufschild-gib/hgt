/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.HeterogeneousRatModIntReciprocity
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntTorsionCircleCharacter

/-!
# Heterogeneous finite-torsion reciprocity

Each place may have its own torsion order and its own additive carrier.  Placewise equivalences
with `ℚ/ℤ[nᵥ]` embed all values in the common `ℚ/ℤ` target.  This specializes heterogeneous
reciprocity to the finite layers produced by cyclic local class field theory while retaining
different orders at different places.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u v

/-- Include a place-specific finite torsion coordinate in the common `ℚ/ℤ` target. -/
noncomputable def heterogeneousTorsionLocalInvariantAddHom
    {ι : Type u} [DecidableEq ι] (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (n : ι → ℕ) (e : ∀ i, A i ≃+ ratModIntNTorsion (n i)) (i : ι) :
    A i →+ RatModInt :=
  (ratModIntNTorsion (n i)).subtype.comp (e i).toAddMonoidHom

/-- Sum a place-dependent finite-torsion profile in `ℚ/ℤ`. -/
noncomputable def heterogeneousTorsionProfileInvariantSumAddHom
    {ι : Type u} [DecidableEq ι] (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (n : ι → ℕ) (e : ∀ i, A i ≃+ ratModIntNTorsion (n i)) :
    (Π₀ i, A i) →+ RatModInt :=
  heterogeneousRatModIntProfileInvariantSumAddHom A
    (heterogeneousTorsionLocalInvariantAddHom A n e)

/-- Global character of a heterogeneous finite-torsion profile. -/
noncomputable def heterogeneousTorsionProfileStdAddChar
    {ι : Type u} [DecidableEq ι] (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (n : ι → ℕ) (e : ∀ i, A i ≃+ ratModIntNTorsion (n i)) :
    AddChar (Π₀ i, A i) ℂ :=
  heterogeneousRatModIntProfileStdAddChar A
    (heterogeneousTorsionLocalInvariantAddHom A n e)

/-- Global finite-torsion character equals the product of its place-dependent local phases. -/
theorem heterogeneousTorsionProfileStdAddChar_eq_dfinsupp_prod
    {ι : Type u} [DecidableEq ι] (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    [(i : ι) → DecidableEq (A i)]
    (n : ι → ℕ) (e : ∀ i, A i ≃+ ratModIntNTorsion (n i)) (f : Π₀ i, A i) :
    heterogeneousTorsionProfileStdAddChar A n e f =
      f.prod fun i x => ratModIntStdAddChar
        (heterogeneousTorsionLocalInvariantAddHom A n e i x) :=
  heterogeneousRatModIntProfileStdAddChar_eq_dfinsupp_prod A
    (heterogeneousTorsionLocalInvariantAddHom A n e) f

/-- Product-one reciprocity is exactly vanishing of the heterogeneous finite-torsion sum. -/
theorem heterogeneousTorsionProfile_product_eq_one_iff_sum_eq_zero
    {ι : Type u} [DecidableEq ι] (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    [(i : ι) → DecidableEq (A i)]
    (n : ι → ℕ) (e : ∀ i, A i ≃+ ratModIntNTorsion (n i)) (f : Π₀ i, A i) :
    f.prod (fun i x => ratModIntStdAddChar
        (heterogeneousTorsionLocalInvariantAddHom A n e i x)) = 1 ↔
      heterogeneousTorsionProfileInvariantSumAddHom A n e f = 0 :=
  heterogeneousRatModIntProfile_product_eq_one_iff_sum_eq_zero A
    (heterogeneousTorsionLocalInvariantAddHom A n e) f

/-- Heterogeneous finite-torsion reciprocity is exact at the profile term. -/
theorem heterogeneousTorsionProfileInvariantSum_exact
    {ι : Type u} [DecidableEq ι] (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (n : ι → ℕ) (e : ∀ i, A i ≃+ ratModIntNTorsion (n i)) :
    Function.Exact
      (heterogeneousTorsionProfileInvariantSumAddHom A n e).ker.subtype
      (heterogeneousTorsionProfileInvariantSumAddHom A n e) :=
  heterogeneousRatModIntProfileInvariantSum_exact A
    (heterogeneousTorsionLocalInvariantAddHom A n e)

/-- Profiles modulo reciprocity recover exactly the subgroup of `ℚ/ℤ` realized by the family. -/
noncomputable def heterogeneousTorsionProfileInvariantSumQuotientEquivRange
    {ι : Type u} [DecidableEq ι] (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (n : ι → ℕ) (e : ∀ i, A i ≃+ ratModIntNTorsion (n i)) :
    (Π₀ i, A i) ⧸ (heterogeneousTorsionProfileInvariantSumAddHom A n e).ker ≃+
      (heterogeneousTorsionProfileInvariantSumAddHom A n e).range :=
  heterogeneousRatModIntProfileInvariantSumQuotientEquivRange A
    (heterogeneousTorsionLocalInvariantAddHom A n e)

/-- A one-place product-one law detects precisely the zero local class. -/
theorem heterogeneousTorsionProfile_single_product_eq_one_iff_eq_zero
    {ι : Type u} [DecidableEq ι] (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    [(i : ι) → DecidableEq (A i)]
    (n : ι → ℕ) (e : ∀ i, A i ≃+ ratModIntNTorsion (n i)) (i : ι) (x : A i) :
    (DFinsupp.single i x).prod (fun j y => ratModIntStdAddChar
        (heterogeneousTorsionLocalInvariantAddHom A n e j y)) = 1 ↔ x = 0 := by
  rw [DFinsupp.prod_single_index]
  · rw [ratModIntStdAddChar_eq_one_iff_eq_zero]
    change ((e i x : ratModIntNTorsion (n i)) : RatModInt) = 0 ↔ x = 0
    constructor
    · intro hx
      apply (e i).injective
      apply Subtype.ext
      simpa using hx
    · rintro rfl
      simp
  · rw [map_zero]
    exact ratModIntStdAddChar.map_zero_eq_one

end

end GaloisForLFunctions.HTGeometry.ABHN
