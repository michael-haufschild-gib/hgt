/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.DFinsuppAddMonoidHomSum
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntCircleCharacter

/-!
# Heterogeneous finite-support reciprocity in Q/Z

Global local--global profiles do not have a common local carrier: residue fields, cyclic splitting
extensions, and torsion orders vary with the place.  This file packages arbitrary place-dependent
additive invariants in the one common ABHN target `ℚ/ℤ`.  Their global character is the finite
product of local phases, its product-one locus is exactly the zero-sum kernel, and quotienting by
that kernel recovers the subgroup of `ℚ/ℤ` realized by the family.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u v

/-- Sum arbitrary place-dependent additive invariants in the common `ℚ/ℤ` target. -/
noncomputable def heterogeneousRatModIntProfileInvariantSumAddHom
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (inv : ∀ i, A i →+ RatModInt) :
    (Π₀ i, A i) →+ RatModInt :=
  DFinsupp.sumAddHom inv

/-- A singleton profile has its one local invariant. -/
@[simp] theorem heterogeneousRatModIntProfileInvariantSumAddHom_single
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (inv : ∀ i, A i →+ RatModInt) (i : ι) (x : A i) :
    heterogeneousRatModIntProfileInvariantSumAddHom A inv (DFinsupp.single i x) = inv i x := by
  classical
  rw [heterogeneousRatModIntProfileInvariantSumAddHom, DFinsupp.sumAddHom_apply]
  exact DFinsupp.sum_single_index (map_zero _)

/-- Faithful global circle character after summing arbitrary place-dependent invariants. -/
noncomputable def heterogeneousRatModIntProfileStdAddChar
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (inv : ∀ i, A i →+ RatModInt) :
    AddChar (Π₀ i, A i) ℂ :=
  ratModIntStdAddChar.compAddMonoidHom
    (heterogeneousRatModIntProfileInvariantSumAddHom A inv)

/-- The global character of a singleton profile is its one local phase. -/
@[simp] theorem heterogeneousRatModIntProfileStdAddChar_single
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (inv : ∀ i, A i →+ RatModInt) (i : ι) (x : A i) :
    heterogeneousRatModIntProfileStdAddChar A inv (DFinsupp.single i x) =
      ratModIntStdAddChar (inv i x) := by
  rw [heterogeneousRatModIntProfileStdAddChar, AddChar.compAddMonoidHom_apply,
    heterogeneousRatModIntProfileInvariantSumAddHom_single]

/-- Global character equals the finite product of all place-dependent local phases. -/
theorem heterogeneousRatModIntProfileStdAddChar_eq_dfinsupp_prod
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    [(i : ι) → DecidableEq (A i)]
    (inv : ∀ i, A i →+ RatModInt) (f : Π₀ i, A i) :
    heterogeneousRatModIntProfileStdAddChar A inv f =
      f.prod fun i x => ratModIntStdAddChar (inv i x) := by
  induction f using DFinsupp.induction with
  | h0 =>
      simp [heterogeneousRatModIntProfileStdAddChar,
        heterogeneousRatModIntProfileInvariantSumAddHom, DFinsupp.prod]
  | @ha i b f hib hb ih =>
      rw [(heterogeneousRatModIntProfileStdAddChar A inv).map_add_eq_mul,
        ih, DFinsupp.prod_add_index]
      · rw [heterogeneousRatModIntProfileStdAddChar_single, DFinsupp.prod_single_index]
        rw [map_zero]
        exact ratModIntStdAddChar.map_zero_eq_one
      · intro i
        rw [map_zero]
        exact ratModIntStdAddChar.map_zero_eq_one
      · intro i a b
        rw [map_add]
        exact ratModIntStdAddChar.map_add_eq_mul _ _

/-- Product-one reciprocity is exactly vanishing of the heterogeneous `ℚ/ℤ` invariant sum. -/
theorem heterogeneousRatModIntProfile_product_eq_one_iff_sum_eq_zero
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    [(i : ι) → DecidableEq (A i)]
    (inv : ∀ i, A i →+ RatModInt) (f : Π₀ i, A i) :
    f.prod (fun i x => ratModIntStdAddChar (inv i x)) = 1 ↔
      heterogeneousRatModIntProfileInvariantSumAddHom A inv f = 0 := by
  rw [← heterogeneousRatModIntProfileStdAddChar_eq_dfinsupp_prod]
  exact ratModIntStdAddChar_eq_one_iff_eq_zero
    (heterogeneousRatModIntProfileInvariantSumAddHom A inv f)

/-- Zero-sum inclusion and heterogeneous invariant sum are exact. -/
theorem heterogeneousRatModIntProfileInvariantSum_exact
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (inv : ∀ i, A i →+ RatModInt) :
    Function.Exact
      (heterogeneousRatModIntProfileInvariantSumAddHom A inv).ker.subtype
      (heterogeneousRatModIntProfileInvariantSumAddHom A inv) := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.property

/-- Profiles modulo reciprocity are exactly the subgroup of `ℚ/ℤ` realized by local invariants. -/
noncomputable def heterogeneousRatModIntProfileInvariantSumQuotientEquivRange
    {ι : Type u} [DecidableEq ι]
    (A : ι → Type v) [(i : ι) → AddCommGroup (A i)]
    (inv : ∀ i, A i →+ RatModInt) :
    (Π₀ i, A i) ⧸ (heterogeneousRatModIntProfileInvariantSumAddHom A inv).ker ≃+
      (heterogeneousRatModIntProfileInvariantSumAddHom A inv).range :=
  QuotientAddGroup.quotientKerEquivRange
    (heterogeneousRatModIntProfileInvariantSumAddHom A inv)

end

end GaloisForLFunctions.HTGeometry.ABHN
