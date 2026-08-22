/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Simultaneous denominator clearing in fraction fields

A finite family in the fraction field of a domain has one common nonzero denominator.  Applied
to the finitely many structure constants of a finite-dimensional algebra, this is the first
algebraic ingredient in constructing an order.  It does not yet assert closure of a chosen
lattice under multiplication, nor Azumaya reduction away from its discriminant.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open nonZeroDivisors

universe u v

/-- A finite set of fraction-field elements has a common nonzero denominator. -/
theorem finite_exists_commonDenominator
    (R : Type u) [CommRing R] [IsDomain R] (K : Type v) [Field K] [Algebra R K]
    [IsFractionRing R K] (s : Finset K) :
    ∃ d : R, d ≠ 0 ∧ ∀ x ∈ s, ∃ n : R,
      algebraMap R K d * x = algebraMap R K n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, one_ne_zero, ?_⟩
      simp
  | insert x s hx ih =>
      obtain ⟨d, hd, hs⟩ := ih
      obtain ⟨n, q, hq, hqx⟩ := IsFractionRing.div_surjective R x
      refine ⟨q * d, mul_ne_zero (nonZeroDivisors.ne_zero hq) hd, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · refine ⟨d * n, ?_⟩
        rw [← hqx, map_mul, map_mul]
        calc
          (algebraMap R K q * algebraMap R K d) *
              (algebraMap R K n / algebraMap R K q) =
              algebraMap R K d *
                (algebraMap R K n / algebraMap R K q) * algebraMap R K q := by
              ac_rfl
          _ = algebraMap R K d * algebraMap R K n := by
              rw [mul_assoc, div_mul_cancel₀ _
                (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq)]
      · obtain ⟨m, hm⟩ := hs y hy
        refine ⟨q * m, ?_⟩
        calc
          algebraMap R K (q * d) * y = algebraMap R K q * (algebraMap R K d * y) := by
            rw [map_mul, mul_assoc]
          _ = algebraMap R K q * algebraMap R K m := by rw [hm]
          _ = algebraMap R K (q * m) := by rw [map_mul]

/-- A finite indexed family of fraction-field elements has a common nonzero denominator. -/
theorem fintype_exists_commonDenominator
    (R : Type u) [CommRing R] [IsDomain R] (K : Type v) [Field K] [Algebra R K]
    [IsFractionRing R K] (ι : Type*) [Fintype ι] (x : ι → K) :
    ∃ d : R, d ≠ 0 ∧ ∀ i : ι, ∃ n : R,
      algebraMap R K d * x i = algebraMap R K n := by
  classical
  obtain ⟨d, hd, h⟩ := finite_exists_commonDenominator R K (Finset.univ.image x)
  refine ⟨d, hd, ?_⟩
  intro i
  exact h (x i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

/-- One nonzero denominator clears every multiplication structure constant of a finite basis of
an algebra over a fraction field. -/
theorem basis_mul_structureConstants_exists_commonDenominator
    (R : Type u) [CommRing R] [IsDomain R] (K : Type v) [Field K] [Algebra R K]
    [IsFractionRing R K] (A : Type*) [Ring A] [Algebra K A]
    (ι : Type*) [Fintype ι] (b : Module.Basis ι K A) :
    ∃ d : R, d ≠ 0 ∧ ∀ i j k : ι, ∃ r : R,
      algebraMap R K d * b.repr (b i * b j) k = algebraMap R K r := by
  obtain ⟨d, hd, h⟩ := fintype_exists_commonDenominator R K (ι × (ι × ι))
    (fun p ↦ b.repr (b p.1 * b p.2.1) p.2.2)
  refine ⟨d, hd, ?_⟩
  intro i j k
  exact h (i, j, k)

end GaloisForLFunctions.HTGeometry.ABHN
