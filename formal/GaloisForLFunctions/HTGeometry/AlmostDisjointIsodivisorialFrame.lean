import GaloisForLFunctions.HTGeometry.PrimeDirichletTailPattern
import Mathlib.Analysis.Meromorphic.Order

/-!
# Almost-disjoint isodivisorial frames

This file isolates the exact finite-rank algebra and local divisor mechanism behind maximal
isodivisorial families of signed prime-Dirichlet sources.

* Pairwise almost-disjoint infinite flip sets have infinite private blocks inside every finite
  subfamily, so their signed coefficient columns are linearly independent modulo finite support.
* A common nowhere-zero phase does not change this tail rank.
* Multiplication by a holomorphic unit does not change local meromorphic order.

The analytic construction of a continuum almost-disjoint family and the classical
Dirichlet-series differential-independence transfer remain external inputs to this finite core.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Set

noncomputable section

/-- Flip the positive orientation precisely on the selected coordinate set. -/
noncomputable def setFlipOrientation {J P : Type*}
    (A : J → Set P) (j : J) (p : P) : Bool := by
  classical
  exact if p ∈ A j then true else false

theorem primeDirichletSign_setFlipOrientation_of_mem {J P : Type*}
    (A : J → Set P) (j : J) (p : P) (hp : p ∈ A j) :
    primeDirichletSign (setFlipOrientation A j p) = -1 := by
  classical
  simp [setFlipOrientation, hp]

theorem primeDirichletSign_setFlipOrientation_of_not_mem {J P : Type*}
    (A : J → Set P) (j : J) (p : P) (hp : p ∉ A j) :
    primeDirichletSign (setFlipOrientation A j p) = 1 := by
  classical
  simp [setFlipOrientation, hp]

/-- Exclusive infinite blocks force the associated sign orientations to be tail independent. -/
theorem primeOrientationTailIndependent_setFlip_of_exclusive
    {J P : Type*} [Fintype J] (A : J → Set P)
    (houtside : {p | ∀ j, p ∉ A j}.Infinite)
    (hexclusive : ∀ j, {p | p ∈ A j ∧ ∀ k, k ≠ j → p ∉ A k}.Infinite) :
    PrimeOrientationTailIndependent (setFlipOrientation A) := by
  classical
  intro c hsupp
  obtain ⟨p₀, hp₀, hp₀supp⟩ := (houtside.diff hsupp).nonempty
  have hp₀out : ∀ j, p₀ ∉ A j := hp₀
  have hzeroOutside : ∑ j, c j = 0 := by
    have h := hp₀supp
    simp only [Set.mem_setOf_eq, not_not] at h
    simpa [setFlipOrientation, hp₀out, primeDirichletSign] using h
  funext j
  obtain ⟨p, hp, hpsupp⟩ := ((hexclusive j).diff hsupp).nonempty
  have hzero : ∑ k, c k * primeDirichletSign (setFlipOrientation A k p) = 0 := by
    simpa only [Set.mem_setOf_eq, not_not] using hpsupp
  have hformula :
      (∑ k, c k * primeDirichletSign (setFlipOrientation A k p)) =
        (∑ k, c k) - 2 * c j := by
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ j)]
    rw [primeDirichletSign_setFlipOrientation_of_mem A j p hp.1]
    have hrest :
        (∑ k ∈ (Finset.univ : Finset J) \ {j},
            c k * primeDirichletSign (setFlipOrientation A k p)) =
          ∑ k ∈ (Finset.univ : Finset J) \ {j}, c k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkj : k ≠ j := by simpa using (Finset.mem_sdiff.mp hk).2
      rw [primeDirichletSign_setFlipOrientation_of_not_mem A k p (hp.2 k hkj)]
      ring
    rw [hrest]
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ j)]
    ring
  rw [hformula, hzeroOutside] at hzero
  simpa using hzero

/-- Pairwise finite intersections leave an infinite private block in each member of a finite
subfamily. -/
theorem infinite_exclusiveBlock_of_pairwise_finite_intersections
    {J P : Type*} [Fintype J] (A : J → Set P)
    (hinfinite : ∀ j, (A j).Infinite)
    (hpair : ∀ i j, i ≠ j → (A i ∩ A j).Finite) :
    ∀ j, {p | p ∈ A j ∧ ∀ k, k ≠ j → p ∉ A k}.Infinite := by
  classical
  intro j
  let bad : Set P := ⋃ k ∈ (Finset.univ.erase j : Finset J), A j ∩ A k
  have hbad : bad.Finite := by
    have hindices : (↑(Finset.univ.erase j) : Set J).Finite :=
      (Finset.univ.erase j).finite_toSet
    exact hindices.biUnion fun k hk => by
      have hkj : k ≠ j := by simpa using hk
      exact hpair j k hkj.symm
  have hprivate : (A j \ bad).Infinite := (hinfinite j).diff hbad
  apply hprivate.mono
  intro p hp
  refine ⟨hp.1, ?_⟩
  intro k hkj hpk
  apply hp.2
  refine Set.mem_iUnion₂.mpr ⟨k, ?_, ?_⟩
  · simp [hkj]
  · exact ⟨hp.1, hpk⟩

/-- A finite subfamily of an almost-disjoint family gives tail-independent flip orientations as
soon as infinitely many coordinates lie outside all selected blocks. -/
theorem primeOrientationTailIndependent_setFlip_of_almostDisjoint
    {J P : Type*} [Fintype J] (A : J → Set P)
    (hinfinite : ∀ j, (A j).Infinite)
    (hpair : ∀ i j, i ≠ j → (A i ∩ A j).Finite)
    (houtside : {p | ∀ j, p ∉ A j}.Infinite) :
    PrimeOrientationTailIndependent (setFlipOrientation A) :=
  primeOrientationTailIndependent_setFlip_of_exclusive A houtside
    (infinite_exclusiveBlock_of_pairwise_finite_intersections A hinfinite hpair)

/-- Multiplication by a holomorphic unit preserves the local meromorphic divisor order. -/
theorem meromorphicOrderAt_mul_analyticUnit_eq
    {f u : ℂ → ℂ} {z : ℂ} (hu : AnalyticAt ℂ u z) (huz : u z ≠ 0) :
    meromorphicOrderAt (u * f) z = meromorphicOrderAt f z :=
  meromorphicOrderAt_mul_of_ne_zero hu huz

end

end GaloisForLFunctions.HTGeometry
