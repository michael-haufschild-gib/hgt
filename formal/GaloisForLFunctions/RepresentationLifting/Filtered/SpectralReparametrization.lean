import GaloisForLFunctions.RepresentationLifting.Filtered.ClockRankOneDensity
import Mathlib.LinearAlgebra.Lagrange

/-!
# Spectral recovery and diagonal observable algebras

A finite diagonal observable can be recovered polynomially from another
exactly when it is constant on the latter's spectral fibers. Thus the
generated algebra remembers precisely the partition into equal eigenvalues.
In particular, squaring the natural clock loses no observable information.
-/

noncomputable section

namespace GaloisForLFunctions.RepresentationLifting.Filtered

open Polynomial HTGeometry
open scoped Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- Lagrange interpolation works on the distinct values, including repeated labels. -/
theorem exists_polynomial_on_fibers_iff {K : Type*} [Field K] (a b : I → K) :
    (∃ p : K[X], ∀ i, p.eval (b i) = a i) ↔
      ∀ i j, b i = b j → a i = a j := by
  classical
  constructor
  · rintro ⟨p, hp⟩ i j hij
    rw [← hp i, ← hp j, hij]
  · intro h
    let g : K → K := fun t => if ht : ∃ i, b i = t then a ht.choose else 0
    have hg (i : I) : g (b i) = a i := by
      have hi : ∃ j, b j = b i := ⟨i, rfl⟩
      dsimp [g]
      rw [dif_pos hi]
      exact h _ _ hi.choose_spec
    refine ⟨Lagrange.interpolate (Finset.univ.image b) id g, fun i => ?_⟩
    exact (Lagrange.eval_interpolate_at_node (s := Finset.univ.image b)
      (v := id) (i := b i) g (fun _ _ _ _ he => he)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)).trans (hg i)

/-- Polynomial recovery is exactly refinement of the partition into spectral fibers. -/
theorem diagonal_mem_adjoin_iff (a b : I → ℝ) :
    Matrix.diagonal a ∈ Algebra.adjoin ℝ ({Matrix.diagonal b} : Set (Matrix I I ℝ)) ↔
      ∀ i j, b i = b j → a i = a j := by
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range]
  constructor
  · rintro ⟨p, hp⟩
    apply (exists_polynomial_on_fibers_iff a b).mp
    refine ⟨p, ?_⟩
    rw [aeval_diagonal_real] at hp
    exact congrFun (Matrix.diagonal_injective hp)
  · intro h
    obtain ⟨p, hp⟩ := (exists_polynomial_on_fibers_iff a b).mpr h
    refine ⟨p, ?_⟩
    rw [aeval_diagonal_real]
    congr 1
    exact funext hp

/-- Equal finite diagonal algebras are classified by equality of spectral partitions. -/
theorem diagonal_adjoin_eq_iff (a b : I → ℝ) :
    Algebra.adjoin ℝ ({Matrix.diagonal a} : Set (Matrix I I ℝ)) =
        Algebra.adjoin ℝ ({Matrix.diagonal b} : Set (Matrix I I ℝ)) ↔
      ∀ i j, a i = a j ↔ b i = b j := by
  constructor
  · intro h
    have ha : Matrix.diagonal a ∈ Algebra.adjoin ℝ {Matrix.diagonal b} := by
      rw [← h]
      exact Algebra.subset_adjoin (Set.mem_singleton _)
    have hb : Matrix.diagonal b ∈ Algebra.adjoin ℝ {Matrix.diagonal a} := by
      rw [h]
      exact Algebra.subset_adjoin (Set.mem_singleton _)
    exact fun i j => ⟨(diagonal_mem_adjoin_iff b a).mp hb i j,
      (diagonal_mem_adjoin_iff a b).mp ha i j⟩
  · intro h
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ rfl
      exact (diagonal_mem_adjoin_iff a b).mpr (fun i j => (h i j).mpr)
    · apply Algebra.adjoin_le
      rintro _ rfl
      exact (diagonal_mem_adjoin_iff b a).mpr (fun i j => (h i j).mp)

/-- The exact obstruction to recovering a diagonal clock from its square. -/
theorem diagonal_square_recovery_iff (a : I → ℝ) :
    Matrix.diagonal a ∈ Algebra.adjoin ℝ ({Matrix.diagonal a ^ 2} : Set (Matrix I I ℝ)) ↔
      ∀ i j, a i ^ 2 = a j ^ 2 → a i = a j := by
  rw [Matrix.diagonal_pow, diagonal_mem_adjoin_iff]
  rfl

private theorem naturalClock_sq_diagonal (n : ℕ) :
    naturalClock n ^ 2 = Matrix.diagonal (fun i : Fin n => (i.val : ℝ) ^ 2) := by
  rw [naturalClock, Matrix.diagonal_pow]
  congr 1

/-- Squaring the nonnegative natural clock preserves its entire polynomial algebra. -/
theorem naturalClock_square_adjoin_eq (n : ℕ) :
    Algebra.adjoin ℝ ({naturalClock n ^ 2} : Set (Matrix (Fin n) (Fin n) ℝ)) =
      Algebra.adjoin ℝ ({naturalClock n} : Set (Matrix (Fin n) (Fin n) ℝ)) := by
  rw [naturalClock, Matrix.diagonal_pow, diagonal_adjoin_eq_iff]
  intro i j
  exact sq_eq_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Endomorphisms preserving a fixed subspace form an algebra. -/
def matrixPreserver (U : Submodule ℝ (I → ℝ)) : Subalgebra ℝ (Matrix I I ℝ) where
  carrier := {A | ∀ x ∈ U, A *ᵥ x ∈ U}
  zero_mem' := by intro x hx; simp
  one_mem' := by intro x hx; simpa only [Matrix.one_mulVec] using hx
  add_mem' := by
    intro A B hA hB x hx
    rw [Matrix.add_mulVec]
    exact U.add_mem (hA x hx) (hB x hx)
  mul_mem' := by
    intro A B hA hB x hx
    rw [← Matrix.mulVec_mulVec]
    exact hA _ (hB x hx)
  algebraMap_mem' := by
    intro c x hx
    have he : (algebraMap ℝ (Matrix I I ℝ)) c *ᵥ x = c • x := by
      ext i
      simp [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]
    rw [he]
    exact U.smul_mem c hx

/-- Spectral recovery transfers invariant subspaces without choosing an eigenbasis in the subspace. -/
theorem diagonal_preserves_of_fiber_refinement (a b : I → ℝ)
    (U : Submodule ℝ (I → ℝ))
    (hfib : ∀ i j, b i = b j → a i = a j)
    (hb : ∀ x ∈ U, Matrix.diagonal b *ᵥ x ∈ U) :
    ∀ x ∈ U, Matrix.diagonal a *ᵥ x ∈ U := by
  have hle : Algebra.adjoin ℝ {Matrix.diagonal b} ≤ matrixPreserver U := by
    apply Algebra.adjoin_le
    rintro _ rfl
    exact hb
  exact hle ((diagonal_mem_adjoin_iff a b).mpr hfib)

/-- The natural clock and its square have precisely the same invariant subspaces. -/
theorem naturalClock_square_preserves_iff (n : ℕ) (U : Submodule ℝ (Fin n → ℝ)) :
    (∀ x ∈ U, naturalClock n ^ 2 *ᵥ x ∈ U) ↔
      ∀ x ∈ U, naturalClock n *ᵥ x ∈ U := by
  constructor
  · intro h
    apply diagonal_preserves_of_fiber_refinement (fun i : Fin n => (i.val : ℝ))
      (fun i : Fin n => (i.val : ℝ) ^ 2) U
    · intro i j hij
      exact (sq_eq_sq₀ (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mp hij
    · rwa [naturalClock_sq_diagonal] at h
  · intro h x hx
    rw [pow_two, ← Matrix.mulVec_mulVec]
    exact h _ (h x hx)

/-- The squared clock and the same rank-one boundary still generate every matrix. -/
theorem naturalClock_square_boundary_adjoin_eq_top (n : ℕ) :
    Algebra.adjoin ℝ ({naturalClock n ^ 2, clockBoundary n} :
      Set (Matrix (Fin n) (Fin n) ℝ)) = ⊤ := by
  rw [naturalClock_sq_diagonal]
  have hinj : Function.Injective (fun i : Fin n => (i.val : ℝ) ^ 2) := by
    intro i j hij
    apply Fin.ext
    have h := (sq_eq_sq₀ (Nat.cast_nonneg i.val) (Nat.cast_nonneg j.val)).mp hij
    exact_mod_cast h
  have h := simpleClock_rankOne_generatedSubalgebra_eq_top
    (fun i : Fin n => (i.val : ℝ) ^ 2) (fun _ => 1) hinj (fun _ => one_ne_zero)
  have hb : (fun _ _ : Fin n => (1 : ℝ) * 1) = clockBoundary n := by
    funext i j
    exact one_mul 1
  rw [hb] at h
  exact h

#print axioms exists_polynomial_on_fibers_iff
#print axioms diagonal_adjoin_eq_iff
#print axioms diagonal_square_recovery_iff
#print axioms naturalClock_square_adjoin_eq
#print axioms naturalClock_square_preserves_iff
#print axioms naturalClock_square_boundary_adjoin_eq_top

end GaloisForLFunctions.RepresentationLifting.Filtered
