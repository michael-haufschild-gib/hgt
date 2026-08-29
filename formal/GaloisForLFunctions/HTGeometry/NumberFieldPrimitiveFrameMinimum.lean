import GaloisForLFunctions.HTGeometry.LatticeSubsetLinearEquivMinimum
import GaloisForLFunctions.HTGeometry.NumberFieldPrimitiveLattice

/-!
# Minimal primitive number-ring vectors in an invertible real frame

This specializes transported lattice-subset minimization to the concrete mixed embedding of a number
ring.  It returns algebraic-integer coordinates and, in rank at least two, a determinant-one matrix
having the minimizing primitive vector as first column.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField
open scoped Classical NumberField

noncomputable section

/-- Mixed embeddings of primitive vectors over `𝓞 K`. -/
def numberFieldPrimitiveVectorSet
    (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Set (Fin n → mixedEmbedding.mixedSpace K) :=
  {x | ∃ a : Fin n → 𝓞 K,
    (∃ p : Fin n → 𝓞 K, ∑ i, p i * a i = 1) ∧
    x = numberFieldIntegerVectorEmbedding K a}

theorem numberFieldPrimitiveVectorSet_nonempty
    (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : 0 < n) :
    (numberFieldPrimitiveVectorSet K n).Nonempty := by
  let i₀ : Fin n := ⟨0, hn⟩
  let e : Fin n → 𝓞 K := fun i ↦ if i = i₀ then 1 else 0
  have hePrimitive : ∃ p : Fin n → 𝓞 K, ∑ i, p i * e i = 1 := by
    refine ⟨e, ?_⟩
    simp [e, i₀]
  exact ⟨numberFieldIntegerVectorEmbedding K e, e, hePrimitive, rfl⟩

theorem numberFieldPrimitiveVectorSet_subset_lattice
    (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    numberFieldPrimitiveVectorSet K n ⊆ numberFieldIntegerVectorLattice K n := by
  rintro x ⟨a, -, rfl⟩
  exact numberFieldIntegerVectorEmbedding_mem_lattice K a

/-- Every invertible real frame on the coordinatewise mixed space has a minimum primitive integral
vector. -/
theorem exists_numberFieldInteger_minimalPrimitiveVector_linearEquiv
    (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : 0 < n)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
    (e : (Fin n → mixedEmbedding.mixedSpace K) ≃L[ℝ] F) :
    ∃ a : Fin n → 𝓞 K,
      (∃ p : Fin n → 𝓞 K, ∑ i, p i * a i = 1) ∧
      ∀ b : Fin n → 𝓞 K,
        (∃ p : Fin n → 𝓞 K, ∑ i, p i * b i = 1) →
        ‖e (numberFieldIntegerVectorEmbedding K a)‖ ≤
          ‖e (numberFieldIntegerVectorEmbedding K b)‖ := by
  rcases exists_minimal_image_norm_mem_of_nonempty_subset
      (numberFieldIntegerVectorLattice K n)
      (numberFieldPrimitiveVectorSet K n)
      (numberFieldPrimitiveVectorSet_nonempty K n hn)
      (numberFieldPrimitiveVectorSet_subset_lattice K n) e with
    ⟨x, ⟨a, haPrimitive, rfl⟩, hx⟩
  refine ⟨a, haPrimitive, ?_⟩
  intro b hbPrimitive
  exact hx _ ⟨b, hbPrimitive, rfl⟩

/-- The transported-norm minimizer extends to a determinant-one integral matrix. -/
theorem exists_numberFieldInteger_minimalPrimitiveVector_linearEquiv_detOneFirstCol
    (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : 2 ≤ n)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
    (e : (Fin n → mixedEmbedding.mixedSpace K) ≃L[ℝ] F) :
    ∃ (a : Fin n → 𝓞 K) (β : Matrix (Fin n) (Fin n) (𝓞 K)),
      (∃ p : Fin n → 𝓞 K, ∑ i, p i * a i = 1) ∧
      (∀ b : Fin n → 𝓞 K,
        (∃ p : Fin n → 𝓞 K, ∑ i, p i * b i = 1) →
        ‖e (numberFieldIntegerVectorEmbedding K a)‖ ≤
          ‖e (numberFieldIntegerVectorEmbedding K b)‖) ∧
      β.det = 1 ∧
      ∀ i, β i ⟨0, lt_of_lt_of_le (Nat.succ_pos 1) hn⟩ = a i := by
  rcases exists_numberFieldInteger_minimalPrimitiveVector_linearEquiv K n
      (lt_of_lt_of_le (Nat.succ_pos 1) hn) e with ⟨a, haPrimitive, hamin⟩
  rcases exists_det_one_firstCol_eq n hn a haPrimitive with ⟨β, hβdet, hβcol⟩
  exact ⟨a, β, haPrimitive, hamin, hβdet, hβcol⟩

end

end GaloisForLFunctions.HTGeometry
