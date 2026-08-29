import GaloisForLFunctions.HTGeometry.LatticeSubsetMinimum
import GaloisForLFunctions.HTGeometry.NumberFieldIntegerMatrixReduction
import GaloisForLFunctions.HTGeometry.UnimodularTransitivity

/-!
# Minimal primitive vectors over a number ring

This file builds the coordinatewise mixed-embedding lattice of `𝓞 K`, proves its topology is
discrete, minimizes the product norm on its primitive-vector subset, and extends the resulting
primitive vector to the first column of a determinant-one integral matrix.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField
open scoped Classical NumberField

noncomputable section

/-- Coordinatewise mixed embeddings of algebraic integers. -/
def numberFieldIntegerVectorLattice
    (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Submodule ℤ (Fin n → mixedEmbedding.mixedSpace K) :=
  Submodule.pi Set.univ fun _ ↦ mixedEmbedding.integerLattice K

/-- The coordinatewise algebraic-integer lattice is the finite product of the one-coordinate
lattices. -/
def numberFieldIntegerVectorLatticeHomeomorph
    (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    numberFieldIntegerVectorLattice K n ≃ₜ
      (Fin n → mixedEmbedding.integerLattice K) where
  toFun x i := ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
  invFun x := ⟨fun i ↦ (x i).1, fun i _ ↦ (x i).2⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by funext i; apply Subtype.ext; rfl
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i ↦ continuous_subtype_val.comp (continuous_apply i)

noncomputable instance numberFieldIntegerVectorLattice.discreteTopology
    (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    DiscreteTopology (numberFieldIntegerVectorLattice K n) :=
  (numberFieldIntegerVectorLatticeHomeomorph K n).symm.discreteTopology

/-- The mixed embedding applied coordinatewise to an integral vector. -/
def numberFieldIntegerVectorEmbedding
    (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (a : Fin n → 𝓞 K) : Fin n → mixedEmbedding.mixedSpace K :=
  fun i ↦ mixedEmbedding K (a i : K)

theorem numberFieldIntegerVectorEmbedding_mem_lattice
    (K : Type*) [Field K] [NumberField K] {n : ℕ}
    (a : Fin n → 𝓞 K) :
    numberFieldIntegerVectorEmbedding K a ∈ numberFieldIntegerVectorLattice K n := by
  intro i _
  exact ⟨a i, rfl⟩

/-- Among primitive vectors over `𝓞 K`, one has minimum coordinatewise mixed-embedding norm. -/
theorem exists_numberFieldInteger_minimalPrimitiveVector
    (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : 0 < n) :
    ∃ a : Fin n → 𝓞 K,
      (∃ p : Fin n → 𝓞 K, ∑ i, p i * a i = 1) ∧
      ∀ b : Fin n → 𝓞 K,
        (∃ p : Fin n → 𝓞 K, ∑ i, p i * b i = 1) →
        ‖numberFieldIntegerVectorEmbedding K a‖ ≤
          ‖numberFieldIntegerVectorEmbedding K b‖ := by
  let i₀ : Fin n := ⟨0, hn⟩
  let e : Fin n → 𝓞 K := fun i ↦ if i = i₀ then 1 else 0
  let S : Set (Fin n → mixedEmbedding.mixedSpace K) :=
    {x | ∃ a : Fin n → 𝓞 K,
      (∃ p : Fin n → 𝓞 K, ∑ i, p i * a i = 1) ∧
      x = numberFieldIntegerVectorEmbedding K a}
  have hePrimitive : ∃ p : Fin n → 𝓞 K, ∑ i, p i * e i = 1 := by
    refine ⟨e, ?_⟩
    simp [e, i₀]
  have hSnonempty : S.Nonempty := by
    exact ⟨numberFieldIntegerVectorEmbedding K e, e, hePrimitive, rfl⟩
  have hSlattice : S ⊆ numberFieldIntegerVectorLattice K n := by
    rintro x ⟨a, -, rfl⟩
    exact numberFieldIntegerVectorEmbedding_mem_lattice K a
  rcases exists_minimal_norm_mem_of_nonempty_subset
      (numberFieldIntegerVectorLattice K n) S hSnonempty hSlattice with
    ⟨x, ⟨a, haPrimitive, rfl⟩, hx⟩
  refine ⟨a, haPrimitive, ?_⟩
  intro b hbPrimitive
  exact hx _ ⟨b, hbPrimitive, rfl⟩

/-- A minimum-norm primitive vector extends to the first column of a determinant-one matrix over
`𝓞 K`. -/
theorem exists_numberFieldInteger_minimalPrimitiveVector_detOneFirstCol
    (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ (a : Fin n → 𝓞 K) (β : Matrix (Fin n) (Fin n) (𝓞 K)),
      (∃ p : Fin n → 𝓞 K, ∑ i, p i * a i = 1) ∧
      (∀ b : Fin n → 𝓞 K,
        (∃ p : Fin n → 𝓞 K, ∑ i, p i * b i = 1) →
        ‖numberFieldIntegerVectorEmbedding K a‖ ≤
          ‖numberFieldIntegerVectorEmbedding K b‖) ∧
      β.det = 1 ∧
      ∀ i, β i ⟨0, lt_of_lt_of_le (Nat.succ_pos 1) hn⟩ = a i := by
  rcases exists_numberFieldInteger_minimalPrimitiveVector K n
      (lt_of_lt_of_le (Nat.succ_pos 1) hn) with ⟨a, haPrimitive, hamin⟩
  rcases exists_det_one_firstCol_eq n hn a haPrimitive with ⟨β, hβdet, hβcol⟩
  exact ⟨a, β, haPrimitive, hamin, hβdet, hβcol⟩

end

end GaloisForLFunctions.HTGeometry
