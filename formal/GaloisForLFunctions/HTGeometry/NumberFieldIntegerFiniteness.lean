import GaloisForLFunctions.HTGeometry.NumberFieldPrimitiveLattice

/-!
# Finiteness of bounded algebraic-integer matrices

The ring of integers is a discrete lattice in mixed Minkowski space. Consequently, algebraic
integers, and finite matrices of algebraic integers, with uniformly bounded archimedean coordinates
form finite sets. All discreteness and properness inputs come from the number field itself.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField NumberField.InfinitePlace
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Algebraic integers with bounded mixed Minkowski embedding form a finite set. -/
theorem finite_numberFieldIntegers_of_mixedEmbedding_norm_le (R : ℝ) :
    {a : 𝓞 K | ‖mixedEmbedding K (a : K)‖ ≤ R}.Finite := by
  let S : Set (𝓞 K) := {a | ‖mixedEmbedding K (a : K)‖ ≤ R}
  have hfinite :
      ((Metric.closedBall (0 : mixedEmbedding.mixedSpace K) R) ∩
        (mixedEmbedding.integerLattice K : Set (mixedEmbedding.mixedSpace K))).Finite :=
    finite_lattice_inter_of_bounded (mixedEmbedding.integerLattice K)
      Metric.isBounded_closedBall
  change S.Finite
  apply Set.Finite.of_finite_image
  · refine hfinite.subset ?_
    rintro x ⟨a, ha, rfl⟩
    change ‖mixedEmbedding K (a : K)‖ ≤ R at ha
    exact ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using ha, ⟨a, rfl⟩⟩
  · intro a _ b _ hab
    apply Subtype.ext
    exact_mod_cast (mixedEmbedding K).injective hab

/-- Matrices of algebraic integers with entrywise bounded mixed embeddings form a finite set. -/
theorem finite_numberFieldIntegerMatrix_of_mixedEmbedding_norm_le
    (n : ℕ) (R : ℝ) :
    {M : Matrix (Fin n) (Fin n) (𝓞 K) |
      ∀ i j, ‖mixedEmbedding K (M i j : K)‖ ≤ R}.Finite := by
  classical
  let S : Set (𝓞 K) := {a | ‖mixedEmbedding K (a : K)‖ ≤ R}
  have hS : S.Finite := finite_numberFieldIntegers_of_mixedEmbedding_norm_le R
  have hbox :
      {M : Matrix (Fin n) (Fin n) (𝓞 K) |
        ∀ i j, ‖mixedEmbedding K (M i j : K)‖ ≤ R} =
        Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => S)) := by
    ext M
    constructor
    · intro hM i _ j _
      exact hM i j
    · intro hM i j
      exact hM i (Set.mem_univ i) j (Set.mem_univ j)
  rw [hbox]
  exact Set.Finite.pi fun _ => Set.Finite.pi fun _ => hS

/-- Separate bounds at every real and complex place imply finiteness of integral matrices. -/
theorem finite_numberFieldIntegerMatrix_of_archimedean_bound
    (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    {M : Matrix (Fin n) (Fin n) (𝓞 K) |
      (∀ i j, ∀ w : {w : InfinitePlace K // IsReal w},
        |InfinitePlace.embedding_of_isReal w.prop (M i j : K)| ≤ R) ∧
      (∀ i j, ∀ w : {w : InfinitePlace K // IsComplex w},
        ‖w.val.embedding (M i j : K)‖ ≤ R)}.Finite := by
  refine (finite_numberFieldIntegerMatrix_of_mixedEmbedding_norm_le
    (K := K) n R).subset ?_
  intro M hM i j
  rw [Prod.norm_def]
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg hR).2
    intro w
    simpa [Real.norm_eq_abs] using hM.1 i j w
  · apply (pi_norm_le_iff_of_nonneg hR).2
    intro w
    exact hM.2 i j w

end

end GaloisForLFunctions.HTGeometry
