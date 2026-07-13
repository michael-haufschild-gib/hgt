import GaloisForLFunctions.HTGeometry.CompactConfigurationBaire
import GaloisForLFunctions.HTGeometry.EvaluationRankDefectTopology

/-!
# Uncountable-configuration Baire assembly for expanded evaluation rank

This module joins the concrete closed rectangular rank-defect locus to the compact-configuration
Baire theorem.  Once density on every compact configuration patch is supplied, one parameter
simultaneously gives full coefficient-uniform evaluation rank for every configuration.  The
dependent version performs the same assembly for countably many differential relation patterns.

The remaining non-topological input is exactly compact-patch density; in the carrier application
this is the classical Whitney-stratified parametric-transversality step instantiated with the
project's formal incidence-codimension and control theorems.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- **Expanded-evaluation configuration law.** Compact-patch density for the literal rectangular
rank defect promotes to a dense residual set of parameters having full evaluation column rank at
every point of a sigma-compact configuration space. -/
theorem expandedEvaluation_globalFullRank_dense_residual_of_sigmaCompact
    {X H row κ : Type*}
    [TopologicalSpace X] [BaireSpace X]
    [TopologicalSpace H] [SigmaCompactSpace H]
    [Fintype row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (exponent : κ → (Fin n →₀ ℕ))
    (F : X × H → (row × Fin n → ℂ)) (hF : Continuous F)
    (hdense : ∀ K : Set H, IsCompact K →
      Dense (compactConfigurationAvoidance F
        (expandedDifferentialEvaluationRankDefect q n z exponent) K)) :
    Dense {x | ∀ h,
        Function.Injective
          (expandedDifferentialEvaluationMatrix q n z exponent (F (x, h))).mulVec} ∧
      {x | ∀ h,
        Function.Injective
          (expandedDifferentialEvaluationMatrix q n z exponent (F (x, h))).mulVec} ∈
        residual X := by
  have h := globalConfigurationAvoidance_dense_residual_of_sigmaCompact
    F hF (expandedDifferentialEvaluationRankDefect q n z exponent)
    (expandedDifferentialEvaluationRankDefect_isClosed q n z exponent) hdense
  simpa only [globalConfigurationAvoidance, mem_setOf_eq,
    mem_expandedDifferentialEvaluationRankDefect_iff, not_not] using h

/-- **Countable full-translation evaluation law.** If every compact configuration patch has dense
avoidance for each member of a countable family of finite expanded relation patterns, then one
dense residual parameter set has full coefficient-uniform rank for every pattern and every
configuration. -/
theorem countableExpandedEvaluation_globalFullRank_dense_residual_of_sigmaCompact
    {X : Type*} [TopologicalSpace X] [BaireSpace X]
    (H row κ : ℕ → Type*)
    [∀ i, TopologicalSpace (H i)] [∀ i, SigmaCompactSpace (H i)]
    [∀ i, Fintype (row i)] [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    (q n : ℕ → ℕ) (z : (i : ℕ) → row i → ℂ)
    (exponent : (i : ℕ) → κ i → (Fin (n i) →₀ ℕ))
    (F : (i : ℕ) → X × H i → (row i × Fin (n i) → ℂ))
    (hF : ∀ i, Continuous (F i))
    (hdense : ∀ (i : ℕ) (K : Set (H i)), IsCompact K →
      Dense (compactConfigurationAvoidance (F i)
        (expandedDifferentialEvaluationRankDefect (q i) (n i) (z i) (exponent i)) K)) :
    Dense {x | ∀ i h,
        Function.Injective
          (expandedDifferentialEvaluationMatrix
            (q i) (n i) (z i) (exponent i) (F i (x, h))).mulVec} ∧
      {x | ∀ i h,
        Function.Injective
          (expandedDifferentialEvaluationMatrix
            (q i) (n i) (z i) (exponent i) (F i (x, h))).mulVec} ∈ residual X := by
  have h := countablePattern_globalConfigurationAvoidance_dense_residual_of_sigmaCompact
    H (fun i => row i × Fin (n i) → ℂ) F hF
    (fun i => expandedDifferentialEvaluationRankDefect
      (q i) (n i) (z i) (exponent i))
    (fun i => expandedDifferentialEvaluationRankDefect_isClosed
      (q i) (n i) (z i) (exponent i)) hdense
  simpa only [mem_expandedDifferentialEvaluationRankDefect_iff, not_not] using h

end

end GaloisForLFunctions.HTGeometry
