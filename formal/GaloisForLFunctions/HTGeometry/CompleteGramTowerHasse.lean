import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.HTGeometry.CompleteGramTowerTopology

/-!
# Hasse principle for complete Toeplitz Gram towers

Finite Toeplitz Gram sections are local finite-dimensional observations of a probability law.
Their complete tower determines the law, and every unequal pair is already separated at one finite
matrix stage.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- Finite Toeplitz Gram sections form a Hasse family for real probability measures. -/
noncomputable def completeToeplitzGramHasseFamily :
    HasseFamily (ProbabilityMeasure ℝ) ℕ where
  Local N := Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ
  profile := completeToeplitzGramTower
  profile_injective := injective_completeToeplitzGramTower

/-- Probability measures agree exactly when all their finite Toeplitz Gram sections agree. -/
theorem probabilityMeasure_congr_completeToeplitzGram_hasse_iff
    (mu nu : ProbabilityMeasure ℝ) :
    (∀ N, completeToeplitzGramTower mu N = completeToeplitzGramTower nu N) ↔ mu = nu :=
  completeToeplitzGramHasseFamily.pointwise_eq_iff mu nu

/-- Unequal probability measures differ at one finite Toeplitz Gram stage. -/
theorem probabilityMeasure_ne_iff_exists_finiteToeplitzGram_ne
    (mu nu : ProbabilityMeasure ℝ) :
    mu ≠ nu ↔ ∃ N, completeToeplitzGramTower mu N ≠ completeToeplitzGramTower nu N :=
  completeToeplitzGramHasseFamily.ne_iff_exists_local_ne mu nu

end

end GaloisForLFunctions.HTGeometry
