import GaloisForLFunctions.HTGeometry.ExpandedEvaluationCompactPatchDensity
import GaloisForLFunctions.HTGeometry.StratifiedParametricPrevalence

/-!
# Compact-patch expanded-evaluation avoidance is prevalent

The projective incidence stratification of the expanded-evaluation rank defect has codimension
larger than the configuration dimension, so a controllable finite probe avoids it on a compact
patch not merely densely but with probability one — after every deterministic recentring, with one
probe that does not depend on the centre.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Compact-patch expanded-evaluation avoidance has probability one.** -/
theorem measure_expandedEvaluation_compactPatchAvoidance_eq_one
    {d : ℕ} {H row κ : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (exponent : κ → (Fin n →₀ ℕ)) (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (q + 1)) + q < Fintype.card row)
    (F : (Fin d → ℝ) × H → (row × Fin n → ℂ))
    (U K : Set H) (hU : IsOpen U) (hKU : K ⊆ U)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (Set.univ ×ˢ U))
    (hsubmersion : ∀ p h, h ∈ U →
      Function.Surjective (fderiv ℝ (fun v => F (v, h)) p))
    (hdim : Module.finrank ℝ H <
      2 * (Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1))
    (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ] (hμ : μ ≪ volume) :
    μ (compactConfigurationAvoidance F
      (expandedDifferentialEvaluationRankDefect q n z exponent) K) = 1 :=
  measure_compactConfigurationAvoidance_eq_one F
    (expandedDifferentialEvaluationRankDefect q n z exponent)
    (2 * (Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1))
    U K hU hKU hF hsubmersion
    (expandedDifferentialEvaluationRankDefect_finiteRegularStratification_unconditional
      q n z hz exponent hexponent hrows)
    hdim μ hμ

/-- **The affine finite-probe expanded-evaluation avoidance phase is prevalent.** -/
theorem prevalent_expandedEvaluation_affineProbe_compactPatchAvoidance
    {d : ℕ} {X H row κ : Type}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (exponent : κ → (Fin n →₀ ℕ)) (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (q + 1)) + q < Fintype.card row)
    (l : (Fin d → ℝ) →L[ℝ] X)
    (base : H → (row × Fin n → ℂ)) (direction : H → (X →L[ℝ] (row × Fin n → ℂ)))
    (U K : Set H) (hU : IsOpen U) (hKU : K ⊆ U)
    (hbase : ContDiffOn ℝ (⊤ : ℕ∞) base U)
    (hdirection : ContDiffOn ℝ (⊤ : ℕ∞) direction U)
    (hDirection : ∀ h ∈ U, Function.Surjective ((direction h).comp l))
    (hdim : Module.finrank ℝ H <
      2 * (Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1))
    (P : CompactProbe (Fin d → ℝ)) (hP : P.measure ≪ volume)
    (hA : MeasurableSet (compactConfigurationAvoidance
      (smoothAffineControlFamily base direction)
      (expandedDifferentialEvaluationRankDefect q n z exponent) K)) :
    Prevalent (compactConfigurationAvoidance
      (smoothAffineControlFamily base direction)
      (expandedDifferentialEvaluationRankDefect q n z exponent) K) :=
  prevalent_compactConfigurationAvoidance l base direction
    (expandedDifferentialEvaluationRankDefect q n z exponent)
    (2 * (Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1))
    U K hU hKU hbase hdirection hDirection
    (expandedDifferentialEvaluationRankDefect_finiteRegularStratification_unconditional
      q n z hz exponent hexponent hrows)
    hdim P hP hA

end

end GaloisForLFunctions.HTGeometry
