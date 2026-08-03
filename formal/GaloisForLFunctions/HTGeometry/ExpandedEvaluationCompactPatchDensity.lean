import GaloisForLFunctions.HTGeometry.ExpandedEvaluationProjectiveStratification
import GaloisForLFunctions.HTGeometry.SmoothAffineControlFamily
import GaloisForLFunctions.HTGeometry.StratifiedParametricAvoidance

/-!
# Compact-patch density for expanded evaluation rank

This is the exact meeting point of the proved incidence theorem, the in-tree stratified
parametric-avoidance theorem, and the project's original formal geometry.  The projective incidence calculation supplies a finite real stratification of
the literal rank defect.  A smooth family whose finite probe derivative is onto is then densely
perturbable away from that defect on a compact configuration patch whenever the formal
codimension exceeds the real configuration dimension.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- **Compact-patch expanded-evaluation density law.** -/
theorem expandedEvaluation_compactPatchAvoidance_dense
    {P H row κ : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (exponent : κ → (Fin n →₀ ℕ)) (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (q + 1)) + q < Fintype.card row)
    (F : P × H → (row × Fin n → ℂ))
    (U : Set H) (K : Set H)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hF : ContDiffOn ℝ ⊤ F (Set.univ ×ˢ U))
    (hsubmersion : ∀ p h, h ∈ U →
      Function.Surjective (fderiv ℝ (fun v => F (v, h)) p))
    (hdim : Module.finrank ℝ H <
      2 * (Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1)) :
    Dense (compactConfigurationAvoidance F
      (expandedDifferentialEvaluationRankDefect q n z exponent) K) := by
  exact compactConfigurationAvoidance_dense_of_finiteRegularStratification F
    (expandedDifferentialEvaluationRankDefect q n z exponent)
    (2 * (Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1))
    U K hU hKU (hF.of_le (by simp)) hsubmersion
    (expandedDifferentialEvaluationRankDefect_finiteRegularStratification_unconditional
      q n z hz exponent hexponent hrows)
    hdim

/-- Affine finite-probe form of compact-patch density.  The parameter derivative is discharged
by the exact derivative theorem in `SmoothAffineControlFamily`. -/
theorem expandedEvaluation_affineProbe_compactPatchAvoidance_dense
    {P H row κ : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    [Fintype row] [DecidableEq row] [Fintype κ] [DecidableEq κ]
    (q n : ℕ) (z : row → ℂ) (hz : Function.Injective z)
    (exponent : κ → (Fin n →₀ ℕ)) (hexponent : Function.Injective exponent)
    (hrows : Fintype.card (κ × Fin (q + 1)) + q < Fintype.card row)
    (base : H → (row × Fin n → ℂ))
    (direction : H → (P →L[ℝ] (row × Fin n → ℂ)))
    (U : Set H) (K : Set H)
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hbase : ContDiffOn ℝ ⊤ base U) (hdirection : ContDiffOn ℝ ⊤ direction U)
    (hsurjective : ∀ h ∈ U, Function.Surjective (direction h))
    (hdim : Module.finrank ℝ H <
      2 * (Fintype.card row - Fintype.card (κ × Fin (q + 1)) - q + 1)) :
    Dense (compactConfigurationAvoidance
      (smoothAffineControlFamily base direction)
      (expandedDifferentialEvaluationRankDefect q n z exponent) K) := by
  apply expandedEvaluation_compactPatchAvoidance_dense
    q n z hz exponent hexponent hrows
    (smoothAffineControlFamily base direction) U K hU hKU
  · exact contDiffOn_smoothAffineControlFamily hbase hdirection
  · intro p h hh
    rw [fderiv_smoothAffineControlFamily_probe]
    exact hsurjective h hh
  · exact hdim

end

end GaloisForLFunctions.HTGeometry
