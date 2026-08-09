import GaloisForLFunctions.HTGeometry.FiniteJetIndistinguishability

/-!
# Constitutive finite-jet realization boundary

Every prescribed finite analytic jet is realized by both a differentially algebraic function and a
hypertranscendental function.  In the finite-jet topology both global law classes are dense, have
empty interior, are nonclosed, and cannot be separated by a continuous Boolean classifier.

This is a closed analytic realization-boundary theorem for the universal-law field.  No computation
tactic, project postulate, or unproved premise is used.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open _root_.HTGeometry

noncomputable section

/-- No continuous Boolean observer on the finite-jet topology can classify differentially
algebraic versus hypertranscendental laws. -/
theorem constitutiveFiniteJet_noContinuousBoolClassifier :
    ¬ ∃ Φ : JetSpace → Bool,
      Continuous Φ ∧
      (∀ f : JetSpace, DifferentiallyAlgebraic (ofJetSpace f) → Φ f = false) ∧
      (∀ f : JetSpace, Hypertranscendental (ofJetSpace f) → Φ f = true) := by
  rintro ⟨Φ, hΦ, hDA, hHT⟩
  exact no_continuous_classifier Φ hΦ (by simp) hDA hHT

/-- Closed package of the analytic realization-boundary law: exact finite-observer double
realization, mutual density, empty interiors, nonclosed global strata, and classifier no-go. -/
theorem constitutiveFiniteJet_realizationBoundary_law :
    (∀ r : ℕ, ∀ c : ℕ → ℂ, ∃ p h : ℂ → ℂ,
      (∀ j ≤ r, jetAtZero j p = c j) ∧
      (∀ j ≤ r, jetAtZero j h = c j) ∧
      DifferentiallyAlgebraic p ∧ Hypertranscendental h) ∧
    Dense {f : JetSpace | DifferentiallyAlgebraic (ofJetSpace f)} ∧
    Dense {f : JetSpace | Hypertranscendental (ofJetSpace f)} ∧
    interior {f : JetSpace | DifferentiallyAlgebraic (ofJetSpace f)} = ∅ ∧
    interior {f : JetSpace | Hypertranscendental (ofJetSpace f)} = ∅ ∧
    ¬ IsClosed {f : JetSpace | DifferentiallyAlgebraic (ofJetSpace f)} ∧
    ¬ IsClosed {f : JetSpace | Hypertranscendental (ofJetSpace f)} ∧
    ¬ ∃ Φ : JetSpace → Bool,
      Continuous Φ ∧
      (∀ f : JetSpace, DifferentiallyAlgebraic (ofJetSpace f) → Φ f = false) ∧
      (∀ f : JetSpace, Hypertranscendental (ofJetSpace f) → Φ f = true) := by
  exact ⟨exists_finiteJet_da_and_ht,
    dense_differentiallyAlgebraic,
    dense_hypertranscendental,
    interior_differentiallyAlgebraic_eq_empty,
    interior_hypertranscendental_eq_empty,
    not_isClosed_differentiallyAlgebraic,
    not_isClosed_hypertranscendental,
    constitutiveFiniteJet_noContinuousBoolClassifier⟩

end


end GaloisForLFunctions.HTGeometry
