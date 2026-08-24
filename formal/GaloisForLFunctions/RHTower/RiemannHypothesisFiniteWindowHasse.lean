import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.RHTower.WindowRelation

/-!
# Finite-window Hasse principle for the Riemann hypothesis

The complete dyadic reflection-window congruence surface is packaged as a predicate-level Hasse
principle for RH.  Its obstruction theorem says that failure of RH is witnessed by one finite
reflection-closed zero packet at one dyadic level.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- One dyadic level together with a finite ξ-zero window and its proposed multiplicities. -/
structure XiFiniteWindowPlace where
  level : ℕ
  support : Finset ℂ
  multiplicity : ℂ → ℕ

/-- The multiplicity congruence required at one finite reflection-window place. -/
def xiFiniteWindowRelationAt (P : XiFiniteWindowPlace) : Prop :=
  (∀ z ∈ P.support, xi z = 0) →
  (∀ z ∈ P.support, (P.multiplicity z : ℕ∞) = analyticOrderAt xi z) →
  (∀ z ∈ P.support, lineReflect z ∈ P.support) →
  (∑ z ∈ P.support, P.multiplicity z ≡
    ∑ z ∈ P.support.filter (fun z => z.re = 1 / 2), P.multiplicity z
      [MOD 2 ^ (P.level + 1)])

/-- RH is a Hasse predicate over all finite dyadic reflection-window places. -/
def riemannHypothesisFiniteWindowHassePredicate :
    HassePredicate Unit XiFiniteWindowPlace where
  global _ := RiemannHypothesis
  atPlace P _ := xiFiniteWindowRelationAt P
  local_global _ := by
    constructor
    · intro hRH P
      exact (rh_iff_all_finite_window_relations_all_levels.mp hRH)
        P.level P.support P.multiplicity
    · intro h
      apply rh_iff_all_finite_window_relations_all_levels.mpr
      intro k t m
      exact h ⟨k, t, m⟩

/-- False RH is equivalent to one finite, reflection-closed multiplicity-congruence obstruction. -/
theorem not_riemannHypothesis_iff_exists_finite_window_congruence_failure :
    ¬ RiemannHypothesis ↔
      ∃ k : ℕ, ∃ t : Finset ℂ, ∃ m : ℂ → ℕ,
        (∀ z ∈ t, xi z = 0) ∧
        (∀ z ∈ t, (m z : ℕ∞) = analyticOrderAt xi z) ∧
        (∀ z ∈ t, lineReflect z ∈ t) ∧
        ¬ (∑ z ∈ t, m z ≡
          ∑ z ∈ t.filter (fun z => z.re = 1 / 2), m z [MOD 2 ^ (k + 1)]) := by
  rw [show (¬ RiemannHypothesis) ↔
      ¬ riemannHypothesisFiniteWindowHassePredicate.global () by rfl]
  rw [riemannHypothesisFiniteWindowHassePredicate.not_global_iff_exists_local_not]
  constructor
  · rintro ⟨P, hP⟩
    change ¬ xiFiniteWindowRelationAt P at hP
    unfold xiFiniteWindowRelationAt at hP
    push Not at hP
    exact ⟨P.level, P.support, P.multiplicity, hP⟩
  · rintro ⟨k, t, m, hzero, horder, hreflect, hmod⟩
    refine ⟨⟨k, t, m⟩, ?_⟩
    change ¬ xiFiniteWindowRelationAt ⟨k, t, m⟩
    intro hrelation
    exact hmod (hrelation hzero horder hreflect)

end RHTower
