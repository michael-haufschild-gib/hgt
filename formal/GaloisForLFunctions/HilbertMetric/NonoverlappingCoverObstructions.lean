import GaloisForLFunctions.HilbertMetric.NonoverlappingBallCover
import GaloisForLFunctions.HTGeometry.HassePredicate

/-!
# Stable finite obstructions to nonoverlapping coverings

A failed covering has a finite witness stable under small perturbations of
its points. All other coordinates may change arbitrarily. This strengthens
the finite-configuration closedness used in Proposition 9.3 of
Kittipassorn--Phetmak--Sriamorn to arbitrarily indexed configurations.

The finite obstruction theorem also gives a concrete instance of the
corpus's predicate Hasse principle.
-/

noncomputable section
namespace GaloisForLFunctions.HilbertMetric

open Metric Set

variable {ι X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- A surjective isometry preserves and reflects coverability. -/
theorem ballCoverable_isometryEquiv_iff (r : NNReal) (p : ι → X) (e : X ≃ᵢ Y) :
    BallCoverable r (e ∘ p) ↔ BallCoverable r p := by
  constructor
  · rintro ⟨c, hc, hs⟩
    refine ⟨e.symm ∘ c, fun i => ?_, fun i j => ?_⟩
    · simpa only [Function.comp_apply, e.symm_apply_apply] using
        (e.symm.dist_eq (e (p i)) (c i)).le.trans (hc i)
    · rcases hs i j with h | h
      · exact Or.inl (congrArg e.symm h)
      · exact Or.inr (by simpa only [Function.comp_apply, e.symm.dist_eq] using h)
  · rintro ⟨c, hc, hs⟩
    refine ⟨e ∘ c, fun i => ?_, fun i j => ?_⟩
    · simpa only [Function.comp_apply, e.dist_eq] using hc i
    · rcases hs i j with h | h
      · exact Or.inl (congrArg e h)
      · exact Or.inr (by simpa only [Function.comp_apply, e.dist_eq] using h)

/-- Finite packets are places for the covering predicate, with a proved local--global law. -/
def ballCoverableHassePredicate [ProperSpace X] (r : NNReal) :
    HTGeometry.HassePredicate (ι → X) (Finset ι) where
  global := BallCoverable r
  atPlace s p := BallCoverable r (fun i : s => p i)
  local_global := ballCoverable_iff_finset r

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/-- A noncoverable configuration has a finite obstruction with positive perturbation tolerance. -/
theorem not_ballCoverable_iff_robust_finset (r : NNReal) (p : ι → E) :
    ¬ BallCoverable r p ↔ ∃ (s : Finset ι) (ε : ℝ), 0 < ε ∧
      ∀ q : ι → E, (∀ i ∈ s, dist (q i) (p i) < ε) → ¬ BallCoverable r q := by
  classical
  constructor
  · intro hp
    obtain ⟨s, hs⟩ := (not_ballCoverable_iff_finset r p).mp hp
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
      (isClosed_ballCoverable (ι := s) (E := E) r).isOpen_compl
      (fun i : s => p i) hs
    refine ⟨s, ε, hε, fun q hq hc => ?_⟩
    have hdist : dist (fun i : s => q i) (fun i : s => p i) < ε :=
      (dist_pi_lt_iff hε).mpr (fun i => hq i i.property)
    exact hball hdist (hc.comp Subtype.val)
  · rintro ⟨s, ε, hε, h⟩
    exact h p (fun _ _ => by simpa only [dist_self] using hε)

/-- Noncoverability persists on an open neighborhood in every continuous family. -/
theorem isOpen_noncoverable_parameters {T : Type*} [TopologicalSpace T]
    (r : NNReal) (p : T → ι → E) (hp : Continuous p) :
    IsOpen {t | ¬ BallCoverable r (p t)} :=
  (isClosed_coverable_parameters r p hp).isOpen_compl

end GaloisForLFunctions.HilbertMetric

#print axioms GaloisForLFunctions.HilbertMetric.ballCoverable_isometryEquiv_iff
#print axioms GaloisForLFunctions.HilbertMetric.ballCoverableHassePredicate
#print axioms GaloisForLFunctions.HilbertMetric.not_ballCoverable_iff_robust_finset
