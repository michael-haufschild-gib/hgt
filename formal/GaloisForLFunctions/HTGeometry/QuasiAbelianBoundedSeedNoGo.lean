import GaloisForLFunctions.HTGeometry.MultivariateEntireFrechetRegularity
import Mathlib.Analysis.Complex.Liouville

/-!
# Globally bounded rank-zero seeds cannot impose a complement zero

The finite-vanishing route for a damped extension requires lower-automorphic
seed columns.  At a rank-zero lower factor the normalised bound demanded by
`AbeDampingBoundBridge` is an ordinary global bound on an entire function.
Liouville then makes every such seed constant, so it cannot both preserve a
nonzero target value and vanish at any complement translate.

This closes a tempting but invalid construction route: finite jet interpolation
alone cannot supply the uniformly normalised seeds at rank zero.  The positive
base construction must instead use its Gaussian-flat Poincare seeds directly.
-/

open Filter Topology Bornology Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Multivariate Liouville for the compact-open entire-source model.** -/
theorem multivariateEntire_apply_eq_of_norm_le {d : ℕ} (f : MultivariateEntire d) {M : ℝ}
    (hbound : ∀ x : Fin d → ℂ, ‖f.1 x‖ ≤ M) (x y : Fin d → ℂ) : f.1 x = f.1 y := by
  have hdiff : Differentiable ℂ f.1 :=
    (MultivariateEntire.contDiff f).differentiable WithTop.top_ne_zero
  have hbdd : IsBounded (Set.range f.1) := by
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨M, ?_⟩
    rintro _ ⟨z, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hbound z
  exact hdiff.apply_eq_apply_of_bounded hbdd x y

/-- **No globally bounded entire seed simultaneously preserves one target value and kills one
complement value.** -/
theorem not_exists_bounded_multivariateEntire_one_zero {d : ℕ} (p q : Fin d → ℂ) :
    ¬ ∃ (f : MultivariateEntire d) (M : ℝ),
      (∀ x : Fin d → ℂ, ‖f.1 x‖ ≤ M) ∧ f.1 p = 1 ∧ f.1 q = 0 := by
  rintro ⟨f, M, hbound, hp, hq⟩
  have h := multivariateEntire_apply_eq_of_norm_le f hbound p q
  rw [hp, hq] at h
  exact one_ne_zero h

/-- **The same obstruction for the polynomial-in-damping-parameter bound consumed by
`AbeDampingBoundBridge`.**  Evaluating the family at `B = 1` reduces it to the preceding
Liouville obstruction. -/
theorem not_exists_polynomially_bounded_seed_family_one_zero {d : ℕ} (p q : Fin d → ℂ) :
    ¬ ∃ (seed : ℝ → MultivariateEntire d) (C : ℝ) (r : ℕ),
      (∀ B : ℝ, 0 ≤ B → ∀ x : Fin d → ℂ, ‖(seed B).1 x‖ ≤ C * B ^ r) ∧
      (∀ B : ℝ, (seed B).1 p = 1) ∧ ∀ B : ℝ, (seed B).1 q = 0 := by
  rintro ⟨seed, C, r, hbound, hp, hq⟩
  apply not_exists_bounded_multivariateEntire_one_zero p q
  refine ⟨seed 1, C, ?_, hp 1, hq 1⟩
  intro x
  simpa using hbound 1 zero_le_one x

end

end GaloisForLFunctions.HTGeometry
