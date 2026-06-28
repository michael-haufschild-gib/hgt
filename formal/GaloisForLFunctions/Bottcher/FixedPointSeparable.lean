/-
# Fixed-point separability from no multiplier-one roots

Focused algebraic bridge for the hRigid connected route.  The event selector needs separable
fixed-point polynomials; dynamically, that condition is exactly the absence of multiplier `1` at the
fixed points of `f_c^[p]`.  This file proves the reusable implication without changing the high-level
hRigid endpoints.
-/
import GaloisForLFunctions.Bottcher.IndexResonance

open Polynomial Finset Filter

namespace Bottcher

/-- A nonzero complex polynomial is separable if its derivative is nonzero at every root.

This is the converse of the repeatedly used `eval_derivative_ne_zero_of_separable`, specialized to
`ℂ`: repeated roots are detected by `rootMultiplicity > 1`, and over an algebraically closed field
`roots.Nodup` is equivalent to separability. -/
theorem separable_of_derivative_ne_zero_at_roots {Q : Polynomial ℂ} (hQ : Q ≠ 0)
    (hderiv : ∀ z : ℂ, Q.IsRoot z → Q.derivative.eval z ≠ 0) :
    Q.Separable := by
  classical
  have hnodup : Q.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro z
    rw [Q.count_roots]
    exact not_lt.mp (by
      intro hgt
      have hboth := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hQ).mp hgt
      exact (hderiv z hboth.1) hboth.2)
  exact (Polynomial.nodup_roots_iff_of_splits hQ (IsAlgClosed.splits Q)).mp hnodup

/-- If no fixed point of `f_c^[p]` has multiplier `1`, then `f_c^[p] - X` is separable. -/
theorem fixedPointPoly_separable_of_multiplier_ne_one (c : ℂ) {p : ℕ} (hp : 1 ≤ p)
    (hmul : ∀ z : ℂ, (fixedPointPoly c p).IsRoot z →
      (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) ≠ (1 : ℂ)) :
    (fixedPointPoly c p).Separable := by
  apply separable_of_derivative_ne_zero_at_roots (fixedPointPoly_ne_zero c hp)
  intro z hz
  rw [eval_deriv_fixedPointPoly]
  exact sub_ne_zero.mpr (hmul z hz)

/-- Eventual no-multiplier-one data supplies eventual fixed-point separability. -/
theorem eventually_fixedPointPoly_separable_of_eventually_multiplier_ne_one (c : ℂ)
    (hmul : ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧
      ∀ z : ℂ, (fixedPointPoly c p).IsRoot z →
        (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) ≠ (1 : ℂ)) :
    ∀ᶠ p : ℕ in atTop, 1 ≤ p ∧ (fixedPointPoly c p).Separable :=
  hmul.mono fun _ hp =>
    ⟨hp.1, fixedPointPoly_separable_of_multiplier_ne_one c hp.1 hp.2⟩

/-- Frequently many no-multiplier-one periods supply frequently many separable periods. -/
theorem frequently_fixedPointPoly_separable_of_frequently_multiplier_ne_one (c : ℂ)
    (hmul : ∃ᶠ p : ℕ in atTop, 1 ≤ p ∧
      ∀ z : ℂ, (fixedPointPoly c p).IsRoot z →
        (∏ k ∈ Finset.range p, 2 * (quadratic c)^[k] z) ≠ (1 : ℂ)) :
    ∃ᶠ p : ℕ in atTop, 1 ≤ p ∧ (fixedPointPoly c p).Separable :=
  hmul.mono fun _ hp =>
    ⟨hp.1, fixedPointPoly_separable_of_multiplier_ne_one c hp.1 hp.2⟩

end Bottcher
