import Mathlib

/-!
# Cofinal pigeonhole over a finite index set

If beyond every bound there is a radius carrying *some* index from a finite set, then one index is
carried cofinally.  The proof is by contradiction: each index would fail beyond its own threshold,
and the maximum of the finitely many thresholds contradicts the hypothesis.

This is the shape a Newton-polygon argument needs when the balancing pair may vary with the radius:
finitely many pairs are available, so one of them recurs.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **Cofinal pigeonhole over a finite index set.**  If beyond every bound there is a radius
carrying *some* index from a finite set, then a single index is carried cofinally: otherwise each
index would fail beyond its own threshold, and the maximum of those finitely many thresholds
contradicts the hypothesis. -/
theorem exists_cofinal_of_finite_pigeonhole {ι : Type*} {S : Finset ι} (hS : S.Nonempty)
    {P : ℝ → ι → Prop} (h : ∀ R : ℝ, ∃ x, R ≤ x ∧ ∃ p ∈ S, P x p) :
    ∃ p ∈ S, ∀ R : ℝ, ∃ x, R ≤ x ∧ P x p := by
  classical
  by_contra hcon
  push Not at hcon
  choose! Rf hRf using hcon
  obtain ⟨x, hx, p, hpS, hP⟩ := h (S.sup' hS Rf)
  exact hRf p hpS x (le_trans (Finset.le_sup' Rf hpS) hx) hP

end GaloisForLFunctions.HTGeometry
