import GaloisForLFunctions.HTGeometry.ObserverDistanceSymmetry

/-!
# The observer metrics form a metric space

An observer metric is a positive-definite Hermitian form.  The distance of the previous modules —
the second form measured in the frame of the first — vanishes exactly on the diagonal, is
symmetric, and obeys the triangle inequality, so it is a metric in the sense of mathlib.

This is the bulk of the boundary picture: the nonpositively curved space whose asymptotic
directions carry the horizon building.
-/

namespace GaloisForLFunctions.HTGeometry

open Module

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- An observer metric: a positive-definite Hermitian form on the observer space. -/
structure ObserverMetric (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] where
  /-- The underlying form. -/
  form : E →ₗ[ℂ] E
  /-- The form is Hermitian. -/
  isSymm : form.IsSymmetric
  /-- The form is positive definite. -/
  isPos : ∀ v : E, v ≠ 0 → 0 < (inner ℂ v (form v)).re

namespace ObserverMetric

theorem ext {P Q : ObserverMetric E} (h : P.form = Q.form) : P = Q := by
  cases P
  cases Q
  subst h
  rfl

/-- The distance between two observer metrics. -/
noncomputable instance : Dist (ObserverMetric E) where
  dist P Q := observerDist P.isSymm (rfl : finrank ℂ E = finrank ℂ E) Q.isSymm

theorem dist_def (P Q : ObserverMetric E) :
    dist P Q = observerDist P.isSymm (rfl : finrank ℂ E = finrank ℂ E) Q.isSymm := rfl

/-- **The observer metrics form a metric space.**  The three axioms are the vanishing of the
distance exactly on the diagonal, its symmetry, and the triangle inequality — the last being the
nonpositive-curvature theorem for this space. -/
noncomputable instance : MetricSpace (ObserverMetric E) where
  dist P Q := observerDist P.isSymm (rfl : finrank ℂ E = finrank ℂ E) Q.isSymm
  dist_self P := observerDist_self P.isSymm rfl P.isPos
  dist_comm P Q := observerDist_comm P.isSymm Q.isSymm rfl P.isPos Q.isPos
  dist_triangle P Q R :=
    observerDist_triangle P.isSymm Q.isSymm R.isSymm rfl P.isPos Q.isPos R.isPos
  eq_of_dist_eq_zero {P Q} h :=
    (ext ((observerDist_eq_zero_iff P.isSymm rfl P.isPos Q.isSymm Q.isPos).1 h)).symm

end ObserverMetric

end GaloisForLFunctions.HTGeometry
