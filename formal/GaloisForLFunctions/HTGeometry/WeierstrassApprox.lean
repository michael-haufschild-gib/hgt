import GaloisForLFunctions.HTGeometry.UniformIntegralLimit
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Weierstrass approximation in pointwise form

`polynomialFunctions_closure_eq_top` states density as an equality of subalgebras of `C(Icc a b,
ℝ)`.
What a measure-theoretic argument needs is an honest polynomial together with a pointwise bound, so
this module performs the translation: closure membership gives a nearby element of
`polynomialFunctions`, which is by definition the restriction of some `Polynomial ℝ`, and the sup
metric on a compact domain gives the pointwise estimate.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

/-- **Weierstrass, pointwise.**  A continuous function on `[a, b]` is uniformly approximated by an
honest polynomial. -/
theorem exists_poly_approx {a b : ℝ} (f : C(Set.Icc a b, ℝ)) {eps : ℝ} (heps : 0 < eps) :
    ∃ p : Polynomial ℝ, ∀ x : Set.Icc a b, |f x - p.eval (x : ℝ)| < eps := by
  have htop := polynomialFunctions_closure_eq_top a b
  have hmem : f ∈ (polynomialFunctions (Set.Icc a b)).topologicalClosure := by
    rw [htop]; trivial
  have hmem' : f ∈ closure ((polynomialFunctions (Set.Icc a b) :
      Subalgebra ℝ C(Set.Icc a b, ℝ)) : Set C(Set.Icc a b, ℝ)) := hmem
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp hmem' eps heps
  rw [polynomialFunctions_coe] at hg
  obtain ⟨p, hp⟩ := hg
  refine ⟨p, fun x => ?_⟩
  have hpt : dist (f x) (g x) ≤ dist f g := ContinuousMap.dist_apply_le_dist x
  have hgx : g x = p.eval (x : ℝ) := by
    rw [← hp]
    rfl
  rw [← Real.dist_eq, ← hgx]
  exact lt_of_le_of_lt hpt hdist

end HTGeometry
