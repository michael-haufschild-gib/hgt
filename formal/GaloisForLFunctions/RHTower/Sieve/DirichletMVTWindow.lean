import GaloisForLFunctions.RHTower.Sieve.DirichletMVT

/-!
# The Dirichlet mean value theorem on an arbitrary interval

The tree's mean value theorem is stated on `[0, T]`.  Subtracting two such statements gives the
version on `[U, V]` that a dyadic window needs, at twice the error constant.
-/

open MeasureTheory

namespace RHTower.Sieve

theorem intervalIntegrable_normSq_dirPoly (N : ℕ) (a : Fin N → ℂ) (U V : ℝ) :
    IntervalIntegrable (fun t : ℝ => ‖dirPoly N a t‖ ^ 2) volume U V :=
  (((continuous_dirPoly N a).norm).pow 2).intervalIntegrable U V

/-- **The mean value theorem on a window.**  On `[U, V]` the mean square of a Dirichlet polynomial
is its diagonal `(V - U) ∑ |a_n|²` up to `8 N (1 + log N) ∑ |a_n|²`. -/
theorem dirichlet_meanValue_window (N : ℕ) (a : Fin N → ℂ) (U V : ℝ) :
    |(∫ t in U..V, ‖dirPoly N a t‖ ^ 2) - (V - U) * ∑ m : Fin N, ‖a m‖ ^ 2|
      ≤ 8 * (N : ℝ) * (1 + Real.log N) * ∑ m : Fin N, ‖a m‖ ^ 2 := by
  have hV := dirichlet_meanValue_theorem N a V
  have hU := dirichlet_meanValue_theorem N a U
  have hsplit : (∫ t in U..V, ‖dirPoly N a t‖ ^ 2)
      = (∫ t in (0 : ℝ)..V, ‖dirPoly N a t‖ ^ 2)
        - ∫ t in (0 : ℝ)..U, ‖dirPoly N a t‖ ^ 2 := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_normSq_dirPoly N a 0 U) (intervalIntegrable_normSq_dirPoly N a U V)
    linarith [hadd]
  rw [hsplit]
  have hkey : ((∫ t in (0 : ℝ)..V, ‖dirPoly N a t‖ ^ 2)
        - ∫ t in (0 : ℝ)..U, ‖dirPoly N a t‖ ^ 2) - (V - U) * ∑ m : Fin N, ‖a m‖ ^ 2
      = ((∫ t in (0 : ℝ)..V, ‖dirPoly N a t‖ ^ 2) - V * ∑ m : Fin N, ‖a m‖ ^ 2)
        - ((∫ t in (0 : ℝ)..U, ‖dirPoly N a t‖ ^ 2) - U * ∑ m : Fin N, ‖a m‖ ^ 2) := by
    ring
  rw [hkey]
  refine le_trans (abs_sub _ _) ?_
  linarith

end RHTower.Sieve
