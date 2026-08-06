import GaloisForLFunctions.RHTower.BornTemperatureFactorType
import GaloisForLFunctions.RHTower.DivisorReesBoundaryGraph

/-!
# Transport of the graded symbol from the Euler chamber to the boundary

The graded Rees symbol is defined at every point of the plane, so it is defined on the whole
continuation: on the Euler chamber `Re ≥ 1`, where the Euler product converges, and on the
critical strip, where the boundary lives.

On the Euler chamber the symbol is constant — the single trivial outer square — because `xi` has
no zeros there, and the same holds on the reflected chamber `Re ≤ 0`.  So every nontrivial value
of the symbol field is created strictly inside the critical strip: a nontrivial symbol at a point
forces that point into `0 < Re < 1`.

Consequently the boundary graph of a compact region is finite, its vertex count is bounded by the
number of `xi` zeros there, and a region lying in the Euler chamber carries no vertices at all —
its assembled relative trace is zero.
-/

open scoped BigOperators Matrix

open GaloisForLFunctions

namespace RHTower

noncomputable section

/-! ### The chambers carry no divisor -/

/-- The reflected Euler chamber is also free of `xi` zeros: the functional equation carries
`Re ρ ≤ 0` to `Re (1 - ρ) ≥ 1`. -/
theorem xi_ne_zero_of_re_nonpos {rho : ℂ} (h : rho.re ≤ 0) : xi rho ≠ 0 := fun hz =>
  absurd (xi_zero_re_mem_open_unit hz).1 (not_lt.mpr h)

/-! ### The symbol is constant on both chambers -/

/-- **The Euler chamber is symbol-trivial.**  Where the Euler product converges the graded symbol
is the single outer square of `(1, 0)`, uniformly. -/
theorem xiGradedSymbol_eq_trivial_of_one_le_re {rho : ℂ} (h : 1 ≤ rho.re) {t : ℝ} (ht : t ≠ 0) :
    xiGradedSymbol rho t = Matrix.vecMulVec ![1, 0] ![1, 0] :=
  xiGradedSymbol_eq_trivial (xi_ne_zero_of_one_le_re h) ht

/-- The reflected chamber is symbol-trivial as well. -/
theorem xiGradedSymbol_eq_trivial_of_re_nonpos {rho : ℂ} (h : rho.re ≤ 0) {t : ℝ} (ht : t ≠ 0) :
    xiGradedSymbol rho t = Matrix.vecMulVec ![1, 0] ![1, 0] :=
  xiGradedSymbol_eq_trivial (xi_ne_zero_of_re_nonpos h) ht

/-- **All nontrivial symbol content is created inside the critical strip.**  This is the transport
law along the continuation: starting from the Euler chamber, where the symbol is the constant
trivial projection, the symbol can only change after the passage into `0 < Re < 1`. -/
theorem re_mem_strip_of_xiGradedSymbol_ne_trivial {rho : ℂ} {t : ℝ} (ht : t ≠ 0)
    (h : xiGradedSymbol rho t ≠ Matrix.vecMulVec ![1, 0] ![1, 0]) :
    0 < rho.re ∧ rho.re < 1 := by
  refine ⟨?_, ?_⟩
  · by_contra hle
    exact h (xiGradedSymbol_eq_trivial_of_re_nonpos (not_lt.mp hle) ht)
  · by_contra hge
    exact h (xiGradedSymbol_eq_trivial_of_one_le_re (not_lt.mp hge) ht)

/-- The two chambers agree: the symbol takes one and the same value on all of `Re ≥ 1` and all of
`Re ≤ 0`. -/
theorem xiGradedSymbol_eq_of_outside_strip {rho sigma : ℂ} {t u : ℝ} (ht : t ≠ 0) (hu : u ≠ 0)
    (hrho : rho.re ≤ 0 ∨ 1 ≤ rho.re) (hsigma : sigma.re ≤ 0 ∨ 1 ≤ sigma.re) :
    xiGradedSymbol rho t = xiGradedSymbol sigma u := by
  have hr : xiGradedSymbol rho t = Matrix.vecMulVec ![1, 0] ![1, 0] :=
    hrho.elim (fun h => xiGradedSymbol_eq_trivial_of_re_nonpos h ht)
      (fun h => xiGradedSymbol_eq_trivial_of_one_le_re h ht)
  have hs : xiGradedSymbol sigma u = Matrix.vecMulVec ![1, 0] ![1, 0] :=
    hsigma.elim (fun h => xiGradedSymbol_eq_trivial_of_re_nonpos h hu)
      (fun h => xiGradedSymbol_eq_trivial_of_one_le_re h hu)
  rw [hr, hs]

/-! ### The boundary graph of a compact region -/

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Every vertex of a boundary graph lies strictly inside the critical strip. -/
theorem xiGradedBoundary_vertex_re_mem_strip {rho : V → ℂ} (hz : ∀ w, xi (rho w) = 0) (w : V) :
    0 < (rho w).re ∧ (rho w).re < 1 :=
  xi_zero_re_mem_open_unit (hz w)

omit [DecidableEq V] in
/-- **A compact boundary region carries at most as many vertices as `xi` has zeros there.**  The
vertex count of the boundary graph is therefore finite and explicitly bounded. -/
theorem card_le_card_xi_zeros {rho : V → ℂ} (c : ℂ) (R : ℝ)
    (hmem : ∀ w, rho w ∈ Metric.closedBall c R) (hz : ∀ w, xi (rho w) = 0)
    (hinj : Function.Injective rho) :
    Fintype.card V ≤ (xi_zeros_closedBall_finite c R).toFinset.card := by
  classical
  have := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset V))
    (t := (xi_zeros_closedBall_finite c R).toFinset) rho
    (fun w _ => (Set.Finite.mem_toFinset _).mpr ⟨hmem w, hz w⟩)
    (fun a _ b _ h => hinj h)
  simpa [Finset.card_univ] using this

/-- **The assembled relative trace of a compact boundary region is bounded by its zero count.** -/
theorem trace_xiGradedBoundarySymbol_le_card_xi_zeros {rho : V → ℂ} (c : ℂ) (R : ℝ)
    (hmem : ∀ w, rho w ∈ Metric.closedBall c R) (hz : ∀ w, xi (rho w) = 0)
    (hinj : Function.Injective rho) :
    Matrix.trace (xiGradedBoundarySymbol rho)
      ≤ ((xi_zeros_closedBall_finite c R).toFinset.card : ℝ) := by
  rw [trace_xiGradedBoundarySymbol]
  exact_mod_cast card_le_card_xi_zeros c R hmem hz hinj

omit [Fintype V] [DecidableEq V] in
/-- A boundary graph whose vertices lie in the Euler chamber has no vertices. -/
theorem isEmpty_of_one_le_re {rho : V → ℂ} (hz : ∀ w, xi (rho w) = 0)
    (hre : ∀ w, 1 ≤ (rho w).re) : IsEmpty V :=
  ⟨fun w => xi_ne_zero_of_one_le_re (hre w) (hz w)⟩

/-- **The Euler chamber contributes no relative trace.**  The whole boundary budget is created by
the continuation into the critical strip; nothing of it is visible where the Euler product
converges. -/
theorem trace_xiGradedBoundarySymbol_eq_zero_of_one_le_re {rho : V → ℂ}
    (hz : ∀ w, xi (rho w) = 0) (hre : ∀ w, 1 ≤ (rho w).re) :
    Matrix.trace (xiGradedBoundarySymbol rho) = 0 := by
  haveI := isEmpty_of_one_le_re hz hre
  rw [trace_xiGradedBoundarySymbol, Fintype.card_eq_zero, Nat.cast_zero]

/-- The same on the reflected chamber. -/
theorem trace_xiGradedBoundarySymbol_eq_zero_of_re_nonpos {rho : V → ℂ}
    (hz : ∀ w, xi (rho w) = 0) (hre : ∀ w, (rho w).re ≤ 0) :
    Matrix.trace (xiGradedBoundarySymbol rho) = 0 := by
  haveI : IsEmpty V := ⟨fun w => xi_ne_zero_of_re_nonpos (hre w) (hz w)⟩
  rw [trace_xiGradedBoundarySymbol, Fintype.card_eq_zero, Nat.cast_zero]

end

end RHTower
