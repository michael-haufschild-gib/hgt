import GaloisForLFunctions.HTGeometry.EllipticOrderBound

/-!
# A regular point, and the degenerate case of a vanishing derivative

Two small inputs for the assembly of the elliptic counting argument.

* **`differentiallyAlgebraic_of_deriv_eq_zero`** — a function with identically vanishing derivative
  satisfies the algebraic differential equation `y₁ = 0`.  This disposes of the degenerate case in
  which the derivative carries no information.
* **`exists_nonneg_meromorphicOrderAt`** — a meromorphic function on `ℂ` has a point of nonnegative
  order.  Poles are finite on every compact set, while the unit segment inside `ℂ` is an infinite
  compact set, so not every point can be a pole.  This supplies the regular point at which the
  counting argument reads off the value of a combination.
* `analyticAt_of_nonneg_meromorphicOrderAt` — for a normal-form function, nonnegative order at a
  point means analyticity there.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **A vanishing derivative is already an algebraic differential equation.** -/
theorem differentiallyAlgebraic_of_deriv_eq_zero {f : ℂ → ℂ} (h : ∀ z, deriv f z = 0) :
    DifferentiallyAlgebraic f := by
  refine ⟨1, MvPolynomial.X 2, MvPolynomial.X_ne_zero 2, fun z => ?_⟩
  rw [MvPolynomial.eval_X, show (2 : Fin 3) = Fin.succ 1 from rfl, Fin.cons_succ]
  simpa [iteratedDeriv_one] using h z

/-- The unit segment of the real axis, a compact infinite subset of `ℂ`. -/
private theorem isCompact_realSegment :
    IsCompact ((fun t : ℝ => (t : ℂ)) '' Set.Icc 0 1) :=
  (isCompact_Icc).image (by fun_prop)

private theorem infinite_realSegment :
    ((fun t : ℝ => (t : ℂ)) '' Set.Icc 0 1).Infinite := by
  refine Set.Infinite.image (fun a _ b _ hab => ?_) (Set.Icc_infinite (by norm_num))
  exact_mod_cast hab

/-- **A meromorphic function has a point of nonnegative order.**  Its poles are finite on every
compact set, and the unit segment is an infinite compact set. -/
theorem exists_nonneg_meromorphicOrderAt {f : ℂ → ℂ} (hf : MeromorphicOn f Set.univ) :
    ∃ z₀ : ℂ, 0 ≤ meromorphicOrderAt f z₀ := by
  by_contra hcon
  have hall : ∀ z : ℂ, meromorphicOrderAt f z < 0 := by
    intro z
    exact lt_of_not_ge (not_exists.mp hcon z)
  have hfin := finite_poles_of_isCompact hf isCompact_realSegment
  refine infinite_realSegment (hfin.subset ?_)
  intro z hz
  exact ⟨hz, hall z⟩

/-- For a normal-form function, nonnegative order at a point means analyticity there. -/
theorem analyticAt_of_nonneg_meromorphicOrderAt {f : ℂ → ℂ}
    (hNF : MeromorphicNFOn f Set.univ) {z : ℂ} (h : 0 ≤ meromorphicOrderAt f z) :
    AnalyticAt ℂ f z :=
  (hNF (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp h

end GaloisForLFunctions.HTGeometry
