import GaloisForLFunctions.HTGeometry.EllipticLiouvilleFacetCodimension

/-!
# Lattice-periodic functions with prescribed poles

Foundations for the last analytic input of the scalar period-rank law: a hypertranscendental
*meromorphic* function cannot be invariant under a full lattice.  The route is elementary and avoids
contour integration entirely.

For a fixed finite set of pole representatives and a fixed order bound, the lattice-periodic
meromorphic functions with poles confined to that data form a `ℂ`-subspace, and the map sending a
function to its finitely many principal parts has **kernel exactly the constants**: a difference with
no principal part extends analytically and is then constant by Liouville
(`const_of_lattice_periodic_analytic`).  Hence that subspace is finite-dimensional, with dimension at
most one more than the total pole order.  Applying this to the monomials `f^i (f')^j`, whose number
grows quadratically while their total pole order grows linearly, produces a nonzero polynomial
relation `Q(f, f') = 0` — a first-order algebraic differential equation for `f`.

This file records the Liouville kernel step.

* `const_of_lattice_periodic_analytic` — an everywhere-analytic lattice-periodic function is
  constant;
* **`exists_const_sub_of_lattice_periodic`** — two lattice-periodic functions whose difference is
  everywhere analytic differ by a constant.  This is the injectivity-modulo-constants that bounds
  the dimension of a pole-bounded space.
-/

namespace GaloisForLFunctions.HTGeometry

/-- An everywhere-analytic lattice-periodic function is constant. -/
theorem const_of_lattice_periodic_analytic (L : PeriodPair) {f : ℂ → ℂ}
    (han : ∀ z, AnalyticAt ℂ f z) (hper : ∀ p ∈ L.lattice, Function.Periodic f p) :
    ∀ x y, f x = f y :=
  const_of_lattice_periodic_differentiable L (fun z => (han z).differentiableAt) hper

/-- **Two lattice-periodic functions with an everywhere-analytic difference differ by a constant.**
The difference is lattice-periodic and has no poles, hence is constant by Liouville. -/
theorem exists_const_sub_of_lattice_periodic (L : PeriodPair) {f g : ℂ → ℂ}
    (hf : ∀ p ∈ L.lattice, Function.Periodic f p) (hg : ∀ p ∈ L.lattice, Function.Periodic g p)
    (han : ∀ z, AnalyticAt ℂ (fun w => f w - g w) z) :
    ∃ c : ℂ, ∀ z, f z - g z = c := by
  refine ⟨f 0 - g 0, fun z => ?_⟩
  refine const_of_lattice_periodic_analytic L han (fun p hp w => ?_) z 0
  show f (w + p) - g (w + p) = f w - g w
  rw [hf p hp w, hg p hp w]

end GaloisForLFunctions.HTGeometry
