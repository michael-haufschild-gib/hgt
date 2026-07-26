import GaloisForLFunctions.HTGeometry.EllipticFreeFacetCodimension

/-!
# Entire realizations need no elliptic input

The one alternative left open by `facetComplement_rankOne_or_lattice` is a facet carrier that is a
hypertranscendental function invariant under a full lattice.  For a **meromorphic** carrier ruling
that out is the elliptic structure theorem, packaged as `EllipticHypertranscendenceFree`.  For an
**entire** carrier it is Liouville's theorem: a lattice-periodic entire function has compact range,
hence is bounded, hence constant.

Since the periodic-pencil realization theorem produces *entire* systems, this removes the elliptic
input entirely for the realizations that actually arise:

* `const_of_lattice_periodic_differentiable` — elliptic Liouville, from mathlib's
  `IsZLattice.isCompact_range_of_periodic` and `Differentiable.apply_eq_apply_of_bounded`;
* `not_hypertranscendental_of_lattice_periodic_differentiable`.

The codimension law itself is stated once, at the level of the analytic datum, in
`EntireFacetRealizationCodimension`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α]

/-- **Elliptic Liouville.**  An entire function invariant under a full lattice is constant: its range
is the continuous image of a compact fundamental set, hence bounded. -/
theorem const_of_lattice_periodic_differentiable (L : PeriodPair) {f : ℂ → ℂ}
    (hdiff : Differentiable ℂ f) (hper : ∀ p ∈ L.lattice, Function.Periodic f p) :
    ∀ x y, f x = f y := by
  intro x y
  exact hdiff.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L.lattice _ hdiff.continuous
      (fun z w hw => hper w hw z)).isBounded x y

/-- An entire function with a full lattice of periods is not hypertranscendental. -/
theorem not_hypertranscendental_of_lattice_periodic_differentiable (L : PeriodPair) {f : ℂ → ℂ}
    (hdiff : Differentiable ℂ f) (hper : ∀ p ∈ L.lattice, Function.Periodic f p) :
    ¬ Hypertranscendental f :=
  not_hypertranscendental_of_const (const_of_lattice_periodic_differentiable L hdiff hper)

end GaloisForLFunctions.HTGeometry
