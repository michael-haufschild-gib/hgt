import GaloisForLFunctions.HTGeometry.ScalarSRRealizationBridge

/-!
# Realizations in a prescribed number of variables, and the intrinsic dimension

`ScalarSRRealization` is the one-variable realization datum.  This file gives its `d`-variable form
and uses it to express the intrinsic dimension in the corpus idiom (a predicate `ℕ → Prop` together
with a least-element hypothesis, as in `FiniteShadowCapacity` and
`QuasiAbelianFacetPaletteCompletion`).

* `SRRealization d` — `ℚ`-independent translation steps in `ℂ^d` and a carrier map on
  Stanley–Reisner classes for which the vertex coordinates act as difference operators and nonzero
  classes have nonconstant carriers.  The analytic condition is stated as nonconstancy, which is what
  the dimension exclusions consume and which hypertranscendence implies.
* `SRRealization.ofScalar` — a one-variable realization is a `1`-variable realization, transported
  along `(Fin 1 → ℂ) ≃ ℂ`; nonconstancy comes from hypertranscendence.
* `isEmpty_srRealization_zero` — **no realization in zero variables**: the steps would all be `0`,
  contradicting `ℚ`-independence.  Purely algebraic, no analysis.
* `boundaryWedge_htDim_eq_two_of_realizable` — for the boundary wedge, the intrinsic dimension is
  `2` as soon as a two-variable realization exists: dimensions `0` and `1` are excluded
  unconditionally (`isEmpty_srRealization_zero` and `isEmpty_scalarSRRealization`), so the periodic
  pencil is the only missing input.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α]

/-- **A `d`-variable Stanley–Reisner realization.** -/
structure SRRealization (d : ℕ) (facets : Finset (Finset α)) where
  /-- The translation step attached to each vertex. -/
  ω : α → (Fin d → ℂ)
  /-- The steps are `ℚ`-linearly independent. -/
  indep : LinearIndependent ℚ ω
  /-- The carrier of a Stanley–Reisner class. -/
  carrier : stanleyReisnerRing ℂ facets → ((Fin d → ℂ) → ℂ)
  /-- The zero class has zero carrier. -/
  carrier_zero : carrier 0 = 0
  /-- The vertex coordinate `x_v` acts as the difference operator along `ω v`. -/
  carrier_vertex : ∀ (v : α) (q : stanleyReisnerRing ℂ facets),
    carrier (srVertexX ℂ facets v * q) = fun z => carrier q (z + ω v) - carrier q z
  /-- A nonzero class has a nonconstant carrier. -/
  carrier_nonconstant : ∀ q : stanleyReisnerRing ℂ facets, q ≠ 0 →
    ∃ z w, carrier q z ≠ carrier q w

omit [DecidableEq α] in
/-- **No realization in zero variables.**  All steps would be the zero vector of a trivial space,
which no `ℚ`-linearly independent family contains. -/
theorem isEmpty_srRealization_zero {facets : Finset (Finset α)} [Nonempty α] :
    IsEmpty (SRRealization 0 facets) := by
  refine ⟨fun R => ?_⟩
  obtain ⟨v⟩ := ‹Nonempty α›
  exact R.indep.ne_zero v (Subsingleton.elim _ _)

/-- A one-variable realization gives a `1`-variable realization. -/
noncomputable def SRRealization.ofScalar {facets : Finset (Finset α)}
    (R : ScalarSRRealization facets) : SRRealization 1 facets where
  ω := fun v _ => R.ω v
  indep := by
    have hmap : LinearIndependent ℚ (fun v => (LinearEquiv.funUnique (Fin 1) ℚ ℂ).symm (R.ω v)) :=
      R.indep.map' (LinearEquiv.funUnique (Fin 1) ℚ ℂ).symm.toLinearMap
        (LinearEquiv.ker _)
    exact hmap
  carrier := fun q z => R.carrier q (z 0)
  carrier_zero := by
    funext z
    show R.carrier 0 (z 0) = 0
    rw [R.carrier_zero]
    rfl
  carrier_vertex := by
    intro v q
    funext z
    show R.carrier (srVertexX ℂ facets v * q) (z 0) = _
    rw [R.carrier_vertex v q]
    rfl
  carrier_nonconstant := by
    intro q hq
    by_contra hconst
    have hall : ∀ z w : ℂ, R.carrier q z = R.carrier q w := by
      intro z w
      by_contra hzw
      exact hconst ⟨fun _ => z, fun _ => w, hzw⟩
    exact not_hypertranscendental_of_const hall (R.carrier_ht q hq)

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.UniformBoundaryWedge

open GaloisForLFunctions.HTGeometry

variable {r s : ℕ}

/-- **The intrinsic dimension of the boundary wedge is two, given the two-variable witness.**
Dimensions `0` and `1` are excluded unconditionally — the first by `ℚ`-independence of the steps
(`isEmpty_srRealization_zero`), the second by the period-rank obstruction
(`isEmpty_scalarSRRealization`) — so a least-realizable-dimension functional equals `2` as soon as a
two-variable realization exists.  The hypotheses `hzero` and `hone` only say that the abstract
realizability predicate, at those two dimensions, yields the corresponding concrete datum. -/
theorem boundaryWedge_htDim_eq_two_of_realizable (hr : 2 ≤ r) (hs : 2 ≤ s)
    {HTRealizable : ℕ → Prop} {htDim : ℕ}
    (hfull : HTRealizable htDim) (hleast : ∀ d, HTRealizable d → htDim ≤ d)
    (htwo : HTRealizable 2)
    (hzero : HTRealizable 0 → Nonempty (SRRealization 0 (boundaryWedgeFacetFinset r s)))
    (hone : HTRealizable 1 → Nonempty (ScalarSRRealization (boundaryWedgeFacetFinset r s))) :
    htDim = 2 := by
  refine htDim_eq_two_of_realizability hfull hleast htwo ?_ ?_
  · exact fun h => (isEmpty_srRealization_zero
      (facets := boundaryWedgeFacetFinset r s)).elim (hzero h).some
  · exact fun h => (isEmpty_scalarSRRealization hr hs).elim (hone h).some

end GaloisForLFunctions.UniformBoundaryWedge
