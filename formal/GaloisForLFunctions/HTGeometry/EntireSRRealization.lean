import GaloisForLFunctions.HTGeometry.SRRealizationDimension
import GaloisForLFunctions.HTGeometry.ArgumentScalingInvariance

/-!
# Entire realizations in a prescribed number of variables

`SRRealization d` asks only that nonzero Stanley–Reisner classes have *nonconstant* carriers, with no
analytic condition at all.  That cannot define an intrinsic dimension: for every `d ≥ 1` and every
`ℚ`-independent step family an arbitrary facet antichain is realized by set-theoretic carriers, so
the predicate `Nonempty (SRRealization d facets)` holds at `d = 1` for complexes whose one-variable
analytic realizations are impossible.  What the dimension exclusions consume is the analytic
condition of `ScalarSRRealization`, and the `d`-variable datum has to carry it too.

`EntireSRRealization d facets` is that datum: entire carriers on `ℂ^d`, vertex coordinates acting as
difference operators along `ℚ`-independent steps, and nonconstant carriers for nonzero classes.
`HTEntireSRRealization` strengthens the analytic condition to hypertranscendence of some complex
line restriction, which at `d = 1` is exactly `ScalarSRRealization`.

* `EntireSRRealization.toSRRealization`, `HTEntireSRRealization.toEntireSRRealization` — the
  forgetful maps;
* `HTEntireSRRealization.toScalarSRRealization` — the `d = 1` hypertranscendental datum is the
  scalar one, since a line restriction is an affine reparametrization;
* `const_of_three_independent_periods` — three `ℚ`-independent periods make a meromorphic normal
  form constant;
* `isEmpty_entireSRRealization_zero`, `not_boundaryWedgeHTRealizable_one` — both dimensions below
  two are excluded for the boundary wedge;
* `boundaryWedge_htDim_eq_two_of_entireRealizable` — the intrinsic dimension is `2` as soon as an
  entire two-variable realization exists.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

variable {α : Type*} [DecidableEq α]

/-- **An entire `d`-variable Stanley–Reisner realization.**  `ℚ`-independent translation steps in
`ℂ^d`, an entire carrier map on Stanley–Reisner classes along which the vertex coordinates act as
difference operators, and nonconstant carriers for nonzero classes. -/
structure EntireSRRealization (d : ℕ) (facets : Finset (Finset α)) where
  /-- The translation step attached to each vertex. -/
  ω : α → (Fin d → ℂ)
  /-- The steps are `ℚ`-linearly independent. -/
  indep : LinearIndependent ℚ ω
  /-- The carrier of a Stanley–Reisner class. -/
  carrier : stanleyReisnerRing ℂ facets → ((Fin d → ℂ) → ℂ)
  /-- Carriers are entire. -/
  carrier_entire : ∀ q, Differentiable ℂ (carrier q)
  /-- The zero class has zero carrier. -/
  carrier_zero : carrier 0 = 0
  /-- The vertex coordinate `x_v` acts as the difference operator along `ω v`. -/
  carrier_vertex : ∀ (v : α) (q : stanleyReisnerRing ℂ facets),
    carrier (srVertexX ℂ facets v * q) = fun z => carrier q (z + ω v) - carrier q z
  /-- A nonzero class has a nonconstant carrier. -/
  carrier_nonconstant : ∀ q : stanleyReisnerRing ℂ facets, q ≠ 0 →
    ∃ z w, carrier q z ≠ carrier q w

/-- **A hypertranscendental entire `d`-variable realization.**  The same datum with the analytic
condition strengthened: a nonzero class has a hypertranscendental restriction to some complex
line. -/
structure HTEntireSRRealization (d : ℕ) (facets : Finset (Finset α)) where
  /-- The translation step attached to each vertex. -/
  ω : α → (Fin d → ℂ)
  /-- The steps are `ℚ`-linearly independent. -/
  indep : LinearIndependent ℚ ω
  /-- The carrier of a Stanley–Reisner class. -/
  carrier : stanleyReisnerRing ℂ facets → ((Fin d → ℂ) → ℂ)
  /-- Carriers are entire. -/
  carrier_entire : ∀ q, Differentiable ℂ (carrier q)
  /-- The zero class has zero carrier. -/
  carrier_zero : carrier 0 = 0
  /-- The vertex coordinate `x_v` acts as the difference operator along `ω v`. -/
  carrier_vertex : ∀ (v : α) (q : stanleyReisnerRing ℂ facets),
    carrier (srVertexX ℂ facets v * q) = fun z => carrier q (z + ω v) - carrier q z
  /-- A nonzero class has a hypertranscendental restriction to some complex line. -/
  carrier_ht : ∀ q : stanleyReisnerRing ℂ facets, q ≠ 0 →
    ∃ z w : Fin d → ℂ, Hypertranscendental fun t : ℂ => carrier q (z + t • w)

namespace EntireSRRealization

variable {d : ℕ} {facets : Finset (Finset α)}

/-- **An entire realization is a realization.** -/
noncomputable def toSRRealization (R : EntireSRRealization d facets) :
    SRRealization d facets where
  ω := R.ω
  indep := R.indep
  carrier := R.carrier
  carrier_zero := R.carrier_zero
  carrier_vertex := R.carrier_vertex
  carrier_nonconstant := R.carrier_nonconstant

/-! ### The one-variable reading -/

/-- The scalar reading of a one-variable realization. -/
noncomputable def scalarCarrier (R : EntireSRRealization 1 facets)
    (q : stanleyReisnerRing ℂ facets) : ℂ → ℂ :=
  fun t => R.carrier q fun _ => t

omit [DecidableEq α] in
theorem differentiable_scalarCarrier (R : EntireSRRealization 1 facets)
    (q : stanleyReisnerRing ℂ facets) : Differentiable ℂ (R.scalarCarrier q) :=
  (R.carrier_entire q).comp (differentiable_pi.mpr fun _ => differentiable_id)

omit [DecidableEq α] in
theorem meromorphicNFOn_scalarCarrier (R : EntireSRRealization 1 facets)
    (q : stanleyReisnerRing ℂ facets) :
    MeromorphicNFOn (R.scalarCarrier q) Set.univ := fun z _ =>
  ((R.differentiable_scalarCarrier q).analyticAt z).meromorphicNFAt

omit [DecidableEq α] in
/-- On a one-element index every vector is the constant vector at its unique entry. -/
theorem eq_const_one (z : Fin 1 → ℂ) : z = fun _ => z 0 := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  rw [hi]

omit [DecidableEq α] in
/-- **Annihilation becomes periodicity.**  If the vertex coordinate `x_v` kills a class, the step
`ω v` is a period of the scalar carrier. -/
theorem periodic_scalarCarrier_of_mul_eq_zero (R : EntireSRRealization 1 facets) {v : α}
    {q : stanleyReisnerRing ℂ facets} (h : srVertexX ℂ facets v * q = 0) :
    Function.Periodic (R.scalarCarrier q) (R.ω v 0) := by
  have hz : (fun z => R.carrier q (z + R.ω v) - R.carrier q z) = 0 := by
    rw [← R.carrier_vertex v q, h, R.carrier_zero]
  intro t
  have hval : R.carrier q ((fun _ => t) + R.ω v) - R.carrier q (fun _ => t) = 0 :=
    congrFun hz fun _ => t
  have hsum : ((fun _ => t) + R.ω v) = fun _ => t + R.ω v 0 := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    rw [hi]
    rfl
  show R.carrier q (fun _ => t + R.ω v 0) = R.carrier q fun _ => t
  rw [← hsum]
  exact sub_eq_zero.mp hval

end EntireSRRealization

namespace HTEntireSRRealization

variable {d : ℕ} {facets : Finset (Finset α)}

omit [DecidableEq α] in
/-- A hypertranscendental line restriction forces the carrier to be nonconstant. -/
theorem exists_ne_of_ht (R : HTEntireSRRealization d facets)
    {q : stanleyReisnerRing ℂ facets} (hq : q ≠ 0) :
    ∃ z w, R.carrier q z ≠ R.carrier q w := by
  obtain ⟨z, w, hht⟩ := R.carrier_ht q hq
  by_contra hconst
  refine not_hypertranscendental_of_const (fun t u => ?_) hht
  by_contra hne
  exact hconst ⟨_, _, hne⟩

/-- **A hypertranscendental realization is an entire realization.** -/
noncomputable def toEntireSRRealization (R : HTEntireSRRealization d facets) :
    EntireSRRealization d facets where
  ω := R.ω
  indep := R.indep
  carrier := R.carrier
  carrier_entire := R.carrier_entire
  carrier_zero := R.carrier_zero
  carrier_vertex := R.carrier_vertex
  carrier_nonconstant := fun _ hq => R.exists_ne_of_ht hq

/-- On a one-element index the affine line through `z` in direction `w` is the affine map
`t ↦ z 0 + t * w 0`. -/
theorem line_eq (z w : Fin 1 → ℂ) (t : ℂ) : z + t • w = fun _ => z 0 + t * w 0 := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  simp

set_option linter.unusedSectionVars false in
theorem hypertranscendental_scalarCarrier (R : HTEntireSRRealization 1 facets)
    {q : stanleyReisnerRing ℂ facets} (hq : q ≠ 0) :
    Hypertranscendental (R.toEntireSRRealization.scalarCarrier q) := by
  obtain ⟨z, w, hht⟩ := R.carrier_ht q hq
  have hline : (fun t : ℂ => R.carrier q (z + t • w))
      = fun t : ℂ => R.toEntireSRRealization.scalarCarrier q (w 0 * t + z 0) := by
    funext t
    rw [line_eq z w t]
    show R.carrier q (fun _ => z 0 + t * w 0) = R.carrier q fun _ => w 0 * t + z 0
    rw [mul_comm (w 0) t, add_comm (z 0) (t * w 0)]
  rw [hline] at hht
  have hw : w 0 ≠ 0 := by
    intro h0
    refine not_hypertranscendental_of_const (fun t u => ?_) hht
    simp [h0]
  have hshift : Hypertranscendental fun t : ℂ =>
      R.toEntireSRRealization.scalarCarrier q (t + z 0) := by
    refine (hypertranscendental_comp_const_mul_iff_uncond
      (f := fun t : ℂ => R.toEntireSRRealization.scalarCarrier q (t + z 0)) hw).mp ?_
    simpa using hht
  exact (hypertranscendental_comp_add_const_iff (z 0)).mp hshift

/-- **A one-variable hypertranscendental realization is a scalar realization.** -/
noncomputable def toScalarSRRealization (R : HTEntireSRRealization 1 facets) :
    ScalarSRRealization facets where
  ω := fun v => R.ω v 0
  indep := by
    have hmap : LinearIndependent ℚ fun v => (LinearEquiv.funUnique (Fin 1) ℚ ℂ) (R.ω v) :=
      R.indep.map' (LinearEquiv.funUnique (Fin 1) ℚ ℂ).toLinearMap (LinearEquiv.ker _)
    exact hmap
  carrier := R.toEntireSRRealization.scalarCarrier
  carrier_meromorphic := R.toEntireSRRealization.meromorphicNFOn_scalarCarrier
  carrier_zero := by
    funext t
    show R.carrier 0 (fun _ => t) = 0
    rw [R.carrier_zero]
    rfl
  carrier_vertex := by
    intro v q
    funext t
    show R.carrier (srVertexX ℂ facets v * q) (fun _ => t) = _
    rw [R.carrier_vertex v q]
    show R.carrier q ((fun _ => t) + R.ω v) - R.carrier q (fun _ => t)
      = R.carrier q (fun _ => t + R.ω v 0) - R.carrier q fun _ => t
    congr 2
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    rfl
  carrier_ht := fun _ hq => R.hypertranscendental_scalarCarrier hq

end HTEntireSRRealization

omit [DecidableEq α] in
/-- **No entire realization in zero variables.**  Every step would be the zero vector of a trivial
space, which no `ℚ`-linearly independent family contains. -/
theorem isEmpty_entireSRRealization_zero {facets : Finset (Finset α)} [Nonempty α] :
    IsEmpty (EntireSRRealization 0 facets) := by
  refine ⟨fun R => ?_⟩
  obtain ⟨v⟩ := ‹Nonempty α›
  exact R.indep.ne_zero v (Subsingleton.elim _ _)

omit [DecidableEq α] in
/-- **Three `ℚ`-independent periods make a meromorphic normal form constant.**  A rank-three integer
period group in `ℂ` is not discrete. -/
theorem const_of_three_independent_periods {f : ℂ → ℂ} (hf : MeromorphicNFOn f Set.univ)
    {ω : α → ℂ} (hindep : LinearIndependent ℚ ω) {T : Finset α} (hcard : 3 ≤ T.card)
    (hper : ∀ v ∈ T, Function.Periodic f (ω v)) : ∀ x y, f x = f y := by
  classical
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hcard
  set g := Finset.equivFinOfCardEq htcard with hg
  set e : Fin 3 → α := fun i => (g.symm i : α) with he
  have hinj : Function.Injective e := by
    intro i j hij
    have hsub : (g.symm i : { x // x ∈ t }) = g.symm j := Subtype.ext hij
    simpa using congrArg g hsub
  have hmem : ∀ i, e i ∈ T := fun i => hts (g.symm i).2
  have hindep3 : LinearIndependent ℚ (ω ∘ e) := hindep.comp e hinj
  have hper3 : ∀ i, Function.Periodic f ((ω ∘ e) i) := fun i => hper (e i) (hmem i)
  exact meromorphicNF_constant_of_rankThree_periods f hf (ω ∘ e) hindep3
    (periodic_of_mem_span_range (f := f) (ω ∘ e) hper3)

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.UniformBoundaryWedge

open GaloisForLFunctions.HTGeometry

variable {r s : ℕ}

/-- Realizability of the boundary wedge in a prescribed number of variables. -/
def BoundaryWedgeHTRealizable (r s d : ℕ) : Prop :=
  Nonempty (EntireSRRealization d (boundaryWedgeFacetFinset r s))

/-- Zero variables never realize the boundary wedge. -/
theorem not_boundaryWedgeHTRealizable_zero (r s : ℕ) :
    ¬ BoundaryWedgeHTRealizable r s 0 := fun h =>
  (isEmpty_entireSRRealization_zero
    (facets := boundaryWedgeFacetFinset r s)).elim h.some

/-- **One variable never realizes the boundary wedge.**  The monomial of a facet is a nonzero class
killed by every vertex coordinate the facet omits, so its carrier acquires `s + 1 ≥ 3`
`ℚ`-independent periods and is therefore constant. -/
theorem not_boundaryWedgeHTRealizable_one (hr : 2 ≤ r) (hs : 2 ≤ s) :
    ¬ BoundaryWedgeHTRealizable r s 1 := by
  rintro ⟨R⟩
  classical
  set facets := boundaryWedgeFacetFinset r s with hfacets
  set A : Finset (BoundaryWedgeVertex r s) := (leftBlock r s).erase none with hA
  have hAmem : A ∈ facets :=
    mem_boundaryWedgeFacetFinset.mpr (Or.inl ⟨none, none_mem_leftBlock, rfl⟩)
  have hanti : FacetAntichain (↑facets : Set (Finset (BoundaryWedgeVertex r s))) := by
    rw [hfacets, coe_boundaryWedgeFacetFinset]
    exact facetAntichain hr hs
  set q : stanleyReisnerRing ℂ facets := ∏ w ∈ A, srVertexX ℂ facets w with hq
  have hqne : q ≠ 0 := srProd_facet_ne_zero facets hAmem
  have hper : ∀ v ∈ (Finset.univ : Finset (BoundaryWedgeVertex r s)) \ A,
      Function.Periodic (R.scalarCarrier q) (R.ω v 0) := fun v hv =>
    R.periodic_scalarCarrier_of_mul_eq_zero
      (srVertexX_mul_srProd_facet_eq_zero facets hanti hAmem (Finset.mem_sdiff.mp hv).2)
  have hindep : LinearIndependent ℚ fun v : BoundaryWedgeVertex r s => R.ω v 0 := by
    have hmap : LinearIndependent ℚ fun v => (LinearEquiv.funUnique (Fin 1) ℚ ℂ) (R.ω v) :=
      R.indep.map' (LinearEquiv.funUnique (Fin 1) ℚ ℂ).toLinearMap (LinearEquiv.ker _)
    exact hmap
  have hcard : 3 ≤ ((Finset.univ : Finset (BoundaryWedgeVertex r s)) \ A).card := by
    rw [hA, card_sdiff_leftFacet none_mem_leftBlock]
    omega
  have hconst := const_of_three_independent_periods
    (R.meromorphicNFOn_scalarCarrier q) hindep hcard hper
  obtain ⟨z, w, hzw⟩ := R.carrier_nonconstant q hqne
  refine hzw ?_
  rw [EntireSRRealization.eq_const_one z, EntireSRRealization.eq_const_one w]
  exact hconst (z 0) (w 0)

/-- **The intrinsic dimension of the boundary wedge is two, given an entire two-variable
realization.**  Dimensions `0` and `1` are excluded unconditionally, by `ℚ`-independence of the
steps and by the period-rank obstruction, so a least-realizable-dimension functional equals `2`. -/
theorem boundaryWedge_htDim_eq_two_of_entireRealizable (hr : 2 ≤ r) (hs : 2 ≤ s)
    {htDim : ℕ} (hfull : BoundaryWedgeHTRealizable r s htDim)
    (hleast : ∀ d, BoundaryWedgeHTRealizable r s d → htDim ≤ d)
    (htwo : BoundaryWedgeHTRealizable r s 2) : htDim = 2 :=
  htDim_eq_two_of_realizability hfull hleast htwo
    (not_boundaryWedgeHTRealizable_zero r s) (not_boundaryWedgeHTRealizable_one hr hs)

end GaloisForLFunctions.UniformBoundaryWedge
