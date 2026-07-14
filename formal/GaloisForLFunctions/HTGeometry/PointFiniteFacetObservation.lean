import GaloisForLFunctions.HTGeometry.FacetRestrictionEmbedding

/-!
# Point-finite facet observation

For an infinite family of finite facets, complete facet restriction is generally an infinite
packet even for one polynomial.  This module isolates the exact algebraic boundary at which the
packet remains finite: after separating the global constant coordinate, this happens for every
polynomial if and only if the facet family is point-finite.

The second half constructs the coherent finite-support row explicitly.  A nonconstant monomial is
copied to every facet on which it is visible, while the constant monomial is stored once in a
distinguished global coordinate.  Its kernel is exactly the Stanley--Reisner nonface ideal for an
arbitrary (possibly infinite) nonempty facet family.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset MvPolynomial

noncomputable section

/-- Every vertex occurs in only finitely many facets. -/
def PointFiniteFacetFamily {α : Type*} (facets : Set (Finset α)) : Prop :=
  ∀ v, {F | F ∈ facets ∧ v ∈ F}.Finite

/-- Facets on which a monomial is visible. -/
def monomialVisibleFacets {α : Type*} (facets : Set (Finset α))
    (d : α →₀ ℕ) : Set (Finset α) :=
  {F | F ∈ facets ∧ d.support ⊆ F}

/-- Facets on which at least one nonconstant monomial of a polynomial is visible.  Constants are
deliberately omitted: they form one global coordinate rather than one coordinate per facet. -/
def polynomialVisibleFacets {R α : Type*} [CommSemiring R]
    (facets : Set (Finset α)) (P : MvPolynomial α R) : Set (Finset α) :=
  {F | F ∈ facets ∧ ∃ d ∈ P.support, d ≠ 0 ∧ d.support ⊆ F}

/-- Point-finiteness makes the visibility set of every nonconstant monomial finite. -/
theorem monomialVisibleFacets_finite_of_pointFinite
    {α : Type*} (facets : Set (Finset α))
    (hfacets : PointFiniteFacetFamily facets) {d : α →₀ ℕ} (hd : d ≠ 0) :
    (monomialVisibleFacets facets d).Finite := by
  obtain ⟨v, hv⟩ := Finsupp.support_nonempty_iff.mpr hd
  exact (hfacets v).subset (by
    intro F hF
    exact ⟨hF.1, hF.2 hv⟩)

/-- Point-finiteness makes the complete nonconstant facet packet of every polynomial finite. -/
theorem polynomialVisibleFacets_finite_of_pointFinite
    {R α : Type*} [CommSemiring R]
    (facets : Set (Finset α)) (hfacets : PointFiniteFacetFamily facets)
    (P : MvPolynomial α R) :
    (polynomialVisibleFacets facets P).Finite := by
  let D : Set (α →₀ ℕ) := {d | d ∈ P.support ∧ d ≠ 0}
  have hD : D.Finite := P.support.finite_toSet.subset (by
    intro d hd
    exact hd.1)
  have hU : (⋃ d ∈ D, monomialVisibleFacets facets d).Finite := by
    exact hD.biUnion (fun d hd =>
      monomialVisibleFacets_finite_of_pointFinite facets hfacets hd.2)
  apply hU.subset
  intro F hF
  obtain ⟨hFfacets, d, hdP, hd0, hdF⟩ := hF
  simp only [Set.mem_iUnion]
  exact ⟨d, ⟨⟨hdP, hd0⟩, hFfacets, hdF⟩⟩

/-- The nonconstant packet of the coordinate variable `X v` is exactly the star of `v`. -/
theorem polynomialVisibleFacets_X
    {R α : Type*} [CommSemiring R] [Nontrivial R] [DecidableEq α]
    (facets : Set (Finset α)) (v : α) :
    polynomialVisibleFacets (R := R) facets (X v) =
      {F | F ∈ facets ∧ v ∈ F} := by
  ext F
  rw [polynomialVisibleFacets, MvPolynomial.support_X]
  simp

/-- **Finite-observation boundary.**  Complete nonconstant facet observation is finite for every
polynomial if and only if the facet family is point-finite. -/
theorem pointFiniteFacetFamily_iff_polynomialVisibleFacets_finite
    {R α : Type*} [CommSemiring R] [Nontrivial R] [DecidableEq α]
    (facets : Set (Finset α)) :
    PointFiniteFacetFamily facets ↔
      ∀ P : MvPolynomial α R, (polynomialVisibleFacets facets P).Finite := by
  constructor
  · intro h P
    exact polynomialVisibleFacets_finite_of_pointFinite facets h P
  · intro h v
    rw [← polynomialVisibleFacets_X (R := R) facets v]
    exact h (X v)

/-- Squarefree exponents indexed by the nonfaces of a possibly infinite facet family. -/
def setNonfaceExponents {α : Type*} [DecidableEq α]
    (facets : Set (Finset α)) : Set (α →₀ ℕ) :=
  {e | ∃ J : Finset α,
    ¬ IsFaceOf facets J ∧ e = indicatorExponent J}

/-- The Stanley--Reisner ideal of a possibly infinite facet family.  Every polynomial still has
finite monomial support, even though the generating nonface family need not be finite. -/
def setStanleyReisnerIdeal (R : Type*) [CommSemiring R]
    {α : Type*} [DecidableEq α] (facets : Set (Finset α)) :
    Ideal (MvPolynomial α R) :=
  Ideal.span ((fun e => monomial e (1 : R)) '' setNonfaceExponents facets)

/-- Coefficientwise membership in the nonface ideal remains exact for an infinite facet family. -/
theorem mem_setStanleyReisnerIdeal_iff
    {R α : Type*} [CommSemiring R] [DecidableEq α]
    (facets : Set (Finset α)) (P : MvPolynomial α R) :
    P ∈ setStanleyReisnerIdeal R facets ↔
      ∀ d ∈ P.support, ¬ IsFaceOf facets d.support := by
  rw [setStanleyReisnerIdeal, MvPolynomial.mem_ideal_span_monomial_image]
  constructor
  · intro h d hd hface
    obtain ⟨e, ⟨J, hJ, rfl⟩, hed⟩ := h d hd
    apply hJ
    apply isFaceOf_mono _ hface
    rw [← VeroneseIdeal.support_sum_single J]
    exact Finsupp.support_mono hed
  · intro h d hd
    refine ⟨indicatorExponent d.support, ⟨d.support, h d hd, rfl⟩, ?_⟩
    intro i
    rw [indicatorExponent, VeroneseIdeal.sum_single_apply]
    split_ifs with hi
    · exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    · exact Nat.zero_le _

/-- The infinite Stanley--Reisner ideal is exactly the intersection of all facet coordinate
ideals. -/
theorem setStanleyReisnerIdeal_eq_iInf_facetIdeal
    {R α : Type*} [CommSemiring R] [DecidableEq α]
    (facets : Set (Finset α)) :
    setStanleyReisnerIdeal R facets =
      ⨅ F : {F // F ∈ facets}, facetIdeal R F.1 := by
  ext P
  rw [mem_setStanleyReisnerIdeal_iff, Ideal.mem_iInf]
  simp only [mem_facetIdeal_iff]
  constructor
  · intro h F d hd hsub
    exact h d hd ⟨F.1, F.2, hsub⟩
  · intro h d hd hface
    obtain ⟨F, hF, hsub⟩ := hface
    exact h ⟨F, hF⟩ d hd hsub

/-- The canonical infinite-facet embedding of the Stanley--Reisner quotient into its complete
facet product. -/
def setStanleyReisnerFacetEmbedding
    {k R α : Type*} [CommRing k] [CommRing R] [DecidableEq α]
    [Algebra k (MvPolynomial α R)] (facets : Set (Finset α)) :
    MvPolynomial α R ⧸ setStanleyReisnerIdeal R facets →ₐ[k]
      ((F : {F // F ∈ facets}) → MvPolynomial α R ⧸ facetIdeal R F.1) :=
  quotientFacetEmbedding (k := k)
    (setStanleyReisnerIdeal R facets)
    (fun F : {F // F ∈ facets} => facetIdeal R F.1)
    (setStanleyReisnerIdeal_eq_iInf_facetIdeal facets)

/-- Complete facet restriction loses no quotient information, even for infinitely many facets. -/
theorem setStanleyReisnerFacetEmbedding_injective
    {k R α : Type*} [CommRing k] [CommRing R] [DecidableEq α]
    [Algebra k (MvPolynomial α R)] (facets : Set (Finset α)) :
    Function.Injective (setStanleyReisnerFacetEmbedding (k := k) (R := R) facets) :=
  quotientFacetEmbedding_injective (k := k)
    (setStanleyReisnerIdeal R facets)
    (fun F : {F // F ∈ facets} => facetIdeal R F.1)
    (setStanleyReisnerIdeal_eq_iInf_facetIdeal facets)

/-- Index type of the coherent restricted facet packet.  `none` is the one global constant mode;
`some (F,d)` is the copy of a nonconstant monomial exponent `d` on facet `F`. -/
abbrev PointFiniteFacetIndex {α : Type*} (facets : Set (Finset α)) :=
  Option ({F // F ∈ facets} × (α →₀ ℕ))

/-- Visible facets, now as a set in the facet subtype. -/
def visibleFacetSubtypes {α : Type*} (facets : Set (Finset α))
    (d : α →₀ ℕ) : Set {F // F ∈ facets} :=
  {F | d.support ⊆ F.1}

/-- A nonzero exponent has only finitely many visible facet subtypes under point-finiteness. -/
theorem visibleFacetSubtypes_finite_of_pointFinite
    {α : Type*} (facets : Set (Finset α))
    (hfacets : PointFiniteFacetFamily facets) {d : α →₀ ℕ} (hd : d ≠ 0) :
    (visibleFacetSubtypes facets d).Finite := by
  have hraw := monomialVisibleFacets_finite_of_pointFinite facets hfacets hd
  apply (hraw.preimage (Set.injOn_of_injective Subtype.val_injective)).subset
  intro F hF
  exact ⟨F.2, hF⟩

/-- The coherent packet of one monomial.  The constant exponent is represented once; a
nonconstant exponent is represented once on each facet where it is visible. -/
def pointFiniteFacetPacket
    {R α : Type*} [CommRing R]
    (facets : Set (Finset α)) (hfacets : PointFiniteFacetFamily facets)
    (d : α →₀ ℕ) : PointFiniteFacetIndex facets →₀ R := by
  classical
  by_cases hd : d = 0
  · exact Finsupp.single none 1
  · exact (visibleFacetSubtypes_finite_of_pointFinite facets hfacets hd).toFinset.sum
      (fun F => Finsupp.single (some (F, d)) 1)

/-- The coherent complete-facet row of a polynomial, obtained by linear extension of the monomial
packets. -/
def pointFiniteFacetRow
    {R α : Type*} [CommRing R]
    (facets : Set (Finset α)) (hfacets : PointFiniteFacetFamily facets) :
    MvPolynomial α R →ₗ[R] (PointFiniteFacetIndex facets →₀ R) :=
  Finsupp.linearCombination R (pointFiniteFacetPacket (R := R) facets hfacets)

/-- The constant monomial contributes one to the distinguished global coordinate. -/
theorem pointFiniteFacetPacket_zero_apply_none
    {R α : Type*} [CommRing R]
    (facets : Set (Finset α)) (hfacets : PointFiniteFacetFamily facets) :
    pointFiniteFacetPacket (R := R) facets hfacets 0 none = 1 := by
  classical
  simp [pointFiniteFacetPacket]

/-- A nonconstant monomial does not contribute to the distinguished global coordinate. -/
theorem pointFiniteFacetPacket_apply_none_of_ne_zero
    {R α : Type*} [CommRing R]
    (facets : Set (Finset α)) (hfacets : PointFiniteFacetFamily facets)
    {d : α →₀ ℕ} (hd : d ≠ 0) :
    pointFiniteFacetPacket (R := R) facets hfacets d none = 0 := by
  classical
  simp [pointFiniteFacetPacket, hd]

/-- A nonconstant monomial contributes one on each facet where it is visible. -/
theorem pointFiniteFacetPacket_apply_some_self_of_visible
    {R α : Type*} [CommRing R]
    (facets : Set (Finset α)) (hfacets : PointFiniteFacetFamily facets)
    (F : {F // F ∈ facets}) {d : α →₀ ℕ} (hd : d ≠ 0)
    (hvisible : d.support ⊆ F.1) :
    pointFiniteFacetPacket (R := R) facets hfacets d (some (F, d)) = 1 := by
  classical
  simp only [pointFiniteFacetPacket, dif_neg hd]
  change (Finsupp.lapply (R := R) (some (F, d))) _ = 1
  rw [map_sum]
  have hself :
      (Finsupp.lapply (R := R) (some (F, d)))
        (Finsupp.single (some (F, d)) (1 : R)) = 1 := by simp
  conv_rhs => rw [← hself]
  apply Finset.sum_eq_single F
  · intro G hG hGF
    simp [hGF]
  · intro hnot
    have hmem : F ∈
        (visibleFacetSubtypes_finite_of_pointFinite facets hfacets hd).toFinset :=
      ((visibleFacetSubtypes_finite_of_pointFinite facets hfacets hd).mem_toFinset).mpr hvisible
    exact (hnot hmem).elim

/-- A nonconstant monomial contributes zero on a facet where it is not visible. -/
theorem pointFiniteFacetPacket_apply_some_self_of_not_visible
    {R α : Type*} [CommRing R]
    (facets : Set (Finset α)) (hfacets : PointFiniteFacetFamily facets)
    (F : {F // F ∈ facets}) {d : α →₀ ℕ} (hd : d ≠ 0)
    (hvisible : ¬d.support ⊆ F.1) :
    pointFiniteFacetPacket (R := R) facets hfacets d (some (F, d)) = 0 := by
  classical
  simp only [pointFiniteFacetPacket, dif_neg hd]
  change (Finsupp.lapply (R := R) (some (F, d))) _ = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro G hG
  have hGvisible : d.support ⊆ G.1 := by
    simpa [visibleFacetSubtypes] using hG
  have hGF : G ≠ F := by
    intro h
    subst G
    exact hvisible hGvisible
  simp [hGF]

/-- A monomial packet vanishes on coordinates carrying a different exponent. -/
theorem pointFiniteFacetPacket_apply_some_of_exponent_ne
    {R α : Type*} [CommRing R]
    (facets : Set (Finset α)) (hfacets : PointFiniteFacetFamily facets)
    (F : {F // F ∈ facets}) {d e : α →₀ ℕ} (hed : e ≠ d) :
    pointFiniteFacetPacket (R := R) facets hfacets e (some (F, d)) = 0 := by
  classical
  by_cases he : e = 0
  · subst e
    simp [pointFiniteFacetPacket]
  · simp only [pointFiniteFacetPacket, dif_neg he]
    change (Finsupp.lapply (R := R) (some (F, d))) _ = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro G hG
    have hindex : some (G, e) ≠ some (F, d) := by
      intro h
      exact hed (congrArg Prod.snd (Option.some.inj h))
    simp [hindex]

/-- The distinguished coordinate of the coherent row is exactly the polynomial's constant
coefficient. -/
theorem pointFiniteFacetRow_apply_none
    {R α : Type*} [CommRing R]
    (facets : Set (Finset α)) (hfacets : PointFiniteFacetFamily facets)
    (P : MvPolynomial α R) :
    pointFiniteFacetRow facets hfacets P none = coeff 0 P := by
  classical
  rw [pointFiniteFacetRow]
  change (P.sum fun d c => c • pointFiniteFacetPacket (R := R) facets hfacets d) none =
    coeff 0 P
  rw [Finsupp.sum_apply]
  change (∑ d ∈ P.support,
    (coeff d P • pointFiniteFacetPacket (R := R) facets hfacets d) none) = coeff 0 P
  by_cases hzero : (0 : α →₀ ℕ) ∈ P.support
  · rw [Finset.sum_eq_single 0]
    · simp [pointFiniteFacetPacket_zero_apply_none]
    · intro d hdP hd0
      simp [pointFiniteFacetPacket_apply_none_of_ne_zero facets hfacets hd0]
    · simp [hzero]
  · have hcoeff : coeff 0 P = 0 := by
      by_contra hc
      exact hzero (Finsupp.mem_support_iff.mpr hc)
    rw [hcoeff]
    apply Finset.sum_eq_zero
    intro d hdP
    have hd0 : d ≠ 0 := by
      intro hd
      subst d
      exact hzero hdP
    simp [pointFiniteFacetPacket_apply_none_of_ne_zero facets hfacets hd0]

/-- On a visible facet, the coherent row recovers the original nonconstant monomial
coefficient. -/
theorem pointFiniteFacetRow_apply_some_of_visible
    {R α : Type*} [CommRing R]
    (facets : Set (Finset α)) (hfacets : PointFiniteFacetFamily facets)
    (P : MvPolynomial α R) (F : {F // F ∈ facets})
    {d : α →₀ ℕ} (hd : d ≠ 0) (hvisible : d.support ⊆ F.1) :
    pointFiniteFacetRow facets hfacets P (some (F, d)) = coeff d P := by
  classical
  rw [pointFiniteFacetRow]
  change (P.sum fun e c => c • pointFiniteFacetPacket (R := R) facets hfacets e)
      (some (F, d)) = coeff d P
  rw [Finsupp.sum_apply]
  change (∑ e ∈ P.support,
    (coeff e P • pointFiniteFacetPacket (R := R) facets hfacets e) (some (F, d))) =
      coeff d P
  by_cases hsupport : d ∈ P.support
  · rw [Finset.sum_eq_single d]
    · simp [pointFiniteFacetPacket_apply_some_self_of_visible facets hfacets F hd hvisible]
    · intro e heP hed
      simp [pointFiniteFacetPacket_apply_some_of_exponent_ne facets hfacets F hed]
    · simp [hsupport]
  · have hcoeff : coeff d P = 0 := by
      by_contra hc
      exact hsupport (Finsupp.mem_support_iff.mpr hc)
    rw [hcoeff]
    apply Finset.sum_eq_zero
    intro e heP
    have hed : e ≠ d := by
      intro h
      subst e
      exact hsupport heP
    simp [pointFiniteFacetPacket_apply_some_of_exponent_ne facets hfacets F hed]

/-- On a facet where a nonconstant exponent is invisible, the coherent row coordinate is zero. -/
theorem pointFiniteFacetRow_apply_some_of_not_visible
    {R α : Type*} [CommRing R]
    (facets : Set (Finset α)) (hfacets : PointFiniteFacetFamily facets)
    (P : MvPolynomial α R) (F : {F // F ∈ facets})
    {d : α →₀ ℕ} (hd : d ≠ 0) (hvisible : ¬d.support ⊆ F.1) :
    pointFiniteFacetRow facets hfacets P (some (F, d)) = 0 := by
  classical
  rw [pointFiniteFacetRow]
  change (P.sum fun e c => c • pointFiniteFacetPacket (R := R) facets hfacets e)
      (some (F, d)) = 0
  rw [Finsupp.sum_apply]
  change (∑ e ∈ P.support,
    (coeff e P • pointFiniteFacetPacket (R := R) facets hfacets e) (some (F, d))) = 0
  apply Finset.sum_eq_zero
  intro e heP
  by_cases hed : e = d
  · subst e
    simp [pointFiniteFacetPacket_apply_some_self_of_not_visible facets hfacets F hd hvisible]
  · simp [pointFiniteFacetPacket_apply_some_of_exponent_ne facets hfacets F hed]

/-- The coherent row has no facet-local copy of the constant exponent. -/
theorem pointFiniteFacetRow_apply_some_zero
    {R α : Type*} [CommRing R]
    (facets : Set (Finset α)) (hfacets : PointFiniteFacetFamily facets)
    (P : MvPolynomial α R) (F : {F // F ∈ facets}) :
    pointFiniteFacetRow facets hfacets P (some (F, 0)) = 0 := by
  classical
  rw [pointFiniteFacetRow]
  change (P.sum fun e c => c • pointFiniteFacetPacket (R := R) facets hfacets e)
      (some (F, 0)) = 0
  rw [Finsupp.sum_apply]
  change (∑ e ∈ P.support,
    (coeff e P • pointFiniteFacetPacket (R := R) facets hfacets e) (some (F, 0))) = 0
  apply Finset.sum_eq_zero
  intro e heP
  by_cases he0 : e = 0
  · subst e
    simp [pointFiniteFacetPacket]
  · simp [pointFiniteFacetPacket_apply_some_of_exponent_ne facets hfacets F he0]

/-- **Exact coherent-packet kernel.**  For a nonempty point-finite facet family, the only
polynomials erased by the finite-support complete-facet row are precisely the Stanley--Reisner
nonface polynomials. -/
theorem pointFiniteFacetRow_eq_zero_iff
    {R α : Type*} [CommRing R] [DecidableEq α]
    (facets : Set (Finset α)) (hne : facets.Nonempty)
    (hfacets : PointFiniteFacetFamily facets) (P : MvPolynomial α R) :
    pointFiniteFacetRow facets hfacets P = 0 ↔
      P ∈ setStanleyReisnerIdeal R facets := by
  constructor
  · intro hrow
    rw [mem_setStanleyReisnerIdeal_iff]
    intro d hdP hface
    have hcoeff : coeff d P ≠ 0 := Finsupp.mem_support_iff.mp hdP
    by_cases hd : d = 0
    · subst d
      have hnone := congrArg (fun q => q none) hrow
      change pointFiniteFacetRow facets hfacets P none = 0 at hnone
      rw [pointFiniteFacetRow_apply_none] at hnone
      exact hcoeff hnone
    · obtain ⟨F, hF, hvisible⟩ := hface
      have hsome := congrArg
        (fun q => q (some (⟨F, hF⟩, d) : PointFiniteFacetIndex facets)) hrow
      change pointFiniteFacetRow facets hfacets P (some (⟨F, hF⟩, d)) = 0 at hsome
      rw [pointFiniteFacetRow_apply_some_of_visible facets hfacets P ⟨F, hF⟩ hd hvisible]
        at hsome
      exact hcoeff hsome
  · intro hP
    apply Finsupp.ext
    intro q
    cases q with
    | none =>
        rw [pointFiniteFacetRow_apply_none]
        by_contra hcoeff
        have hzeroSupport : (0 : α →₀ ℕ) ∈ P.support :=
          Finsupp.mem_support_iff.mpr hcoeff
        have hnonface := (mem_setStanleyReisnerIdeal_iff facets P).mp hP 0 hzeroSupport
        obtain ⟨F, hF⟩ := hne
        exact hnonface ⟨F, hF, by simp⟩
    | some q =>
        obtain ⟨F, d⟩ := q
        by_cases hd : d = 0
        · subst d
          exact pointFiniteFacetRow_apply_some_zero facets hfacets P F
        · by_cases hvisible : d.support ⊆ F.1
          · rw [pointFiniteFacetRow_apply_some_of_visible facets hfacets P F hd hvisible]
            by_contra hcoeff
            have hdSupport : d ∈ P.support := Finsupp.mem_support_iff.mpr hcoeff
            have hnonface := (mem_setStanleyReisnerIdeal_iff facets P).mp hP d hdSupport
            exact hnonface ⟨F.1, F.2, hvisible⟩
          · exact pointFiniteFacetRow_apply_some_of_not_visible
              facets hfacets P F hd hvisible

/-- The coherent restricted facet row represents exactly the linear matroid of the infinite
Stanley--Reisner quotient. -/
theorem linearIndependent_pointFiniteFacetRow_iff
    {R α ι : Type*} [CommRing R] [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (facets : Set (Finset α)) (hne : facets.Nonempty)
    (hfacets : PointFiniteFacetFamily facets) (P : ι → MvPolynomial α R) :
    LinearIndependent R (pointFiniteFacetRow facets hfacets ∘ P) ↔
      LinearIndependent R
        (fun i => Ideal.Quotient.mk (setStanleyReisnerIdeal R facets) (P i)) := by
  classical
  rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
  constructor
  · intro hrow A hquot i
    apply hrow A
    let S : MvPolynomial α R := ∑ j, A j • P j
    have hmem : S ∈ setStanleyReisnerIdeal R facets := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      simpa [S, map_sum, map_smul] using hquot
    have hzero := (pointFiniteFacetRow_eq_zero_iff facets hne hfacets S).mpr hmem
    simpa [S, map_sum, map_smul, Function.comp_apply] using hzero
  · intro hquot A hrow i
    apply hquot A
    let S : MvPolynomial α R := ∑ j, A j • P j
    have hzero : pointFiniteFacetRow facets hfacets S = 0 := by
      simpa [S, map_sum, map_smul, Function.comp_apply] using hrow
    have hmem := (pointFiniteFacetRow_eq_zero_iff facets hne hfacets S).mp hzero
    simpa [S, map_sum, map_smul] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)

end

end GaloisForLFunctions.HTGeometry
