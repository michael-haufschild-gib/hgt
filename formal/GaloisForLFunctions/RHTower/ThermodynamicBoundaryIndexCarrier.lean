import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Nonliftable quotient symbols and their boundary index

A singular infinite-volume completion of a finite-prime thermodynamic model is described by a
unital extension `0 → J → E → Q → 0`.  The associated index datum is the segment

`K₁(E) --lift--> K₁(Q) --boundary--> K₀(J)`

of the six-term exact sequence: `lift` sends an invertible bulk symbol to its quotient symbol and
`boundary` sends a quotient symbol to the obstruction against inverting it inside the bulk.

This module isolates the exact algebra of that segment.  Everything below is proved from one
hypothesis — exactness at the middle term, `boundary.ker = lift.range` — and nothing else.

The results are:

* `boundary_ne_zero_iff_not_mem_liftRange`: a quotient symbol has nonzero boundary index exactly
  when it has no bulk lift.  The integer is therefore not assigned separately; it *is* the lifting
  obstruction.
* `lift_surjective_iff_boundary_trivial`: the completion is regular — every quotient symbol lifts —
  exactly when no symbol carries a boundary index at all.  A charge in a regular completion must
  therefore already be present in the bulk.
* `quotientLiftRangeEquivBoundaryRange`: the boundary index is a *complete* invariant of the
  nonliftable class, since it induces an isomorphism `Q ⧸ lift.range ≃+ boundary.range`.
* `multiplicity_ne_zero_iff_not_mem_liftRange`: if the boundary class of a contour symbol is an
  integer multiple of a fixed generator of infinite order, that integer is nonzero exactly when the
  symbol does not lift, and it is uniquely determined.
* `HasIndex.add`: boundary multiplicities of composed symbols add, so nested contour symbols carry
  additive charges.
-/

noncomputable section

namespace ThermodynamicBoundaryIndex

variable {E Q J : Type*} [AddCommGroup E] [AddCommGroup Q] [AddCommGroup J]

/-- The exact segment `E → Q → J` of a six-term index sequence: a lifting map from bulk symbols to
quotient symbols, a boundary map from quotient symbols to the ideal, and exactness at the middle
term. -/
structure ExactSegment (E Q J : Type*) [AddCommGroup E] [AddCommGroup Q] [AddCommGroup J] where
  /-- Bulk symbols map to quotient symbols. -/
  lift : E →+ Q
  /-- A quotient symbol maps to its lifting obstruction in the ideal. -/
  boundary : Q →+ J
  /-- Exactness at the quotient term. -/
  exact : boundary.ker = lift.range

namespace ExactSegment

variable (S : ExactSegment E Q J)

/-- A lifted symbol has zero boundary index. -/
theorem boundary_lift (v : E) : S.boundary (S.lift v) = 0 := by
  have h : S.lift v ∈ S.boundary.ker := by
    rw [S.exact]
    exact ⟨v, rfl⟩
  simpa using h

/-- **Boundary index vanishes exactly on liftable symbols.** -/
theorem boundary_eq_zero_iff_mem_liftRange (u : Q) :
    S.boundary u = 0 ↔ u ∈ S.lift.range := by
  constructor
  · intro h
    have h' : u ∈ S.boundary.ker := by simpa using h
    rwa [S.exact] at h'
  · rintro ⟨v, rfl⟩
    exact S.boundary_lift v

/-- **The boundary index is exactly the lifting obstruction.**  A quotient symbol has nonzero
boundary class precisely when it admits no invertible bulk lift. -/
theorem boundary_ne_zero_iff_not_mem_liftRange (u : Q) :
    S.boundary u ≠ 0 ↔ u ∉ S.lift.range := by
  simp [S.boundary_eq_zero_iff_mem_liftRange u]

/-- A nonzero boundary index witnesses nonliftability. -/
theorem not_mem_liftRange_of_boundary_ne_zero {u : Q} (h : S.boundary u ≠ 0) :
    u ∉ S.lift.range :=
  (S.boundary_ne_zero_iff_not_mem_liftRange u).1 h

/-- **Regular completion dichotomy.**  Every quotient symbol lifts exactly when no quotient symbol
carries a boundary index.  Hence a nonzero charge in a completion whose symbols all lift cannot be
created by the completion; it must already be carried in the bulk. -/
theorem lift_surjective_iff_boundary_trivial :
    Function.Surjective S.lift ↔ ∀ u : Q, S.boundary u = 0 := by
  constructor
  · intro hsurj u
    obtain ⟨v, rfl⟩ := hsurj u
    exact S.boundary_lift v
  · intro hzero u
    exact (S.boundary_eq_zero_iff_mem_liftRange u).1 (hzero u)

/-- If some symbol carries a nonzero boundary index, the extension is not split at the level of
symbols: the lifting map fails to be surjective. -/
theorem not_surjective_lift_of_boundary_ne_zero {u : Q} (h : S.boundary u ≠ 0) :
    ¬ Function.Surjective S.lift := by
  intro hsurj
  exact h ((S.lift_surjective_iff_boundary_trivial).1 hsurj u)

/-- **The boundary index is a complete invariant of the nonliftable class.**  The boundary map
induces an isomorphism from the group of quotient symbols modulo liftable symbols onto the group of
realized boundary indices. -/
def quotientLiftRangeEquivBoundaryRange :
    (Q ⧸ S.lift.range) ≃+ S.boundary.range :=
  (QuotientAddGroup.quotientAddEquivOfEq S.exact.symm).trans
    (QuotientAddGroup.quotientKerEquivRange S.boundary)

/-- Two quotient symbols have the same boundary index exactly when they differ by a liftable
symbol. -/
theorem boundary_eq_iff_sub_mem_liftRange (u u' : Q) :
    S.boundary u = S.boundary u' ↔ u - u' ∈ S.lift.range := by
  rw [← S.boundary_eq_zero_iff_mem_liftRange, map_sub, sub_eq_zero]

end ExactSegment

/-- A distinguished ideal generator has infinite order. -/
def InfiniteOrder (e : J) : Prop := ∀ n : ℤ, n • e = 0 → n = 0

/-- The exact index datum of a contour symbol: its boundary class is the prescribed integer
multiple of a distinguished positive generator. -/
def HasIndex (S : ExactSegment E Q J) (e : J) (u : Q) (m : ℤ) : Prop :=
  S.boundary u = m • e

variable {S : ExactSegment E Q J}

/-- **Index identity forces the lifting obstruction.**  If a contour symbol has boundary class
`m • e` for a generator of infinite order, then `m ≠ 0` exactly when the symbol does not lift. -/
theorem multiplicity_ne_zero_iff_not_mem_liftRange
    {e : J} (he : InfiniteOrder e) {u : Q} {m : ℤ} (h : HasIndex S e u m) :
    m ≠ 0 ↔ u ∉ S.lift.range := by
  rw [← S.boundary_ne_zero_iff_not_mem_liftRange, h]
  constructor
  · intro hm hcontra
    exact hm (he m hcontra)
  · intro hne hm
    exact hne (by simp [hm])

/-- The index of a symbol is uniquely determined by its boundary class. -/
theorem index_unique {e : J} (he : InfiniteOrder e) {u : Q} {m m' : ℤ}
    (h : HasIndex S e u m) (h' : HasIndex S e u m') : m = m' := by
  have hzero : (m - m') • e = 0 := by
    rw [sub_zsmul, ← h, ← h']; simp
  have := he _ hzero
  omega

/-- **Contour additivity.**  Composing quotient symbols adds their boundary indices. -/
theorem HasIndex.add {e : J} {u u' : Q} {m m' : ℤ}
    (h : HasIndex S e u m) (h' : HasIndex S e u' m') :
    HasIndex S e (u + u') (m + m') := by
  unfold HasIndex at *
  rw [map_add, h, h', add_zsmul]

/-- A liftable symbol has index zero. -/
theorem HasIndex.eq_zero_of_mem_liftRange {e : J} (he : InfiniteOrder e) {u : Q} {m : ℤ}
    (h : HasIndex S e u m) (hu : u ∈ S.lift.range) : m = 0 := by
  by_contra hm
  exact (multiplicity_ne_zero_iff_not_mem_liftRange he h).1 hm hu

/-- The image of the bulk unit has index zero. -/
theorem hasIndex_zero {e : J} : HasIndex S e 0 0 := by
  simp [HasIndex]

end ThermodynamicBoundaryIndex
