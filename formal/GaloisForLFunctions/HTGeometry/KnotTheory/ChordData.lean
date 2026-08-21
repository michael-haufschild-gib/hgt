import Mathlib

/-!
# Chord diagrams and singular-knot data

A chord diagram is represented exactly as a fixed-point-free involution on an ordered finite set
of endpoints.  Singular-knot data retains this pairing and a local sign for every double point.
The four-term quotient and Kontsevich integration are deliberately separate future layers.
-/

namespace GaloisForLFunctions.HTGeometry.KnotTheory

/-- An unoriented chord diagram with `n` double points, represented by its fixed-point-free
involution on `2n` ordered endpoints. -/
structure ChordDiagram (n : ℕ) where
  mate : Fin (2 * n) → Fin (2 * n)
  mate_involutive : ∀ x, mate (mate x) = x
  mate_fixedPointFree : ∀ x, mate x ≠ x

/-- The relation that two endpoints form one chord. -/
def ChordDiagram.IsMate (D : ChordDiagram n) (x y : Fin (2 * n)) : Prop := D.mate x = y

theorem ChordDiagram.isMate_symmetric (D : ChordDiagram n) (x y : Fin (2 * n)) :
    D.IsMate x y ↔ D.IsMate y x := by
  constructor
  · intro h
    change D.mate y = x
    rw [← h, D.mate_involutive]
  · intro h
    change D.mate x = y
    rw [← h, D.mate_involutive]

/-- Change of endpoint parametrization transports a chord diagram. -/
def ChordDiagram.relabel (D : ChordDiagram n) (e : Equiv.Perm (Fin (2 * n))) : ChordDiagram n where
  mate x := e (D.mate (e.symm x))
  mate_involutive := by
    intro x
    rw [e.symm_apply_apply, D.mate_involutive, e.apply_symm_apply]
  mate_fixedPointFree := by
    intro x h
    apply D.mate_fixedPointFree (e.symm x)
    apply e.injective
    simpa using h

theorem ChordDiagram.isMate_relabel_iff (D : ChordDiagram n) (e : Equiv.Perm (Fin (2 * n)))
    (x y : Fin (2 * n)) :
    (D.relabel e).IsMate x y ↔ D.IsMate (e.symm x) (e.symm y) := by
  change e (D.mate (e.symm x)) = y ↔ D.mate (e.symm x) = e.symm y
  constructor
  · intro h
    exact (e.apply_eq_iff_eq_symm_apply).mp h
  · intro h
    exact (e.apply_eq_iff_eq_symm_apply).mpr h

theorem ChordDiagram.relabel_refl (D : ChordDiagram n) :
    D.relabel (Equiv.refl _) = D := by
  cases D
  rfl

theorem ChordDiagram.relabel_trans (D : ChordDiagram n) (e f : Equiv.Perm (Fin (2 * n))) :
    D.relabel (e.trans f) = (D.relabel e).relabel f := by
  cases D
  rfl

/-- Raw singular-knot datum: chord pairing plus a sign at each double point. -/
structure SingularKnotData (n : ℕ) where
  chords : ChordDiagram n
  localSigns : Fin n → Bool

def SingularKnotData.underlyingChordDiagram (K : SingularKnotData n) : ChordDiagram n := K.chords
def SingularKnotData.singularOrder (_K : SingularKnotData n) : ℕ := n

theorem SingularKnotData.singularOrder_eq (K : SingularKnotData n) : K.singularOrder = n := rfl

/-- A raw degree-`n` weight system is a value assigned to every `n`-chord diagram. -/
abbrev RawWeightSystem (R : Type*) (n : ℕ) := ChordDiagram n → R

/-- A choice of over/under resolution at each of `n` singular crossings. -/
abbrev LocalResolution (n : ℕ) := Fin n → Bool

/-- Retain the chord diagram while replacing its local crossing resolutions. -/
def SingularKnotData.withLocalResolutions (K : SingularKnotData n)
    (resolutions : LocalResolution n) : SingularKnotData n where
  chords := K.chords
  localSigns := resolutions

theorem SingularKnotData.withLocalResolutions_chords (K : SingularKnotData n)
    (resolutions : LocalResolution n) :
    (K.withLocalResolutions resolutions).underlyingChordDiagram = K.underlyingChordDiagram := rfl

/-- The four choices at a pair of singular crossings, ordered by their endpoint index. -/
def twoCrossingResolution (first second : Bool) : LocalResolution 2 := fun i =>
  if i.val = 0 then first else second

/-- Alternating two-singularity extension of an integer-valued resolved-knot observable.

This is the local Vassiliev finite difference; it deliberately does not assert that the observable
already descends through an ambient-isotopy quotient. -/
def twoSingularAlternatingExtension (F : LocalResolution 2 → ℤ) : ℤ :=
  F (twoCrossingResolution true true)
    - F (twoCrossingResolution false true)
    - F (twoCrossingResolution true false)
    + F (twoCrossingResolution false false)

/-- The order-at-most-one condition at a fixed two-singularity local model. -/
def IsTwoSingularVassilievOrderAtMostOne (F : LocalResolution 2 → ℤ) : Prop :=
  twoSingularAlternatingExtension F = 0

/-- A crossing-count observable is linear in the two local resolutions. -/
def twoCrossingCount (resolutions : LocalResolution 2) : ℤ :=
  (if resolutions 0 then 1 else 0) + (if resolutions 1 then 1 else 0)

/-- Linear local crossing data has vanishing second Vassiliev difference. -/
theorem twoCrossingCount_vassiliev_order_one :
    IsTwoSingularVassilievOrderAtMostOne twoCrossingCount := by
  simp [IsTwoSingularVassilievOrderAtMostOne, twoSingularAlternatingExtension,
    twoCrossingCount, twoCrossingResolution]

end GaloisForLFunctions.HTGeometry.KnotTheory
