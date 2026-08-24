import GaloisForLFunctions.HTGeometry.ABHN.FinsuppReciprocitySupportCardinality
import GaloisForLFunctions.HTGeometry.PairGroupoidBidescentLaw

/-!
# Hasse support for additive cocycle triangles

Every additive pair-groupoid cocycle gives a three-place reciprocity packet: two consecutive local
defects and the negative composite defect have zero sum.  Consequently an active triangle edge can
never be the unique active edge.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.HTGeometry.ABHN

universe u v

/-- Three-place reciprocity profile attached to an additive cocycle triangle. -/
noncomputable def additiveCocycleTriangleProfile
    {X : Type u} {A : Type v} [AddCommGroup A]
    (d : X → X → A) (x y z : X) : Fin 3 →₀ A :=
  Finsupp.equivFunOnFinite.symm ![d x y, d y z, -d x z]

@[simp]
theorem additiveCocycleTriangleProfile_zero
    {X : Type u} {A : Type v} [AddCommGroup A]
    (d : X → X → A) (x y z : X) :
    additiveCocycleTriangleProfile d x y z 0 = d x y := rfl

@[simp]
theorem additiveCocycleTriangleProfile_one
    {X : Type u} {A : Type v} [AddCommGroup A]
    (d : X → X → A) (x y z : X) :
    additiveCocycleTriangleProfile d x y z 1 = d y z := rfl

@[simp]
theorem additiveCocycleTriangleProfile_two
    {X : Type u} {A : Type v} [AddCommGroup A]
    (d : X → X → A) (x y z : X) :
    additiveCocycleTriangleProfile d x y z 2 = -d x z := rfl

/-- An additive cocycle triangle obeys the three-place reciprocity sum. -/
theorem additiveCocycleTriangleProfile_sum_eq_zero
    {X : Type u} {A : Type v} [AddCommGroup A]
    (d : X → X → A) (x y z : X)
    (hcocycle : d x z = d x y + d y z) :
    (additiveCocycleTriangleProfile d x y z).sum (fun _ a => a) = 0 := by
  rw [Finsupp.sum_fintype _ _ (by intro; rfl)]
  change ∑ i : Fin 3, (![d x y, d y z, -d x z] : Fin 3 → A) i = 0
  simp [Fin.sum_univ_succ, hcocycle]

/-- Every active coordinate of an additive cocycle triangle has another active coordinate. -/
theorem additiveCocycleTriangleProfile_exists_other_nonzero
    {X : Type u} {A : Type v} [AddCommGroup A]
    (d : X → X → A) (x y z : X)
    (hcocycle : d x z = d x y + d y z) {i : Fin 3}
    (hi : additiveCocycleTriangleProfile d x y z i ≠ 0) :
    ∃ j : Fin 3, j ≠ i ∧ additiveCocycleTriangleProfile d x y z j ≠ 0 :=
  finsupp_exists_other_nonzero_place_of_sum_eq_zero
    (additiveCocycleTriangleProfile d x y z)
    (additiveCocycleTriangleProfile_sum_eq_zero d x y z hcocycle) hi

/-- A nonzero additive cocycle triangle occupies at least two edges. -/
theorem additiveCocycleTriangleProfile_two_le_support_card
    {X : Type u} {A : Type v} [AddCommGroup A]
    (d : X → X → A) (x y z : X)
    (hcocycle : d x z = d x y + d y z)
    (hne : additiveCocycleTriangleProfile d x y z ≠ 0) :
    2 ≤ (additiveCocycleTriangleProfile d x y z).support.card :=
  finsupp_two_le_support_card_of_sum_eq_zero
    (additiveCocycleTriangleProfile d x y z)
    (additiveCocycleTriangleProfile_sum_eq_zero d x y z hcocycle) hne

/-- Universal pair-descent triangle as a finite reciprocity profile. -/
noncomputable def pairDescentTriangleProfile
    {X : Type u} (f : X → ℂ) (x y z : X) : Fin 3 →₀ ℂ :=
  additiveCocycleTriangleProfile (pairDescentDefect f) x y z

@[simp]
theorem pairDescentTriangleProfile_zero
    {X : Type u} (f : X → ℂ) (x y z : X) :
    pairDescentTriangleProfile f x y z 0 = pairDescentDefect f x y := rfl

@[simp]
theorem pairDescentTriangleProfile_one
    {X : Type u} (f : X → ℂ) (x y z : X) :
    pairDescentTriangleProfile f x y z 1 = pairDescentDefect f y z := rfl

@[simp]
theorem pairDescentTriangleProfile_two
    {X : Type u} (f : X → ℂ) (x y z : X) :
    pairDescentTriangleProfile f x y z 2 = -pairDescentDefect f x z := rfl

/-- Universal pair-descent defects obey the three-edge reciprocity sum. -/
theorem pairDescentTriangleProfile_sum_eq_zero
    {X : Type u} (f : X → ℂ) (x y z : X) :
    (pairDescentTriangleProfile f x y z).sum (fun _ a => a) = 0 :=
  additiveCocycleTriangleProfile_sum_eq_zero (pairDescentDefect f) x y z
    (pairDescentDefect_cocycle f x y z)

/-- A nonzero pair-descent defect on one triangle edge forces another nonzero edge defect. -/
theorem pairDescentTriangleProfile_exists_other_nonzero
    {X : Type u} (f : X → ℂ) (x y z : X) {i : Fin 3}
    (hi : pairDescentTriangleProfile f x y z i ≠ 0) :
    ∃ j : Fin 3, j ≠ i ∧ pairDescentTriangleProfile f x y z j ≠ 0 :=
  additiveCocycleTriangleProfile_exists_other_nonzero (pairDescentDefect f) x y z
    (pairDescentDefect_cocycle f x y z) hi

/-- A nonzero universal descent triangle has support on at least two edges. -/
theorem pairDescentTriangleProfile_two_le_support_card
    {X : Type u} (f : X → ℂ) (x y z : X)
    (hne : pairDescentTriangleProfile f x y z ≠ 0) :
    2 ≤ (pairDescentTriangleProfile f x y z).support.card :=
  additiveCocycleTriangleProfile_two_le_support_card (pairDescentDefect f) x y z
    (pairDescentDefect_cocycle f x y z) hne

end GaloisForLFunctions.HTGeometry
