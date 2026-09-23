import GaloisForLFunctions.HTGeometry.DirectionalKaehlerWedge
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic

/-!
# Event-coframe Plebanski simplicity

A complex four-coframe has three canonical degree-two exterior forms

`Σ₁(τ) = τ e⁰e¹ + e²e³`,
`Σ₂(τ) = τ e⁰e² - e¹e³`,
`Σ₃(τ) = τ e⁰e³ + e¹e²`.

This file proves their exact simplicity matrix

`Σᵢ(τ) Σⱼ(τ) = 2 τ δᵢⱼ vol`.

Thus `τ = 1` gives the Euclidean quaternionic triple, `τ = I` gives its standard complex chiral
continuation, and `τ = 0` is the degenerate endpoint.  For `τ ≠ 0`, the three forms are linearly
independent.  These are unconditional exterior-algebra identities.

No Lorentzian reality condition, physical real-form selection, tetrad, connection, action,
Einstein equation, exceptional event interpretation, or gravitational claim is assumed here.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Complex coordinate one-forms on a four-direction carrier. -/
abbrev EventCoframe4 := Fin 4 → ℂ

/-- Full exterior algebra of the complex event coframe. -/
abbrev EventCoframeExterior := ExteriorAlgebra ℂ EventCoframe4

/-- The `i`th coordinate one-form, embedded in the exterior algebra. -/
def eventCoframeOne (i : Fin 4) : EventCoframeExterior :=
  ExteriorAlgebra.ι ℂ (Pi.basisFun ℂ (Fin 4) i)

/-- Oriented coordinate four-volume. -/
def eventPlebanskiVolume : EventCoframeExterior :=
  eventCoframeOne 0 *
    (eventCoframeOne 1 * (eventCoframeOne 2 * eventCoframeOne 3))

/-- First member of the event-coframe simplicity triple. -/
def eventSigmaOne (τ : ℂ) : EventCoframeExterior :=
  τ • (eventCoframeOne 0 * eventCoframeOne 1) +
    eventCoframeOne 2 * eventCoframeOne 3

/-- Second member of the event-coframe simplicity triple. -/
def eventSigmaTwo (τ : ℂ) : EventCoframeExterior :=
  τ • (eventCoframeOne 0 * eventCoframeOne 2) -
    eventCoframeOne 1 * eventCoframeOne 3

/-- Third member of the event-coframe simplicity triple. -/
def eventSigmaThree (τ : ℂ) : EventCoframeExterior :=
  τ • (eventCoframeOne 0 * eventCoframeOne 3) +
    eventCoframeOne 1 * eventCoframeOne 2

private lemma eventCoframeOne_sq (i : Fin 4) :
    eventCoframeOne i * eventCoframeOne i = 0 := by
  exact ExteriorAlgebra.ι_sq_zero _

private lemma eventCoframeOne_swap (i j : Fin 4) :
    eventCoframeOne i * eventCoframeOne j =
      -(eventCoframeOne j * eventCoframeOne i) := by
  have h := ExteriorAlgebra.ι_add_mul_swap (R := ℂ)
    (Pi.basisFun ℂ (Fin 4) i) (Pi.basisFun ℂ (Fin 4) j)
  change
    eventCoframeOne i * eventCoframeOne j +
      eventCoframeOne j * eventCoframeOne i = 0 at h
  exact eq_neg_of_add_eq_zero_left h

private lemma eventCoframeOne_move
    (i j : Fin 4) (x : EventCoframeExterior) :
    eventCoframeOne i * (eventCoframeOne j * x) =
      -(eventCoframeOne j * (eventCoframeOne i * x)) := by
  rw [← mul_assoc, eventCoframeOne_swap, neg_mul, mul_assoc]

private lemma eventCoframeOne_repeat
    (i : Fin 4) (x : EventCoframeExterior) :
    eventCoframeOne i * (eventCoframeOne i * x) = 0 := by
  rw [← mul_assoc, eventCoframeOne_sq, zero_mul]

private lemma eventCoframeOne_dup13
    (i j : Fin 4) (x : EventCoframeExterior) :
    eventCoframeOne i *
        (eventCoframeOne j * (eventCoframeOne i * x)) = 0 := by
  rw [eventCoframeOne_move j i, mul_neg, eventCoframeOne_repeat, neg_zero]

private lemma eventCoframeOne_dup14 (i j k : Fin 4) :
    eventCoframeOne i *
        (eventCoframeOne j * (eventCoframeOne k * eventCoframeOne i)) = 0 := by
  rw [eventCoframeOne_swap k i, mul_neg, eventCoframeOne_move j i, neg_neg,
    eventCoframeOne_repeat]

private lemma eventCoframeOne_dup23
    (i j : Fin 4) (x : EventCoframeExterior) :
    eventCoframeOne i *
        (eventCoframeOne j * (eventCoframeOne j * x)) = 0 := by
  rw [eventCoframeOne_repeat, mul_zero]

private lemma eventCoframeOne_dup24 (i j k : Fin 4) :
    eventCoframeOne i *
        (eventCoframeOne j * (eventCoframeOne k * eventCoframeOne j)) = 0 := by
  rw [eventCoframeOne_swap k j, mul_neg, eventCoframeOne_repeat, neg_zero, mul_zero]

private lemma eventPair_mul_pair_same_first (i j k : Fin 4) :
    (eventCoframeOne i * eventCoframeOne j) *
        (eventCoframeOne i * eventCoframeOne k) = 0 := by
  rw [mul_assoc, eventCoframeOne_dup13]

private lemma eventPair_mul_pair_outer (i j k : Fin 4) :
    (eventCoframeOne i * eventCoframeOne j) *
        (eventCoframeOne k * eventCoframeOne i) = 0 := by
  rw [mul_assoc, eventCoframeOne_dup14]

private lemma eventPair_mul_pair_middle (i j k : Fin 4) :
    (eventCoframeOne i * eventCoframeOne j) *
        (eventCoframeOne j * eventCoframeOne k) = 0 := by
  rw [mul_assoc, eventCoframeOne_dup23]

private lemma eventPair_mul_pair_same_second (i j k : Fin 4) :
    (eventCoframeOne i * eventCoframeOne j) *
        (eventCoframeOne k * eventCoframeOne j) = 0 := by
  rw [mul_assoc, eventCoframeOne_dup24]

private lemma event_two_three_zero_one :
    eventCoframeOne 2 *
        (eventCoframeOne 3 * (eventCoframeOne 0 * eventCoframeOne 1)) =
      eventPlebanskiVolume := by
  rw [eventCoframeOne_move 3 0, mul_neg, eventCoframeOne_move 2 0, neg_neg,
    eventCoframeOne_swap 3 1, mul_neg, eventCoframeOne_move 2 1, neg_neg]
  rfl

private lemma eventPair01_sq :
    (eventCoframeOne 0 * eventCoframeOne 1) *
        (eventCoframeOne 0 * eventCoframeOne 1) = 0 := by
  rw [mul_assoc, eventCoframeOne_move 1 0, mul_neg, eventCoframeOne_repeat, neg_zero]

private lemma eventPair23_sq :
    (eventCoframeOne 2 * eventCoframeOne 3) *
        (eventCoframeOne 2 * eventCoframeOne 3) = 0 := by
  rw [mul_assoc, eventCoframeOne_move 3 2, mul_neg, eventCoframeOne_repeat, neg_zero]

private lemma eventPair01_pair23 :
    (eventCoframeOne 0 * eventCoframeOne 1) *
        (eventCoframeOne 2 * eventCoframeOne 3) =
      eventPlebanskiVolume := by
  simp [eventPlebanskiVolume, mul_assoc]

private lemma eventPair23_pair01 :
    (eventCoframeOne 2 * eventCoframeOne 3) *
        (eventCoframeOne 0 * eventCoframeOne 1) =
      eventPlebanskiVolume := by
  simpa only [mul_assoc] using event_two_three_zero_one

private lemma event_zero_two_one_three :
    eventCoframeOne 0 *
        (eventCoframeOne 2 * (eventCoframeOne 1 * eventCoframeOne 3)) =
      -eventPlebanskiVolume := by
  rw [eventCoframeOne_move 2 1, mul_neg]
  rfl

private lemma event_one_three_zero_two :
    eventCoframeOne 1 *
        (eventCoframeOne 3 * (eventCoframeOne 0 * eventCoframeOne 2)) =
      -eventPlebanskiVolume := by
  rw [eventCoframeOne_move 3 0, mul_neg, eventCoframeOne_move 1 0, neg_neg,
    eventCoframeOne_swap 3 2, mul_neg, mul_neg]
  rfl

private lemma event_zero_three_one_two :
    eventCoframeOne 0 *
        (eventCoframeOne 3 * (eventCoframeOne 1 * eventCoframeOne 2)) =
      eventPlebanskiVolume := by
  rw [eventCoframeOne_move 3 1, mul_neg, eventCoframeOne_swap 3 2, mul_neg, mul_neg,
    neg_neg]
  rfl

private lemma event_one_two_zero_three :
    eventCoframeOne 1 *
        (eventCoframeOne 2 * (eventCoframeOne 0 * eventCoframeOne 3)) =
      eventPlebanskiVolume := by
  rw [eventCoframeOne_move 2 0, mul_neg, eventCoframeOne_move 1 0, neg_neg]
  rfl

private lemma eventPair02_pair13 :
    (eventCoframeOne 0 * eventCoframeOne 2) *
        (eventCoframeOne 1 * eventCoframeOne 3) =
      -eventPlebanskiVolume := by
  simpa only [mul_assoc] using event_zero_two_one_three

private lemma eventPair13_pair02 :
    (eventCoframeOne 1 * eventCoframeOne 3) *
        (eventCoframeOne 0 * eventCoframeOne 2) =
      -eventPlebanskiVolume := by
  simpa only [mul_assoc] using event_one_three_zero_two

private lemma eventPair03_pair12 :
    (eventCoframeOne 0 * eventCoframeOne 3) *
        (eventCoframeOne 1 * eventCoframeOne 2) =
      eventPlebanskiVolume := by
  simpa only [mul_assoc] using event_zero_three_one_two

private lemma eventPair12_pair03 :
    (eventCoframeOne 1 * eventCoframeOne 2) *
        (eventCoframeOne 0 * eventCoframeOne 3) =
      eventPlebanskiVolume := by
  simpa only [mul_assoc] using event_one_two_zero_three

private lemma eventSigmaOne_sq (τ : ℂ) :
    eventSigmaOne τ * eventSigmaOne τ =
      (2 * τ) • eventPlebanskiVolume := by
  simp only [eventSigmaOne, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  rw [eventPair01_sq, eventPair23_pair01, eventPair01_pair23, eventPair23_sq]
  module

private lemma eventSigmaTwo_sq (τ : ℂ) :
    eventSigmaTwo τ * eventSigmaTwo τ =
      (2 * τ) • eventPlebanskiVolume := by
  simp only [eventSigmaTwo, sub_eq_add_neg, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, neg_mul, mul_neg]
  rw [eventPair_mul_pair_same_first, eventPair13_pair02, eventPair02_pair13,
    eventPair_mul_pair_same_first]
  module

private lemma eventSigmaThree_sq (τ : ℂ) :
    eventSigmaThree τ * eventSigmaThree τ =
      (2 * τ) • eventPlebanskiVolume := by
  simp only [eventSigmaThree, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  rw [eventPair_mul_pair_same_first, eventPair12_pair03, eventPair03_pair12,
    eventPair_mul_pair_same_first]
  module

private lemma eventSigmaOne_mul_eventSigmaTwo (τ : ℂ) :
    eventSigmaOne τ * eventSigmaTwo τ = 0 := by
  simp only [eventSigmaOne, eventSigmaTwo, sub_eq_add_neg, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, mul_neg]
  rw [eventPair_mul_pair_same_first, eventPair_mul_pair_middle, eventPair_mul_pair_outer,
    eventPair_mul_pair_same_second]
  simp

private lemma eventSigmaOne_mul_eventSigmaThree (τ : ℂ) :
    eventSigmaOne τ * eventSigmaThree τ = 0 := by
  simp only [eventSigmaOne, eventSigmaThree, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm]
  rw [eventPair_mul_pair_same_first, eventPair_mul_pair_middle, eventPair_mul_pair_outer,
    eventPair_mul_pair_same_second]
  simp

private lemma eventSigmaTwo_mul_eventSigmaThree (τ : ℂ) :
    eventSigmaTwo τ * eventSigmaThree τ = 0 := by
  simp only [eventSigmaTwo, eventSigmaThree, sub_eq_add_neg, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, neg_mul]
  rw [eventPair_mul_pair_same_first, eventPair_mul_pair_same_second,
    eventPair_mul_pair_same_second, eventPair_mul_pair_same_first]
  simp

private lemma eventSigmaTwo_mul_eventSigmaOne (τ : ℂ) :
    eventSigmaTwo τ * eventSigmaOne τ = 0 := by
  simp only [eventSigmaOne, eventSigmaTwo, sub_eq_add_neg, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, neg_mul]
  rw [eventPair_mul_pair_same_first, eventPair_mul_pair_outer, eventPair_mul_pair_middle,
    eventPair_mul_pair_same_second]
  simp

private lemma eventSigmaThree_mul_eventSigmaOne (τ : ℂ) :
    eventSigmaThree τ * eventSigmaOne τ = 0 := by
  simp only [eventSigmaOne, eventSigmaThree, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm]
  rw [eventPair_mul_pair_same_first, eventPair_mul_pair_outer,
    eventPair_mul_pair_same_second, eventPair_mul_pair_middle]
  simp

private lemma eventSigmaThree_mul_eventSigmaTwo (τ : ℂ) :
    eventSigmaThree τ * eventSigmaTwo τ = 0 := by
  simp only [eventSigmaTwo, eventSigmaThree, sub_eq_add_neg, add_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, mul_neg]
  rw [eventPair_mul_pair_same_first, eventPair_mul_pair_same_second,
    eventPair_mul_pair_same_second, eventPair_mul_pair_same_first]
  simp

/-- The three degree-two forms of the event-coframe family. -/
def eventSigma (τ : ℂ) : Fin 3 → EventCoframeExterior :=
  ![eventSigmaOne τ, eventSigmaTwo τ, eventSigmaThree τ]

/--
**Event-coframe simplicity law.** The full wedge matrix is scalar: the off-diagonal products
vanish and every diagonal product is `2 τ` times the same oriented four-volume.
-/
theorem eventSigma_simplicity (τ : ℂ) (i j : Fin 3) :
    eventSigma τ i * eventSigma τ j =
      if i = j then (2 * τ) • eventPlebanskiVolume else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [eventSigma, eventSigmaOne_sq, eventSigmaTwo_sq, eventSigmaThree_sq,
      eventSigmaOne_mul_eventSigmaTwo, eventSigmaOne_mul_eventSigmaThree,
      eventSigmaTwo_mul_eventSigmaOne, eventSigmaTwo_mul_eventSigmaThree,
      eventSigmaThree_mul_eventSigmaOne, eventSigmaThree_mul_eventSigmaTwo]

/-- A two-plane exterior field in the oriented `01` and `23` coordinate planes. -/
def eventTwoPlaneForm (first second : ℂ) : EventCoframeExterior :=
  first • (eventCoframeOne 0 * eventCoframeOne 1) +
    second • (eventCoframeOne 2 * eventCoframeOne 3)

/-- The square of a two-plane field is its oriented pseudoscalar coefficient times volume. -/
theorem eventTwoPlaneForm_sq (first second : ℂ) :
    eventTwoPlaneForm first second * eventTwoPlaneForm first second =
      (2 * first * second) • eventPlebanskiVolume := by
  simp only [eventTwoPlaneForm, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  rw [eventPair01_sq, eventPair23_pair01, eventPair01_pair23, eventPair23_sq]
  module

/-- The coordinate four-volume is nonzero in the exterior algebra. -/
theorem eventPlebanskiVolume_ne_zero : eventPlebanskiVolume ≠ 0 := by
  let coframe : Fin 4 → EventCoframe4 := Pi.basisFun ℂ (Fin 4)
  have hLI : LinearIndependent ℂ coframe :=
    (Pi.basisFun ℂ (Fin 4)).linearIndependent
  have htop : exteriorPower.ιMulti ℂ 4 coframe ≠ 0 :=
    exteriorPower_ιMulti_ne_zero_of_linearIndependent coframe hLI
  have heq :
      ((exteriorPower.ιMulti ℂ 4 coframe : ⋀[ℂ]^(4 : ℕ) EventCoframe4) :
          EventCoframeExterior) =
        eventPlebanskiVolume := by
    change ExteriorAlgebra.ιMulti ℂ 4 coframe = eventPlebanskiVolume
    rw [ExteriorAlgebra.ιMulti_apply]
    simp [coframe, eventPlebanskiVolume, eventCoframeOne]
  rw [← heq]
  intro hzero
  apply htop
  exact Subtype.ext hzero

/-- Euclidean quaternionic endpoint of the simplicity family. -/
theorem eventSigma_euclidean_simplicity (i j : Fin 3) :
    eventSigma 1 i * eventSigma 1 j =
      if i = j then 2 • eventPlebanskiVolume else 0 := by
  simpa using! eventSigma_simplicity 1 i j

/--
Complex chiral endpoint used in Lorentzian Plebanski formulations.  A physical Lorentzian metric
still requires separate reality conditions.
-/
theorem eventSigma_complexChiral_simplicity (i j : Fin 3) :
    eventSigma Complex.I i * eventSigma Complex.I j =
      if i = j then (2 * Complex.I) • eventPlebanskiVolume else 0 :=
  eventSigma_simplicity Complex.I i j

/-- At the zero parameter, the entire simplicity wedge matrix degenerates. -/
theorem eventSigma_degenerate_simplicity (i j : Fin 3) :
    eventSigma 0 i * eventSigma 0 j = 0 := by
  simpa using eventSigma_simplicity 0 i j

/-- Away from the degenerate parameter, the three simplicity forms are linearly independent. -/
theorem eventSigma_linearIndependent {τ : ℂ} (hτ : τ ≠ 0) :
    LinearIndependent ℂ (eventSigma τ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  have hmul :=
    congrArg (fun x : EventCoframeExterior => x * eventSigma τ i) hsum
  simp only [Finset.sum_mul, smul_mul_assoc, zero_mul, eventSigma_simplicity] at hmul
  have hdiag : g i • ((2 * τ) • eventPlebanskiVolume) = 0 := by
    simpa using hmul
  rw [smul_smul] at hdiag
  have hscalar : g i * (2 * τ) = 0 :=
    (smul_eq_zero.mp hdiag).resolve_right eventPlebanskiVolume_ne_zero
  rcases mul_eq_zero.mp hscalar with hgi | htwoτ
  · exact hgi
  · exact False.elim ((mul_ne_zero two_ne_zero hτ) htwoτ)

end GaloisForLFunctions.HTGeometry
