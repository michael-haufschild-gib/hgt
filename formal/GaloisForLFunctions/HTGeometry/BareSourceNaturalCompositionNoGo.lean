import Mathlib

/-!
# Bare-source natural composition no-go

A binary operation assigned to every bare type and natural under every map is necessarily one of
the two coordinate projections. Consequently no such natural operation is commutative.

This is the binary representable/Yoneda classification, proved directly using `Bool`. It does not
apply once a source has additional incidence or higher-cell structure, and it proves no physical
composition, time, quantumness, spacetime, gravity, or force law.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A polymorphic binary operation on bare small types. -/
abbrev BinaryNaturalOperation :=
  (X : Type) → X × X → X

/-- Naturality under every map of bare types. -/
def BinaryNaturalOperation.Natural
    (op : BinaryNaturalOperation) : Prop :=
  ∀ {X Y : Type} (f : X → Y) (x₀ x₁ : X),
    f (op X (x₀, x₁)) = op Y (f x₀, f x₁)

/-- First-coordinate operation. -/
def binaryFirstProjection : BinaryNaturalOperation :=
  fun _ x => x.1

/-- Second-coordinate operation. -/
def binarySecondProjection : BinaryNaturalOperation :=
  fun _ x => x.2

/-- **Binary Yoneda classification.** Every binary operation natural under all maps of bare
types is exactly one coordinate projection. -/
theorem binaryNaturalOperation_eq_projection
    (op : BinaryNaturalOperation)
    (hnatural : op.Natural) :
    op = binaryFirstProjection ∨ op = binarySecondProjection := by
  cases hchoice : op Bool (false, true) with
  | false =>
      left
      funext X p
      rcases p with ⟨x₀, x₁⟩
      let f : Bool → X := fun b => b.casesOn x₀ x₁
      have h := hnatural f false true
      rw [hchoice] at h
      simpa [f, binaryFirstProjection] using h.symm
  | true =>
      right
      funext X p
      rcases p with ⟨x₀, x₁⟩
      let f : Bool → X := fun b => b.casesOn x₀ x₁
      have h := hnatural f false true
      rw [hchoice] at h
      simpa [f, binarySecondProjection] using h.symm

/-- Commutativity of a polymorphic binary operation on every bare type. -/
def BinaryNaturalOperation.Commutative
    (op : BinaryNaturalOperation) : Prop :=
  ∀ {X : Type} (x₀ x₁ : X),
    op X (x₀, x₁) = op X (x₁, x₀)

/-- No binary operation on all bare types is both natural under every map and commutative. -/
theorem no_commutative_binaryNaturalOperation
    (op : BinaryNaturalOperation)
    (hnatural : op.Natural) :
    ¬ op.Commutative := by
  intro hcomm
  rcases binaryNaturalOperation_eq_projection op hnatural with hfirst | hsecond
  · have h := hcomm false true
    rw [hfirst] at h
    exact Bool.false_ne_true h
  · have h := hcomm false true
    rw [hsecond] at h
    exact Bool.false_ne_true h.symm

end GaloisForLFunctions.HTGeometry
