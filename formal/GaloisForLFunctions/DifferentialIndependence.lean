import Mathlib.FieldTheory.Differential.Basic
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.Tactic

/-!
# Differential algebraic independence

This file supplies the field-relative notion needed by the multiple-elliptic-gamma matroid theorem.
A family is differentially algebraically independent exactly when the family of all its algebraic
jets is algebraically independent.  This avoids replacing the final theorem by the older
function-level `DifferentiallyAlgebraic` predicate over `ℂ(z)`.
-/

open scoped Differential

namespace GaloisForLFunctions

noncomputable section

/-- The `n`th algebraic derivative of an element of a differential ring. -/
def differentialJet {K : Type*} [CommRing K] [Differential K] (n : ℕ) (x : K) : K :=
  (Differential.deriv^[n]) x

@[simp]
theorem differentialJet_zero {K : Type*} [CommRing K] [Differential K] (x : K) :
    differentialJet 0 x = x := by
  simp [differentialJet]

theorem differentialJet_add {K : Type*} [CommRing K] [Differential K]
    (m n : ℕ) (x : K) :
    differentialJet (m + n) x = differentialJet m (differentialJet n x) := by
  exact Function.iterate_add_apply Differential.deriv m n x

/-- A family in a differential field is differentially algebraically independent over `F` when
the family of all of its jets is algebraically independent over `F`. -/
def DifferentialIndependent (F : Type*) {K : Type*} [CommRing F] [CommRing K]
    [Algebra F K] [Differential K] {ι : Type*} (x : ι → K) : Prop :=
  AlgebraicIndependent F (fun p : ι × ℕ => differentialJet p.2 (x p.1))

/-- An element is differentially algebraic over `F` exactly when its full jet family is
algebraically dependent over `F`. -/
def DifferentialAlgebraicOver (F : Type*) {K : Type*} [CommRing F] [CommRing K]
    [Algebra F K] [Differential K] (x : K) : Prop :=
  ¬ DifferentialIndependent F (fun _ : Unit => x)

/-- Hypertranscendence over a differential-field base is the negation of differential
algebraicity over that base. -/
def HypertranscendentalOver (F : Type*) {K : Type*} [CommRing F] [CommRing K]
    [Algebra F K] [Differential K] (x : K) : Prop :=
  ¬ DifferentialAlgebraicOver F x

theorem hypertranscendentalOver_iff_differentialIndependent_singleton
    (F : Type*) {K : Type*} [CommRing F] [CommRing K] [Algebra F K] [Differential K]
    (x : K) :
    HypertranscendentalOver F x ↔ DifferentialIndependent F (fun _ : Unit => x) := by
  simp [HypertranscendentalOver, DifferentialAlgebraicOver]

/-- Differential independence passes to an injectively indexed subfamily. -/
theorem DifferentialIndependent.comp
    {F K : Type*} [CommRing F] [CommRing K] [Algebra F K] [Differential K]
    {ι ι' : Type*} {x : ι → K} (hx : DifferentialIndependent F x)
    (f : ι' → ι) (hf : Function.Injective f) :
    DifferentialIndependent F (x ∘ f) := by
  let g : ι' × ℕ → ι × ℕ := fun p => (f p.1, p.2)
  have hg : Function.Injective g := by
    rintro ⟨i, n⟩ ⟨j, m⟩ h
    simp only [g, Prod.mk.injEq] at h ⊢
    exact ⟨hf h.1, h.2⟩
  unfold DifferentialIndependent at hx ⊢
  simpa only [Function.comp_apply, g] using AlgebraicIndependent.comp hx g hg

/-- Differential independence implies ordinary algebraic independence of the order-zero
coordinates. -/
theorem DifferentialIndependent.algebraicIndependent
    {F K : Type*} [CommRing F] [CommRing K] [Algebra F K] [Differential K]
    {ι : Type*} {x : ι → K} (hx : DifferentialIndependent F x) :
    AlgebraicIndependent F x := by
  unfold DifferentialIndependent at hx
  have h := AlgebraicIndependent.comp hx (fun i : ι => (i, 0)) (by
    intro i j h
    exact congrArg Prod.fst h)
  simpa using h

/-- Replacing each member of a differentially independent family by any fixed derivative of that
member preserves differential independence. -/
theorem DifferentialIndependent.jetShift
    {F K : Type*} [CommRing F] [CommRing K] [Algebra F K] [Differential K]
    {ι : Type*} {x : ι → K} (hx : DifferentialIndependent F x) (m : ι → ℕ) :
    DifferentialIndependent F (fun i => differentialJet (m i) (x i)) := by
  let g : ι × ℕ → ι × ℕ := fun p => (p.1, p.2 + m p.1)
  have hg : Function.Injective g := by
    rintro ⟨i, n⟩ ⟨j, p⟩ h
    simp only [g, Prod.mk.injEq] at h ⊢
    rcases h with ⟨rfl, h⟩
    exact ⟨rfl, Nat.add_right_cancel h⟩
  unfold DifferentialIndependent at hx ⊢
  have h := AlgebraicIndependent.comp hx g hg
  simpa only [Function.comp_apply, g, ← differentialJet_add] using h

/-- Ordinary algebraic extension of the coefficient field preserves differential independence.
This is the algebraic part of the base-change step used in constant extension. -/
theorem DifferentialIndependent.extendScalars
    {F S K : Type*} [Field F] [Field S] [Field K]
    [Algebra F S] [Algebra S K] [Algebra F K] [IsScalarTower F S K]
    [Differential K] [Algebra.IsAlgebraic F S]
    {ι : Type*} {x : ι → K} (hx : DifferentialIndependent F x) :
    DifferentialIndependent S x := by
  unfold DifferentialIndependent at hx ⊢
  exact AlgebraicIndependent.extendScalars S hx

end

end GaloisForLFunctions
