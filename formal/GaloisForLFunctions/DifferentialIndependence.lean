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

@[simp]
theorem differentialJet_succ {K : Type*} [CommRing K] [Differential K]
    (n : ℕ) (x : K) :
    differentialJet (n + 1) x = (differentialJet n x)′ := by
  exact Function.iterate_succ_apply' Differential.deriv n x

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

/-- The set of all derivatives of elements of `s`. -/
def differentialJetSet {K : Type*} [CommRing K] [Differential K] (s : Set K) : Set K :=
  {y | ∃ x ∈ s, ∃ n : ℕ, differentialJet n x = y}

/-- The differential field generated by `s`, realized as the ordinary field generated by all
jets of `s`. -/
def differentialAdjoin (F : Type*) {K : Type*} [Field F] [Field K]
    [Algebra F K] [Differential K] (s : Set K) : IntermediateField F K :=
  IntermediateField.adjoin F (differentialJetSet s)

theorem subset_differentialAdjoin (F : Type*) {K : Type*} [Field F] [Field K]
    [Algebra F K] [Differential K] (s : Set K) :
    s ⊆ differentialAdjoin F s := by
  intro x hx
  exact IntermediateField.subset_adjoin F _ ⟨x, hx, 0, by simp⟩

theorem differentialJet_mem_differentialAdjoin (F : Type*) {K : Type*}
    [Field F] [Field K] [Algebra F K] [Differential K]
    {s : Set K} {x : K} (hx : x ∈ s) (n : ℕ) :
    differentialJet n x ∈ differentialAdjoin F s :=
  IntermediateField.subset_adjoin F _ ⟨x, hx, n, rfl⟩

/-- A field inside a differential field is derivation-closed when it contains the derivative of
each of its elements. -/
def DerivationClosed {F K : Type*} [Field F] [Field K] [Algebra F K] [Differential K]
    (L : IntermediateField F K) : Prop :=
  ∀ ⦃x : K⦄, x ∈ L → x′ ∈ L

/-- The field generated by all jets is closed under the derivation. -/
theorem derivationClosed_differentialAdjoin
    (F : Type*) {K : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K] (s : Set K) :
    DerivationClosed (differentialAdjoin F s) := by
  intro x hx
  apply IntermediateField.adjoin_induction F (s := differentialJetSet s) (p := fun y _ => y′ ∈
    differentialAdjoin F s)
  · rintro y ⟨z, hz, n, rfl⟩
    rw [← differentialJet_succ]
    exact differentialJet_mem_differentialAdjoin F hz (n + 1)
  · intro c
    rw [deriv_algebraMap]
    exact IntermediateField.algebraMap_mem _ _
  · intro a b ha hb hda hdb
    rw [map_add]
    exact IntermediateField.add_mem _ hda hdb
  · intro a ha hda
    rw [Derivation.leibniz_inv]
    have hainv : a⁻¹ ∈ differentialAdjoin F s := IntermediateField.inv_mem _ ha
    have hasq : a⁻¹ ^ (2 : ℕ) ∈ differentialAdjoin F s := by
      simpa [pow_two] using IntermediateField.mul_mem _ hainv hainv
    exact IntermediateField.mul_mem _ (IntermediateField.neg_mem _ hasq) hda
  · intro a b ha hb hda hdb
    rw [Derivation.leibniz]
    exact IntermediateField.add_mem _
      (IntermediateField.mul_mem _ ha hdb) (IntermediateField.mul_mem _ hb hda)
  exact hx

/-- Minimality of differential adjunction: every derivation-closed intermediate field containing
`s` contains the field generated by all jets of `s`. -/
theorem differentialAdjoin_le
    (F : Type*) {K : Type*} [Field F] [Field K] [Algebra F K] [Differential K]
    {s : Set K} {L : IntermediateField F K}
    (hsL : s ⊆ L) (hL : DerivationClosed L) :
    differentialAdjoin F s ≤ L := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro y ⟨x, hx, n, rfl⟩
  induction n with
  | zero => simpa using hsL hx
  | succ n ih =>
      rw [differentialJet_succ]
      exact hL ih

/-- Restrict the ambient derivation to a derivation-closed intermediate field. -/
@[reducible]
noncomputable def derivationClosedDifferential
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Differential K]
    (L : IntermediateField F K) (hL : DerivationClosed L) : Differential L where
  deriv :=
    { toLinearMap :=
        { toFun := fun x => ⟨x.1′, hL x.2⟩
          map_add' := fun x y => Subtype.ext (Differential.deriv.map_add x.1 y.1)
          map_smul' := fun n x => Subtype.ext (Differential.deriv.map_smul n x.1) }
      map_one_eq_zero' := Subtype.ext Differential.deriv.map_one_eq_zero
      leibniz' := fun x y => Subtype.ext (Differential.deriv.leibniz x.1 y.1) }

@[simp]
theorem derivationClosedDifferential_apply
    {F K : Type*} [Field F] [Field K] [Algebra F K] [Differential K]
    (L : IntermediateField F K) (hL : DerivationClosed L) (x : L) :
    letI := derivationClosedDifferential L hL
    ((x′ : L) : K) = x.1′ :=
  rfl

/-- The differential field generated by a set inherits the ambient derivation. -/
noncomputable instance differentialAdjoin.instDifferential
    (F : Type*) {K : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K] (s : Set K) :
    Differential (differentialAdjoin F s) :=
  derivationClosedDifferential _ (derivationClosed_differentialAdjoin F s)

/-- Differential adjunction is a differential algebra over the base field. -/
instance differentialAdjoin.instDifferentialAlgebra
    (F : Type*) {K : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K] (s : Set K) :
    DifferentialAlgebra F (differentialAdjoin F s) where
  deriv_algebraMap c := by
    apply Subtype.ext
    exact deriv_algebraMap c

end

end GaloisForLFunctions
