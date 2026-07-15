import GaloisForLFunctions.HTGeometry.FiniteRangeProjectiveTail
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Recurrent-pattern kernel of a valuation--Veronese layer

For a finite-range point sequence, an observable is nonzero at only finitely many coordinates
exactly when it vanishes on every value with an infinite fibre.  Applied to homogeneous
polynomials, this identifies the complete linear tail kernel of one Veronese layer with the
homogeneous vanishing space of the recurrent point set.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- Values of a sequence whose fibres are infinite. -/
def recurringValueSet {P V : Type*} (x : P → V) : Set V :=
  {v | {p | x p = v}.Infinite}

theorem recurringValueSet_subset_range {P V : Type*} (x : P → V) :
    recurringValueSet x ⊆ Set.range x := by
  intro v hv
  obtain ⟨p, hp⟩ := hv.nonempty
  exact ⟨p, hp⟩

theorem recurringValueSet_finite_of_range_finite {P V : Type*} (x : P → V)
    (hrange : (Set.range x).Finite) :
    (recurringValueSet x).Finite :=
  hrange.subset (recurringValueSet_subset_range x)

/-- **Finite-range observable kernel.**  An observable of a finite-range sequence is eventually
zero exactly when it vanishes on every recurrent value. -/
theorem finiteRange_observable_support_finite_iff
    {P V : Type*} (x : P → V) (hrange : (Set.range x).Finite) (f : V → ℂ) :
    {p | f (x p) ≠ 0}.Finite ↔ ∀ v ∈ recurringValueSet x, f v = 0 := by
  constructor
  · intro hsupp v hv
    by_contra hfv
    have hsub : {p | x p = v} ⊆ {p | f (x p) ≠ 0} := by
      intro p hp
      change x p = v at hp
      change f (x p) ≠ 0
      rw [hp]
      exact hfv
    exact (hv.mono hsub) hsupp
  · intro hvanish
    let bad : Set V := {v | f v ≠ 0}
    have hbad : (Set.range x ∩ bad).Finite := hrange.inter_of_left bad
    have hfibre : ∀ v ∈ Set.range x ∩ bad, {p | x p = v}.Finite := by
      intro v hv
      rw [← Set.not_infinite]
      intro hinf
      exact hv.2 (hvanish v hinf)
    have hunion :
        (⋃ v ∈ Set.range x ∩ bad, {p | x p = v}).Finite :=
      hbad.biUnion hfibre
    apply hunion.subset
    intro p hp
    have hx : x p ∈ Set.range x := ⟨p, rfl⟩
    have hbadp : x p ∈ bad := hp
    exact Set.mem_iUnion₂.mpr ⟨x p, ⟨hx, hbadp⟩, rfl⟩

/-- Polynomial specialization of the finite-range observable kernel. -/
theorem finiteRange_mvPolynomial_eval_support_finite_iff
    {P σ : Type*} (x : P → σ → ℂ) (hrange : (Set.range x).Finite)
    (Q : MvPolynomial σ ℂ) :
    {p | eval (x p) Q ≠ 0}.Finite ↔
      ∀ v ∈ recurringValueSet x, eval v Q = 0 :=
  finiteRange_observable_support_finite_iff x hrange (fun v => eval v Q)

/-- Homogeneous polynomials whose evaluations have finite coordinate support. -/
def homogeneousTailRelationSubmodule
    {P σ : Type*} (x : P → σ → ℂ) (m : ℕ) :
    Submodule ℂ (homogeneousSubmodule σ ℂ m) where
  carrier := {Q | {p | eval (x p) Q.1 ≠ 0}.Finite}
  zero_mem' := by simp
  add_mem' := by
    intro Q R hQ hR
    apply (hQ.union hR).subset
    intro p hp
    simp only [Set.mem_union, Set.mem_setOf_eq] at hp ⊢
    by_contra hQR
    rcases not_or.mp hQR with ⟨hQ, hR⟩
    have hQ0 := not_ne_iff.mp hQ
    have hR0 := not_ne_iff.mp hR
    apply hp
    simp [hQ0, hR0]
  smul_mem' := by
    intro a Q hQ
    apply hQ.subset
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    intro hzero
    apply hp
    simp [hzero]

/-- Homogeneous polynomials vanishing on every recurrent value. -/
def homogeneousRecurringVanishingSubmodule
    {P σ : Type*} (x : P → σ → ℂ) (m : ℕ) :
    Submodule ℂ (homogeneousSubmodule σ ℂ m) where
  carrier := {Q | ∀ v ∈ recurringValueSet x, eval v Q.1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro Q R hQ hR v hv
    simp [hQ v hv, hR v hv]
  smul_mem' := by
    intro a Q hQ v hv
    simp [hQ v hv]

/-- Evaluation of one homogeneous layer on the recurrent point set. -/
def homogeneousRecurringEvaluation
    {P σ : Type*} (x : P → σ → ℂ) (m : ℕ) :
    homogeneousSubmodule σ ℂ m →ₗ[ℂ] (recurringValueSet x → ℂ) where
  toFun Q := fun v => eval v.1 Q.1
  map_add' := by
    intro Q R
    funext v
    simp
  map_smul' := by
    intro a Q
    funext v
    simp

/-- The recurrent vanishing space is the algebraic kernel of recurrent evaluation. -/
theorem homogeneousRecurringVanishingSubmodule_eq_ker
    {P σ : Type*} (x : P → σ → ℂ) (m : ℕ) :
    homogeneousRecurringVanishingSubmodule x m =
      LinearMap.ker (homogeneousRecurringEvaluation x m) := by
  ext Q
  constructor
  · intro hQ
    apply LinearMap.mem_ker.mpr
    funext v
    exact hQ v.1 v.2
  · intro hQ v hv
    have hfun := congrFun (LinearMap.mem_ker.mp hQ) ⟨v, hv⟩
    exact hfun

/-- **Valuation--Veronese layer kernel.**  For a finite-range point sequence, the homogeneous
tail-relation space in degree `m` is exactly the degree-`m` vanishing space of its recurrent
pattern geometry. -/
theorem homogeneousTailRelationSubmodule_eq_recurringVanishing
    {P σ : Type*} (x : P → σ → ℂ) (hrange : (Set.range x).Finite) (m : ℕ) :
    homogeneousTailRelationSubmodule x m =
      homogeneousRecurringVanishingSubmodule x m := by
  ext Q
  exact finiteRange_mvPolynomial_eval_support_finite_iff x hrange Q.1

/-- The homogeneous tail kernel is literally the kernel of evaluation on the recurrent point
set. -/
theorem homogeneousTailRelationSubmodule_eq_ker
    {P σ : Type*} (x : P → σ → ℂ) (hrange : (Set.range x).Finite) (m : ℕ) :
    homogeneousTailRelationSubmodule x m =
      LinearMap.ker (homogeneousRecurringEvaluation x m) := by
  rw [homogeneousTailRelationSubmodule_eq_recurringVanishing x hrange m,
    homogeneousRecurringVanishingSubmodule_eq_ker]

/-- **Homogeneous coordinate realization.**  The degree-`m` tail quotient is canonically the
range of evaluation on the recurrent point geometry. -/
noncomputable def homogeneousTailQuotientEquivRecurringRange
    {P σ : Type*} (x : P → σ → ℂ) (hrange : (Set.range x).Finite) (m : ℕ) :
    (homogeneousSubmodule σ ℂ m ⧸ homogeneousTailRelationSubmodule x m) ≃ₗ[ℂ]
      LinearMap.range (homogeneousRecurringEvaluation x m) := by
  rw [homogeneousTailRelationSubmodule_eq_ker x hrange m]
  exact (homogeneousRecurringEvaluation x m).quotKerEquivRange

/-- The valuation-resolved differential Hilbert number is the dimension of either the homogeneous
tail quotient or its recurrent evaluation image. -/
theorem finrank_homogeneousTailQuotient_eq_recurringRange
    {P σ : Type*} [Fintype σ]
    (x : P → σ → ℂ) (hrange : (Set.range x).Finite) (m : ℕ) :
    Module.finrank ℂ
        (homogeneousSubmodule σ ℂ m ⧸ homogeneousTailRelationSubmodule x m) =
      Module.finrank ℂ (LinearMap.range (homogeneousRecurringEvaluation x m)) :=
  (homogeneousTailQuotientEquivRecurringRange x hrange m).finrank_eq

end

end GaloisForLFunctions.HTGeometry
