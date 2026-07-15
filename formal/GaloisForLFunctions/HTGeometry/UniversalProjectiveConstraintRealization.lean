import GaloisForLFunctions.HTGeometry.CountablePrimeProfileRealization
import Mathlib.Topology.Algebra.MvPolynomial

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- A chosen countable dense profile in a nonempty subset of a finite-dimensional complex profile
space. -/
def denseConstraintProfile {σ : Type*} [Fintype σ]
    (K : Set (σ → ℂ)) [Nonempty K] : ℕ → (σ → ℂ) :=
  fun n => (TopologicalSpace.denseSeq K n).1

/-- A multivariable polynomial vanishes on the chosen dense profile exactly when it vanishes on
the whole constraint set. -/
theorem eval_denseConstraintProfile_eq_zero_iff
    {σ : Type*} [Fintype σ] (K : Set (σ → ℂ)) [Nonempty K]
    (Q : MvPolynomial σ ℂ) :
    (∀ n, eval (denseConstraintProfile K n) Q = 0) ↔
      ∀ v ∈ K, eval v Q = 0 := by
  constructor
  · intro hzero
    let g : K → ℂ := fun v => eval v.1 Q
    have hg : Continuous g := by
      simpa only [g] using
        (MvPolynomial.continuous_eval Q).comp
          (continuous_subtype_val : Continuous (fun v : K => v.1))
    have heq : g = fun _ => 0 := by
      apply (TopologicalSpace.denseRange_denseSeq K).equalizer hg continuous_const
      funext n
      exact hzero n
    intro v hv
    exact congrFun heq ⟨v, hv⟩
  · intro hvanish n
    exact hvanish (denseConstraintProfile K n)
      (TopologicalSpace.denseSeq K n).2

/-- Homogeneous polynomials vanishing on a prescribed constraint set. -/
def homogeneousConstraintVanishingSubmodule
    {σ : Type*} (K : Set (σ → ℂ)) (m : ℕ) :
    Submodule ℂ (homogeneousSubmodule σ ℂ m) where
  carrier := {Q | ∀ v ∈ K, eval v Q.1 = 0}
  zero_mem' := by simp
  add_mem' := by
    intro Q R hQ hR v hv
    simp [hQ v hv, hR v hv]
  smul_mem' := by
    intro a Q hQ v hv
    simp [hQ v hv]

/-- Repeating a dense constraint profile on infinite prime fibres realizes exactly the prescribed
homogeneous vanishing space as the recurrent vanishing space. -/
theorem homogeneousRecurringVanishingSubmodule_infinitelyRepeatedDenseConstraint
    {σ : Type*} [Fintype σ]
    (e : ℕ ≃ Nat.Primes) (K : Set (σ → ℂ)) [Nonempty K] (m : ℕ) :
    homogeneousRecurringVanishingSubmodule
        (infinitelyRepeatedPrimeProfile e (denseConstraintProfile K)) m =
      homogeneousConstraintVanishingSubmodule K m := by
  ext Q
  change
    (∀ v ∈ recurringValueSet
        (infinitelyRepeatedPrimeProfile e (denseConstraintProfile K)),
      eval v Q.1 = 0) ↔
    ∀ v ∈ K, eval v Q.1 = 0
  rw [recurringValueSet_infinitelyRepeatedPrimeProfile]
  constructor
  · intro hrec
    apply (eval_denseConstraintProfile_eq_zero_iff K Q.1).mp
    intro n
    exact hrec (denseConstraintProfile K n) ⟨n, rfl⟩
  · intro hvanish v hv
    obtain ⟨n, rfl⟩ := hv
    exact (eval_denseConstraintProfile_eq_zero_iff K Q.1).mpr hvanish n

/-- **Universal homogeneous constraint realization.** Every nonempty constraint subset of a
finite-dimensional complex profile space is realized exactly, degree by degree, as the finite-prime
tail relation geometry of a cofinally recurrent prime profile. -/
theorem homogeneousTailRelationSubmodule_infinitelyRepeatedDenseConstraint
    {σ : Type*} [Fintype σ]
    (e : ℕ ≃ Nat.Primes) (K : Set (σ → ℂ)) [Nonempty K] (m : ℕ) :
    homogeneousTailRelationSubmodule
        (infinitelyRepeatedPrimeProfile e (denseConstraintProfile K)) m =
      homogeneousConstraintVanishingSubmodule K m := by
  rw [homogeneousTailRelationSubmodule_eq_recurringVanishing_of_cofinitelyRecurring
    (infinitelyRepeatedPrimeProfile e (denseConstraintProfile K))
    (infinitelyRepeatedPrimeProfile_cofinitelyRecurring e (denseConstraintProfile K)) m]
  exact homogeneousRecurringVanishingSubmodule_infinitelyRepeatedDenseConstraint e K m

/-- The homogeneous coordinate Hilbert function of an arbitrary constraint set. -/
def constraintHomogeneousHilbertFunction
    {σ : Type*} [Fintype σ] (K : Set (σ → ℂ)) (m : ℕ) : ℕ :=
  Module.finrank ℂ
    (homogeneousSubmodule σ ℂ m ⧸ homogeneousConstraintVanishingSubmodule K m)

/-- Under the universal prime realization, the valuation-tail Hilbert function is exactly the
ordinary homogeneous coordinate Hilbert function of the prescribed constraint. -/
theorem valuationTailHilbertFunction_infinitelyRepeatedDenseConstraint
    {σ : Type*} [Fintype σ]
    (e : ℕ ≃ Nat.Primes) (K : Set (σ → ℂ)) [Nonempty K] (m : ℕ) :
    valuationTailHilbertFunction
        (infinitelyRepeatedPrimeProfile e (denseConstraintProfile K)) m =
      constraintHomogeneousHilbertFunction K m := by
  unfold valuationTailHilbertFunction constraintHomogeneousHilbertFunction
  rw [homogeneousTailRelationSubmodule_infinitelyRepeatedDenseConstraint e K m]

/-- **Existential universal constraint realization.** Every nonempty constraint set admits an
actual prime profile, with no enumeration supplied as a hypothesis, whose complete homogeneous
tail kernels and valuation Hilbert numbers are exactly those of the constraint. -/
theorem exists_cofinitelyRecurring_primeProfile_realizing_constraint
    {σ : Type*} [Fintype σ] (K : Set (σ → ℂ)) [Nonempty K] :
    ∃ x : Nat.Primes → (σ → ℂ),
      CofinitelyRecurring x ∧
      ∀ m,
        homogeneousTailRelationSubmodule x m =
            homogeneousConstraintVanishingSubmodule K m ∧
          valuationTailHilbertFunction x m =
            constraintHomogeneousHilbertFunction K m := by
  let e : ℕ ≃ Nat.Primes :=
    Classical.choice (inferInstance : Nonempty (ℕ ≃ Nat.Primes))
  let x := infinitelyRepeatedPrimeProfile e (denseConstraintProfile K)
  refine ⟨x, infinitelyRepeatedPrimeProfile_cofinitelyRecurring e
    (denseConstraintProfile K), fun m => ?_⟩
  exact ⟨homogeneousTailRelationSubmodule_infinitelyRepeatedDenseConstraint e K m,
    valuationTailHilbertFunction_infinitelyRepeatedDenseConstraint e K m⟩

/-- The recurrent Hilbert function of the universal prime realization is the homogeneous
coordinate Hilbert function of the prescribed constraint. -/
theorem recurrentHomogeneousHilbertFunction_infinitelyRepeatedDenseConstraint
    {σ : Type*} [Fintype σ]
    (e : ℕ ≃ Nat.Primes) (K : Set (σ → ℂ)) [Nonempty K] (m : ℕ) :
    recurrentHomogeneousHilbertFunction
        (infinitelyRepeatedPrimeProfile e (denseConstraintProfile K)) m =
      constraintHomogeneousHilbertFunction K m := by
  rw [← valuationTailHilbertFunction_eq_recurrent_of_cofinitelyRecurring
    (infinitelyRepeatedPrimeProfile e (denseConstraintProfile K))
    (infinitelyRepeatedPrimeProfile_cofinitelyRecurring e (denseConstraintProfile K)) m]
  exact valuationTailHilbertFunction_infinitelyRepeatedDenseConstraint e K m

/-- **Universal complete relation realization.** Every nonempty constraint subset of a
finite-dimensional complex profile space has a cofinally recurrent prime realization whose full
finite-window differential relation ideal is generated by its prolonged homogeneous coordinate
reductions. -/
theorem universalConstraint_complete_relationIdeal
    {d : ℕ} {σ : Type u} [Fintype σ]
    {A : Fin d → Type u}
    [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)]
    (e : ℕ ≃ Nat.Primes) (K : Set (σ → ℂ)) [Nonempty K]
    [Nonempty (Σ r : Fin d,
      fullRecurrentHilbertIndex
        (infinitelyRepeatedPrimeProfile e (denseConstraintProfile K)) (r + 1) × A r)]
    (α : ∀ r, A r → ℂ)
    (hdistinct : ∀ r, Function.Injective (fun a ↦ (α r a).re)) :
    let x := infinitelyRepeatedPrimeProfile e (denseConstraintProfile K)
    let P := fullRecurrentHilbertValuationPresentation (d := d) x
    let T := P.toRecurringPivotPresentation
      (infinitelyRepeatedPrimeProfile_cofinitelyRecurring e (denseConstraintProfile K))
    GaloisForLFunctions.differentialRelationIdeal
        (C := finitePrimeRationalCoefficientField)
        (Sum.elim (T.pivotPalette α) (T.dependentPalette α)) =
      differentialPivotRelationIdeal T.paletteMatrix (T.baseCorrection α) := by
  dsimp only
  exact fullRecurrentHilbert_complete_relationIdeal_of_cofinitelyRecurring
    (infinitelyRepeatedPrimeProfile e (denseConstraintProfile K))
    (infinitelyRepeatedPrimeProfile_cofinitelyRecurring e (denseConstraintProfile K))
    α hdistinct

/-- **Universal valuation--Hilbert realization theorem.** Every nonempty constraint subset of a
finite-dimensional complex profile space occurs as an exact prime-supported HT constraint: its
homogeneous Hilbert numbers are the differential ranks of the matching valuation sectors, the
Hilbert pivots are a differential transcendence basis, and the homogeneous reductions generate
the entire monomial-carrier field. -/
theorem universalConstraint_differentialBasis_and_rank
    {d : ℕ} {σ : Type u} [Fintype σ]
    {A : Fin d → Type u}
    [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)]
    (e : ℕ ≃ Nat.Primes) (K : Set (σ → ℂ)) [Nonempty K]
    [Nonempty (Σ r : Fin d,
      fullRecurrentHilbertIndex
        (infinitelyRepeatedPrimeProfile e (denseConstraintProfile K)) (r + 1) × A r)]
    (α : ∀ r, A r → ℂ)
    (hdistinct : ∀ r, Function.Injective (fun a ↦ (α r a).re)) :
    let x := infinitelyRepeatedPrimeProfile e (denseConstraintProfile K)
    let P := fullRecurrentHilbertValuationPresentation (d := d) x
    let T := P.toRecurringPivotPresentation
      (infinitelyRepeatedPrimeProfile_cofinitelyRecurring e (denseConstraintProfile K))
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
        (T.pivotPalette α) ∧
      GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (Sum.elim (T.pivotPalette α) (T.dependentPalette α))) =
        GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (T.pivotPalette α)) ∧
      Fintype.card (Σ r : Fin d,
          fullRecurrentHilbertIndex x (r + 1) × A r) =
        ∑ r : Fin d,
          constraintHomogeneousHilbertFunction K (r + 1) * Fintype.card (A r) := by
  dsimp only
  have h := fullRecurrentHilbert_differentialBasis_and_rank_of_cofinitelyRecurring
    (infinitelyRepeatedPrimeProfile e (denseConstraintProfile K))
    (infinitelyRepeatedPrimeProfile_cofinitelyRecurring e (denseConstraintProfile K))
    α hdistinct
  simpa only [recurrentHomogeneousHilbertFunction_infinitelyRepeatedDenseConstraint]
    using h

end

end GaloisForLFunctions.HTGeometry
