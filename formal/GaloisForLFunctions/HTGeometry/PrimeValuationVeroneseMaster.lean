import GaloisForLFunctions.HTGeometry.PrimeValuationVeroneseKernel
import GaloisForLFunctions.HTGeometry.PrimeValuationVeroneseRelationIdeal

/-!
# Prime-valuation Veronese master theorem

This module closes the geometric-to-differential bridge.  A basis of homogeneous polynomial
observables on the recurrent value set becomes a tail-independent coefficient basis in the
matching prime-power valuation layer.  Every remaining homogeneous observable has a finite-tail
residual in its recurrent coordinate expansion.  The valuation relation theorem then computes the
complete differential relation ideal.

Thus polynomial degree on the recurrent constraint is converted into prime-power valuation degree
without loss: no nonlinear or cross-degree differential relations remain hidden.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction MvPolynomial
open scoped Differential

noncomputable section

universe u

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 80000

/-- Layerwise homogeneous coordinate data on the recurrent value set.  Layer `r` represents
homogeneous degree and valuation degree `r+1`. -/
structure RecurrentHomogeneousValuationPresentation
    (d : ℕ) (σ : Type u) (J R : Fin d → Type u)
    [∀ r, Fintype (J r)] (x : Nat.Primes → σ → ℂ) where
  pivot : ∀ r, J r → homogeneousSubmodule σ ℂ (r + 1)
  dependent : ∀ r, R r → homogeneousSubmodule σ ℂ (r + 1)
  coefficient : ∀ r, R r → J r → ℂ
  pivotRecurringIndependent : ∀ r,
    LinearIndependent ℂ (fun j ↦ fun v : recurringValueSet x ↦
      eval v.1 (pivot r j).1)
  pivotRecurringSpans : ∀ r : Fin d,
    ∀ Q : homogeneousSubmodule σ ℂ (r + 1),
    ∃ z : J r → ℂ, ∀ v : recurringValueSet x,
      eval v.1 Q.1 = ∑ j, z j * eval v.1 (pivot r j).1
  dependentRecurringExpansion : ∀ r q (v : recurringValueSet x),
    eval v.1 (dependent r q).1 =
      ∑ j, coefficient r q j * eval v.1 (pivot r j).1

/-- The prime coefficient column obtained by evaluating a homogeneous observable on the source
sequence. -/
def RecurrentHomogeneousValuationPresentation.pivotColumn
    {d : ℕ} {σ : Type u} {J R : Fin d → Type u} [∀ r, Fintype (J r)]
    {x : Nat.Primes → σ → ℂ}
    (P : RecurrentHomogeneousValuationPresentation d σ J R x)
    (r : Fin d) (j : J r) (p : Nat.Primes) : ℂ :=
  eval (x p) (P.pivot r j).1

def RecurrentHomogeneousValuationPresentation.dependentColumn
    {d : ℕ} {σ : Type u} {J R : Fin d → Type u} [∀ r, Fintype (J r)]
    {x : Nat.Primes → σ → ℂ}
    (P : RecurrentHomogeneousValuationPresentation d σ J R x)
    (r : Fin d) (q : R r) (p : Nat.Primes) : ℂ :=
  eval (x p) (P.dependent r q).1

/-- A chosen pivot, regarded as an element of the recurrent evaluation range. -/
def RecurrentHomogeneousValuationPresentation.pivotRangeElement
    {d : ℕ} {σ : Type u} {J R : Fin d → Type u} [∀ r, Fintype (J r)]
    {x : Nat.Primes → σ → ℂ}
    (P : RecurrentHomogeneousValuationPresentation d σ J R x)
    (r : Fin d) (j : J r) :
    LinearMap.range (homogeneousRecurringEvaluation x (r + 1)) :=
  ⟨fun v ↦ eval v.1 (P.pivot r j).1, ⟨P.pivot r j, rfl⟩⟩

/-- The chosen recurrent homogeneous pivot vectors are linearly independent in the complete
degree-`r+1` evaluation range. -/
theorem RecurrentHomogeneousValuationPresentation.pivotRangeElement_linearIndependent
    {d : ℕ} {σ : Type u} {J R : Fin d → Type u} [∀ r, Fintype (J r)]
    {x : Nat.Primes → σ → ℂ}
    (P : RecurrentHomogeneousValuationPresentation d σ J R x) (r : Fin d) :
    LinearIndependent ℂ (P.pivotRangeElement r) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro z hz
  have hLI := P.pivotRecurringIndependent r
  rw [Fintype.linearIndependent_iff] at hLI
  apply hLI z
  funext v
  have hv := congrFun (congrArg
    (fun y : LinearMap.range (homogeneousRecurringEvaluation x (r + 1)) => y.1) hz) v
  simpa [RecurrentHomogeneousValuationPresentation.pivotRangeElement,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hv

/-- Every recurrent homogeneous evaluation vector lies in the span of the chosen pivots. -/
theorem RecurrentHomogeneousValuationPresentation.mem_span_pivotRangeElement
    {d : ℕ} {σ : Type u} {J R : Fin d → Type u} [∀ r, Fintype (J r)]
    {x : Nat.Primes → σ → ℂ}
    (P : RecurrentHomogeneousValuationPresentation d σ J R x) (r : Fin d)
    (y : LinearMap.range (homogeneousRecurringEvaluation x (r + 1))) :
    y ∈ Submodule.span ℂ (Set.range (P.pivotRangeElement r)) := by
  classical
  obtain ⟨Q, hQ⟩ := y.2
  obtain ⟨z, hz⟩ := P.pivotRecurringSpans r Q
  have hy : y = ∑ j, z j • P.pivotRangeElement r j := by
    apply Subtype.ext
    funext v
    have hQv := congrFun hQ v
    rw [← hQv]
    simpa [RecurrentHomogeneousValuationPresentation.pivotRangeElement,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hz v
  rw [hy]
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self j))

/-- The chosen recurrent homogeneous pivots form a basis of the complete degree-`r+1`
evaluation range. -/
noncomputable def RecurrentHomogeneousValuationPresentation.pivotRangeBasis
    {d : ℕ} {σ : Type u} {J R : Fin d → Type u} [∀ r, Fintype (J r)]
    {x : Nat.Primes → σ → ℂ}
    (P : RecurrentHomogeneousValuationPresentation d σ J R x) (r : Fin d) :
    Module.Basis (J r) ℂ
      (LinearMap.range (homogeneousRecurringEvaluation x (r + 1))) :=
  Module.Basis.mk (P.pivotRangeElement_linearIndependent r)
    (fun y _ => P.mem_span_pivotRangeElement r y)

/-- The recurrent degree-`r+1` evaluation rank is exactly the number of chosen pivots. -/
theorem RecurrentHomogeneousValuationPresentation.finrank_recurringRange_eq_card
    {d : ℕ} {σ : Type u} {J R : Fin d → Type u} [∀ r, Fintype (J r)]
    {x : Nat.Primes → σ → ℂ}
    (P : RecurrentHomogeneousValuationPresentation d σ J R x) (r : Fin d) :
    Module.finrank ℂ
        (LinearMap.range (homogeneousRecurringEvaluation x (r + 1))) =
      Fintype.card (J r) :=
  Module.finrank_eq_card_basis (P.pivotRangeBasis r)

/-- The degree-`r+1` homogeneous tail quotient has the exact pivot cardinality. -/
theorem RecurrentHomogeneousValuationPresentation.finrank_tailQuotient_eq_card
    {d : ℕ} {σ : Type u} [Fintype σ]
    {J R : Fin d → Type u} [∀ r, Fintype (J r)]
    {x : Nat.Primes → σ → ℂ}
    (P : RecurrentHomogeneousValuationPresentation d σ J R x)
    (hrange : (Set.range x).Finite) (r : Fin d) :
    Module.finrank ℂ
        (homogeneousSubmodule σ ℂ (r + 1) ⧸
          homogeneousTailRelationSubmodule x (r + 1)) =
      Fintype.card (J r) := by
  rw [finrank_homogeneousTailQuotient_eq_recurringRange x hrange (r + 1)]
  exact P.finrank_recurringRange_eq_card r

/-- Evaluation of the chosen recurrent homogeneous basis is independent modulo finite prime
support. -/
theorem RecurrentHomogeneousValuationPresentation.pivotColumn_tailIndependent
    {d : ℕ} {σ : Type u} {J R : Fin d → Type u} [∀ r, Fintype (J r)]
    {x : Nat.Primes → σ → ℂ}
    (P : RecurrentHomogeneousValuationPresentation d σ J R x)
    (hrange : (Set.range x).Finite) (r : Fin d) :
    TailCoefficientIndependent (P.pivotColumn r) := by
  apply (finiteRange_observable_tailIndependent_iff x hrange
    (fun j v ↦ eval v (P.pivot r j).1)).2
  exact P.pivotRecurringIndependent r

/-- A finite-range source gives every finite homogeneous pivot family finite joint pattern range. -/
theorem RecurrentHomogeneousValuationPresentation.pivotColumn_patternRangeFinite
    {d : ℕ} {σ : Type u} {J R : Fin d → Type u} [∀ r, Fintype (J r)]
    {x : Nat.Primes → σ → ℂ}
    (P : RecurrentHomogeneousValuationPresentation d σ J R x)
    (hrange : (Set.range x).Finite) (r : Fin d) :
    (Set.range (coefficientPattern (P.pivotColumn r))).Finite := by
  let obs : (σ → ℂ) → (J r → ℂ) := fun v j ↦ eval v (P.pivot r j).1
  apply (hrange.image obs).subset
  intro b hb
  obtain ⟨p, rfl⟩ := hb
  refine ⟨x p, ⟨p, rfl⟩, ?_⟩
  rfl

/-- A recurrent homogeneous coordinate expansion fails only on finitely many primes. -/
theorem RecurrentHomogeneousValuationPresentation.residualFinite
    {d : ℕ} {σ : Type u} {J R : Fin d → Type u} [∀ r, Fintype (J r)]
    {x : Nat.Primes → σ → ℂ}
    (P : RecurrentHomogeneousValuationPresentation d σ J R x)
    (hrange : (Set.range x).Finite) (r : Fin d) (q : R r) :
    {p | P.dependentColumn r q p -
      ∑ j, P.coefficient r q j * P.pivotColumn r j p ≠ 0}.Finite := by
  apply (finiteRange_observable_support_finite_iff x hrange
    (fun v ↦ eval v (P.dependent r q).1 -
      ∑ j, P.coefficient r q j * eval v (P.pivot r j).1)).2
  intro v hv
  rw [P.dependentRecurringExpansion r q ⟨v, hv⟩]
  ring

/-- The homogeneous recurrent coordinate data canonically supplies the layerwise tail-pivot
presentation consumed by the prime-valuation relation theorem. -/
def RecurrentHomogeneousValuationPresentation.toTailPivotPresentation
    {d : ℕ} {σ : Type u} {J R : Fin d → Type u} [∀ r, Fintype (J r)]
    {x : Nat.Primes → σ → ℂ}
    (P : RecurrentHomogeneousValuationPresentation d σ J R x)
    (hrange : (Set.range x).Finite) :
    PrimeValuationTailPivotPresentation d J R where
  pivot := P.pivotColumn
  dependent := P.dependentColumn
  coefficient := P.coefficient
  pivotTailIndependent := P.pivotColumn_tailIndependent hrange
  pivotPatternRangeFinite := P.pivotColumn_patternRangeFinite hrange
  residualFinite := P.residualFinite hrange

/-- **Prime-valuation Veronese completeness.**  Given any homogeneous coordinate basis in each
degree, the matching valuation-resolved pivot palette is a differential basis and the prolonged
homogeneous coordinate reductions generate the complete relation ideal of all chosen observables.
There are no additional nonlinear relations and no relations mixing valuation degrees. -/
theorem RecurrentHomogeneousValuationPresentation.complete_relationIdeal
    {d : ℕ} {σ : Type u} {J R A : Fin d → Type u}
    [∀ r, Fintype (J r)] [∀ r, DecidableEq (J r)]
    [∀ r, Fintype (R r)] [∀ r, DecidableEq (R r)]
    [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)] [∀ r, Nonempty (A r)]
    [Nonempty (Σ r, J r × A r)]
    {x : Nat.Primes → σ → ℂ}
    (P : RecurrentHomogeneousValuationPresentation d σ J R x)
    (hrange : (Set.range x).Finite) (α : ∀ r, A r → ℂ)
    (hdistinct : ∀ r, Function.Injective (fun a ↦ (α r a).re)) :
    let T := P.toTailPivotPresentation hrange
    GaloisForLFunctions.differentialRelationIdeal
        (C := finitePrimeRationalCoefficientField)
        (Sum.elim (T.pivotPalette α) (T.dependentPalette α)) =
      differentialPivotRelationIdeal T.paletteMatrix (T.baseCorrection α) := by
  dsimp only
  exact (P.toTailPivotPresentation hrange).complete_relationIdeal α hdistinct

/-- The chosen recurrent homogeneous bases become an exact differential transcendence basis of
the full valuation-resolved palette field. -/
theorem RecurrentHomogeneousValuationPresentation.differentialBasis
    {d : ℕ} {σ : Type u} {J R A : Fin d → Type u}
    [∀ r, Fintype (J r)] [∀ r, DecidableEq (J r)]
    [∀ r, Fintype (R r)] [∀ r, DecidableEq (R r)]
    [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)] [∀ r, Nonempty (A r)]
    [Nonempty (Σ r, J r × A r)]
    {x : Nat.Primes → σ → ℂ}
    (P : RecurrentHomogeneousValuationPresentation d σ J R x)
    (hrange : (Set.range x).Finite) (α : ∀ r, A r → ℂ)
    (hdistinct : ∀ r, Function.Injective (fun a ↦ (α r a).re)) :
    let T := P.toTailPivotPresentation hrange
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
        (T.pivotPalette α) ∧
      GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (Sum.elim (T.pivotPalette α) (T.dependentPalette α))) =
        GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (T.pivotPalette α)) := by
  dsimp only
  exact (P.toTailPivotPresentation hrange).differentialBasis α hdistinct

end

end GaloisForLFunctions.HTGeometry
