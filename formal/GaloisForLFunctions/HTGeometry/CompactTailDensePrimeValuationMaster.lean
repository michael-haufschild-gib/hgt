import GaloisForLFunctions.HTGeometry.CompactTailDensePrimeShiftJet
import GaloisForLFunctions.HTGeometry.CofinalRecurrentPrimeValuationMaster

/-!
# Compact tail-dense prime valuation master theorem

This module identifies the complete arithmetic differential geometry of a prime profile whose
every cofinite tail is dense in a prescribed constraint set. In each homogeneous degree, the
constraint evaluation range supplies canonical Hilbert pivots. Tail-dense shift--jet separation
makes all their finite valuation palettes differentially independent, while exact expansion on the
constraint set reduces every monomial carrier to those pivots.

Consequently the constraint Hilbert function is the exact differential rank spectrum and the
homogeneous coordinate reductions generate the complete differential relation ideal. No repeated
profile values, finite coefficient range, or rate of equidistribution is required.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction MvPolynomial Set
open scoped Differential

noncomputable section

universe u

/-- Evaluation of one homogeneous polynomial layer on a prescribed constraint set. -/
def homogeneousConstraintEvaluation
    {σ : Type u} (K : Set (σ → ℂ)) (m : ℕ) :
    homogeneousSubmodule σ ℂ m →ₗ[ℂ] (K → ℂ) where
  toFun Q := fun v => eval v.1 Q.1
  map_add' Q R := by funext v; simp
  map_smul' z Q := by funext v; simp

/-- The homogeneous constraint vanishing space is the kernel of restriction to the constraint. -/
theorem homogeneousConstraintVanishingSubmodule_eq_ker
    {σ : Type u} (K : Set (σ → ℂ)) (m : ℕ) :
    homogeneousConstraintVanishingSubmodule K m =
      LinearMap.ker (homogeneousConstraintEvaluation K m) := by
  ext Q
  constructor
  · intro hQ
    apply LinearMap.mem_ker.mpr
    funext v
    exact hQ v.1 v.2
  · intro hQ v hv
    exact congrFun (LinearMap.mem_ker.mp hQ) ⟨v, hv⟩

/-- The homogeneous coordinate quotient is canonically the range of constraint evaluation. -/
noncomputable def homogeneousConstraintQuotientEquivRange
    {σ : Type u} (K : Set (σ → ℂ)) (m : ℕ) :
    (homogeneousSubmodule σ ℂ m ⧸ homogeneousConstraintVanishingSubmodule K m) ≃ₗ[ℂ]
      LinearMap.range (homogeneousConstraintEvaluation K m) := by
  rw [homogeneousConstraintVanishingSubmodule_eq_ker]
  exact (homogeneousConstraintEvaluation K m).quotKerEquivRange

/-- The rank of the homogeneous evaluation range on the constraint set. -/
def constraintEvaluationHilbertFunction
    {σ : Type u} [Fintype σ] (K : Set (σ → ℂ)) (m : ℕ) : ℕ :=
  Module.finrank ℂ (LinearMap.range (homogeneousConstraintEvaluation K m))

/-- Evaluation rank and homogeneous-coordinate quotient rank are equal. -/
theorem constraintEvaluationHilbertFunction_eq_constraintHomogeneousHilbertFunction
    {σ : Type u} [Fintype σ] (K : Set (σ → ℂ)) (m : ℕ) :
    constraintEvaluationHilbertFunction K m = constraintHomogeneousHilbertFunction K m := by
  unfold constraintEvaluationHilbertFunction constraintHomogeneousHilbertFunction
  exact (homogeneousConstraintQuotientEquivRange K m).finrank_eq.symm

/-- Universe-lifted full Hilbert index of one constraint layer. -/
abbrev fullConstraintHilbertIndex
    {σ : Type u} [Fintype σ] (K : Set (σ → ℂ)) (m : ℕ) : Type u :=
  ULift.{u} (Fin (constraintEvaluationHilbertFunction K m))

/-- A basis of the complete homogeneous evaluation range on the constraint set. -/
noncomputable def fullConstraintEvaluationBasis
    {σ : Type u} [Fintype σ] (K : Set (σ → ℂ)) (m : ℕ) :
    Module.Basis (fullConstraintHilbertIndex K m) ℂ
      (LinearMap.range (homogeneousConstraintEvaluation K m)) :=
  (Module.finBasis ℂ _).reindex Equiv.ulift.symm

/-- A homogeneous polynomial lift of one full constraint-Hilbert basis vector. -/
noncomputable def fullConstraintHilbertPivot
    {σ : Type u} [Fintype σ] (K : Set (σ → ℂ)) (m : ℕ)
    (j : fullConstraintHilbertIndex K m) : homogeneousSubmodule σ ℂ m :=
  Classical.choose (fullConstraintEvaluationBasis K m j).2

theorem homogeneousConstraintEvaluation_fullConstraintHilbertPivot
    {σ : Type u} [Fintype σ] (K : Set (σ → ℂ)) (m : ℕ)
    (j : fullConstraintHilbertIndex K m) :
    homogeneousConstraintEvaluation K m (fullConstraintHilbertPivot K m j) =
      (fullConstraintEvaluationBasis K m j).1 :=
  Classical.choose_spec (fullConstraintEvaluationBasis K m j).2

/-- The polynomial lifts of the full Hilbert basis remain independent on the constraint set. -/
theorem fullConstraintHilbertPivot_linearIndependent
    {σ : Type u} [Fintype σ] (K : Set (σ → ℂ)) (m : ℕ) :
    LinearIndependent ℂ (fun j : fullConstraintHilbertIndex K m =>
      fun v : K => eval v.1 (fullConstraintHilbertPivot K m j).1) := by
  have hLI := (fullConstraintEvaluationBasis K m).linearIndependent.map'
    (LinearMap.range (homogeneousConstraintEvaluation K m)).subtype
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  change LinearIndependent ℂ (fun j : fullConstraintHilbertIndex K m =>
    homogeneousConstraintEvaluation K m (fullConstraintHilbertPivot K m j))
  simpa only [homogeneousConstraintEvaluation_fullConstraintHilbertPivot] using hLI

/-- Coordinates of a homogeneous observable in the full constraint-Hilbert basis. -/
noncomputable def fullConstraintHilbertCoefficient
    {σ : Type u} [Fintype σ] (K : Set (σ → ℂ)) (m : ℕ)
    (Q : homogeneousSubmodule σ ℂ m) (j : fullConstraintHilbertIndex K m) : ℂ :=
  (fullConstraintEvaluationBasis K m).repr
    ⟨homogeneousConstraintEvaluation K m Q, ⟨Q, rfl⟩⟩ j

/-- Every homogeneous observable has an exact full-Hilbert expansion at every constraint point. -/
theorem fullConstraintHilbertPivot_spans
    {σ : Type u} [Fintype σ] (K : Set (σ → ℂ)) (m : ℕ)
    (Q : homogeneousSubmodule σ ℂ m) :
    ∀ v : K, eval v.1 Q.1 =
      ∑ j, fullConstraintHilbertCoefficient K m Q j *
        eval v.1 (fullConstraintHilbertPivot K m j).1 := by
  let y : LinearMap.range (homogeneousConstraintEvaluation K m) :=
    ⟨homogeneousConstraintEvaluation K m Q, ⟨Q, rfl⟩⟩
  have hsum := (fullConstraintEvaluationBasis K m).sum_repr y
  have hsum' := congrArg
    (LinearMap.range (homogeneousConstraintEvaluation K m)).subtype hsum
  simp only [map_sum, map_smul] at hsum'
  intro v
  have hv := congrFun hsum' v
  change (homogeneousConstraintEvaluation K m Q) v =
    ∑ j, fullConstraintHilbertCoefficient K m Q j *
      (homogeneousConstraintEvaluation K m (fullConstraintHilbertPivot K m j)) v
  simp_rw [homogeneousConstraintEvaluation_fullConstraintHilbertPivot]
  simpa only [y, fullConstraintHilbertCoefficient, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] using hv.symm

/-- The full constraint-Hilbert pivot presentation in a finite prime-valuation window. -/
noncomputable def fullConstraintHilbertPrimeValuationPresentation
    {d : ℕ} {σ : Type u} [Fintype σ]
    (x : Nat.Primes → σ → ℂ) (K : Set (σ → ℂ)) (hx : CofiniteTailDenseOn x K) :
    PrimeValuationRecurringPivotPresentation d
      (fun r => fullConstraintHilbertIndex K (r + 1))
      (fun r => homogeneousMonomialIndex σ (r + 1)) where
  pivot r j p := eval (x p) (fullConstraintHilbertPivot K (r + 1) j).1
  dependent r q p := eval (x p) (homogeneousMonomial (r + 1) q).1
  coefficient r q j := fullConstraintHilbertCoefficient K (r + 1)
    (homogeneousMonomial (r + 1) q) j
  pivotShiftJetTailIndependent r A _ alpha hdistinct m := by
    apply cofiniteTailDenseOn_primePowerShiftedRotatedJet_tailIndependent
      r x K hx
      (fun j v => eval v (fullConstraintHilbertPivot K (r + 1) j).1)
      (fun j => MvPolynomial.continuous_eval
        (fullConstraintHilbertPivot K (r + 1) j).1)
      (fullConstraintHilbertPivot_linearIndependent K (r + 1))
      alpha hdistinct m
  residualFinite r q := by
    have hzero : ∀ p : Nat.Primes,
        eval (x p) (homogeneousMonomial (r + 1) q).1 -
          ∑ j, fullConstraintHilbertCoefficient K (r + 1)
            (homogeneousMonomial (r + 1) q) j *
              eval (x p) (fullConstraintHilbertPivot K (r + 1) j).1 = 0 := by
      intro p
      have hpK : x p ∈ K := hx.1 ⟨p, rfl⟩
      exact sub_eq_zero.mpr
        (fullConstraintHilbertPivot_spans K (r + 1)
          (homogeneousMonomial (r + 1) q) ⟨x p, hpK⟩)
    simp [hzero]

/-- The complete pivot alphabet has the shift-weighted constraint Hilbert cardinality. -/
theorem fullConstraintHilbert_pivotPalette_card
    {d : ℕ} {σ : Type u} [Fintype σ]
    (K : Set (σ → ℂ)) (A : Fin d → Type u) [∀ r, Fintype (A r)] :
    Fintype.card (Σ r : Fin d, fullConstraintHilbertIndex K (r + 1) × A r) =
      ∑ r : Fin d,
        constraintHomogeneousHilbertFunction K (r + 1) * Fintype.card (A r) := by
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro r _
  rw [Fintype.card_prod, Fintype.card_ulift, Fintype.card_fin,
    constraintEvaluationHilbertFunction_eq_constraintHomogeneousHilbertFunction]

/-- **Compact tail-dense complete relation theorem.** In every finite valuation window, the
prolonged homogeneous coordinate reductions generate the full differential relation ideal. -/
theorem fullConstraintHilbert_complete_relationIdeal_of_cofiniteTailDenseOn
    {d : ℕ} {σ : Type u} [Fintype σ]
    {A : Fin d → Type u}
    [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)]
    (x : Nat.Primes → σ → ℂ) (K : Set (σ → ℂ)) (hx : CofiniteTailDenseOn x K)
    [Nonempty (Σ r : Fin d, fullConstraintHilbertIndex K (r + 1) × A r)]
    (alpha : ∀ r, A r → ℂ)
    (hdistinct : ∀ r, Function.Injective (fun a => (alpha r a).re)) :
    let P := fullConstraintHilbertPrimeValuationPresentation (d := d) x K hx
    GaloisForLFunctions.differentialRelationIdeal
        (C := finitePrimeRationalCoefficientField)
        (Sum.elim (P.pivotPalette alpha) (P.dependentPalette alpha)) =
      differentialPivotRelationIdeal P.paletteMatrix (P.baseCorrection alpha) := by
  dsimp only
  exact (fullConstraintHilbertPrimeValuationPresentation (d := d) x K hx
    |>.complete_relationIdeal alpha hdistinct)

/-- **Compact tail-dense valuation--Hilbert master theorem.** The full homogeneous-coordinate
pivots are a differential transcendence basis of the selected prime-supported carrier field; all
monomial carriers generate the same differential field; and the exact basis size is the
shift-weighted Hilbert-rank sum of the constraint geometry. -/
theorem fullConstraintHilbert_differentialBasis_and_rank_of_cofiniteTailDenseOn
    {d : ℕ} {σ : Type u} [Fintype σ]
    {A : Fin d → Type u}
    [∀ r, Fintype (A r)] [∀ r, DecidableEq (A r)]
    (x : Nat.Primes → σ → ℂ) (K : Set (σ → ℂ)) (hx : CofiniteTailDenseOn x K)
    [Nonempty (Σ r : Fin d, fullConstraintHilbertIndex K (r + 1) × A r)]
    (alpha : ∀ r, A r → ℂ)
    (hdistinct : ∀ r, Function.Injective (fun a => (alpha r a).re)) :
    let P := fullConstraintHilbertPrimeValuationPresentation (d := d) x K hx
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
        (P.pivotPalette alpha) ∧
      GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (Sum.elim (P.pivotPalette alpha) (P.dependentPalette alpha))) =
        GaloisForLFunctions.differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (P.pivotPalette alpha)) ∧
      Fintype.card (Σ r : Fin d, fullConstraintHilbertIndex K (r + 1) × A r) =
        ∑ r : Fin d,
          constraintHomogeneousHilbertFunction K (r + 1) * Fintype.card (A r) := by
  dsimp only
  let P := fullConstraintHilbertPrimeValuationPresentation (d := d) x K hx
  obtain ⟨hind, hadjoin⟩ := P.differentialBasis alpha hdistinct
  exact ⟨hind, hadjoin, fullConstraintHilbert_pivotPalette_card K A⟩

end

end GaloisForLFunctions.HTGeometry
