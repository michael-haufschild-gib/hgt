import GaloisForLFunctions.RHTower.PaperLagCayleyOperator

/-! # Exact arithmetic quotient of the full lag-phase observation family

The quotient norm of every continuous actual-source observable is exactly the
ordinary norm of its recurrent arithmetic model. All compact corrections are
allowed, including operators which mix coordinates. Polynomial phase observations
are faithful in this quotient because distinct primes supply infinitely many roots.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped ENNReal

namespace RHTower.PaperLagCayley

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

theorem modelObservable_compactIdealDistance (f : C(Circle, ℂ)) :
    compactIdealDistance (modelObservable f) = ‖modelObservable f‖ :=
  paperRecurrentDiagonal_compactIdealDistance _ _ _ (recurrent_arithmetic_observable f)

theorem observable_compactIdealDistance (f : C(Circle, ℂ)) :
    compactIdealDistance (observable f) = ‖modelObservable f‖ := by
  calc
    _ = compactIdealDistance (modelObservable f + (observable f - modelObservable f)) := by
      congr 1
      abel
    _ = compactIdealDistance (modelObservable f) :=
      paperCompactIdealDistance_add_compact _ ⟨_, observable_sub_model_compact f⟩
    _ = _ := modelObservable_compactIdealDistance f

theorem model_norm_le_source_sub_compact (f : C(Circle, ℂ))
    (K : compactOperatorStarAlgebra Space) :
    ‖modelObservable f‖ ≤ ‖observable f - K.val‖ := by
  rw [← observable_compactIdealDistance]
  exact compactIdealDistance_le _ _ K.property

theorem observable_compact_iff_model_zero (f : C(Circle, ℂ)) :
    IsCompactOperator (observable f) ↔ modelObservable f = 0 := by
  constructor
  · intro h
    apply norm_eq_zero.1
    rw [← observable_compactIdealDistance]
    exact compactIdealDistance_eq_zero_of_isCompactOperator _ h
  · intro h
    have hcompact := observable_sub_model_compact f
    simpa only [h, sub_zero] using hcompact

theorem modelObservable_zero_iff (f : C(Circle, ℂ)) :
    modelObservable f = 0 ↔ f basePhase = 0 ∧ ∀ p : Nat.Primes, f (primePhase p) = 0 := by
  constructor
  · intro h
    have hval : ∀ n, f (arithmeticPhase n) = 0 := by
      intro n
      have he := congrArg (fun T : Space →L[ℂ] Space => T (lp.single 2 n (1 : ℂ)) n) h
      simpa [modelObservable_apply, lp.single_apply] using he
    exact ⟨by simpa only [arithmeticPhase_compositeIndex] using hval (compositeIndex 0),
      fun p => by simpa only [arithmeticPhase_primeIndex] using hval (primeIndex p 0)⟩
  · rintro ⟨hb, hp⟩
    ext x n
    change f (arithmeticPhase n) * x n = 0
    rcases arithmeticPhase_cases n with h | ⟨p, h⟩
    · rw [h, hb, zero_mul]
    · rw [h, hp p, zero_mul]

/-- Complete continuous-observable vanishing criterion in the compact quotient. -/
theorem observable_compact_iff (f : C(Circle, ℂ)) :
    IsCompactOperator (observable f) ↔
      f basePhase = 0 ∧ ∀ p : Nat.Primes, f (primePhase p) = 0 := by
  rw [observable_compact_iff_model_zero, modelObservable_zero_iff]

theorem compact_observable_vanishes_at_one (f : C(Circle, ℂ))
    (h : IsCompactOperator (observable f)) : f 1 = 0 :=
  observable_one_eq_zero f ((observable_compact_iff f).1 h).2

theorem norm_arithmeticOperator : ‖arithmeticOperator‖ = 1 := by
  have heq : arithmeticOperator = diagonalOperator (fun n => (arithmeticPhase n : ℂ))
      (fun n => (Circle.norm_coe (arithmeticPhase n)).le) := by
    ext x n
    rfl
  rw [heq]
  exact norm_diagonalOperator_eq _ _ (m := 0) (Circle.norm_coe _)

theorem sourceOperator_compactIdealDistance : compactIdealDistance sourceOperator = 1 := by
  rw [sourceOperator, observable_compactIdealDistance]
  exact norm_arithmeticOperator

theorem sourceOperator_ideal_cost : compactOperatorTraceCost Space sourceOperator = ∞ := by
  apply (compactOperatorTraceCost_eq_top_iff _).2
  intro h
  have hz := compactIdealDistance_eq_zero_of_isCompactOperator _ h
  rw [sourceOperator_compactIdealDistance] at hz
  exact one_ne_zero hz

theorem observable_ideal_cost (f : C(Circle, ℂ)) :
    compactOperatorTraceCost Space (observable f) =
      if f basePhase = 0 ∧ ∀ p : Nat.Primes, f (primePhase p) = 0 then 0 else ∞ := by
  classical
  split_ifs with h
  · exact (compactOperatorTraceCost_eq_zero_iff _).2 ((observable_compact_iff f).2 h)
  · exact (compactOperatorTraceCost_eq_top_iff _).2
      (fun hc => h ((observable_compact_iff f).1 hc))

theorem observable_ideal_cost_add_compact (f : C(Circle, ℂ))
    (K : compactOperatorStarAlgebra Space) :
    compactOperatorTraceCost Space (observable f + K.val) =
      if f basePhase = 0 ∧ ∀ p : Nat.Primes, f (primePhase p) = 0 then 0 else ∞ := by
  rw [compactOperatorTraceCost_add_compact, observable_ideal_cost]

def polynomialPhase (P : Polynomial ℂ) : C(Circle, ℂ) :=
  ⟨fun z => P.eval (z : ℂ), P.continuous.comp continuous_subtype_val⟩

theorem polynomial_observable_compact_iff (P : Polynomial ℂ) :
    IsCompactOperator (observable (polynomialPhase P)) ↔ P = 0 := by
  rw [observable_compact_iff]
  constructor
  · intro h
    apply P.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := Set.range fun p : Nat.Primes => (primePhase p : ℂ))
      (t := {z | P.IsRoot z}) ?_ infinite_prime_phases
    rintro z ⟨p, rfl⟩
    exact h.2 p
  · rintro rfl
    simp [polynomialPhase]

theorem polynomial_observable_ideal_cost (P : Polynomial ℂ) :
    compactOperatorTraceCost Space (observable (polynomialPhase P)) =
      if P = 0 then 0 else ∞ := by
  classical
  split_ifs with h
  · exact (compactOperatorTraceCost_eq_zero_iff _).2 ((polynomial_observable_compact_iff P).2 h)
  · exact (compactOperatorTraceCost_eq_top_iff _).2
      (fun hc => h ((polynomial_observable_compact_iff P).1 hc))

end RHTower.PaperLagCayley
