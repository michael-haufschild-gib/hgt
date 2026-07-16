import GaloisForLFunctions.HTGeometry.HankelGuardrailCounterexamples

/-!
# Consequences of the elementary Hankel guardrail counterexamples

This file packages three unconditional failures of tempting finite or ungraded
moment-positivity shortcuts.  It proves that combined shifted positivity does
not recover the two graded sectors, that any finite moment prefix admits an
arbitrarily delayed negative square test, and that cancelling only a zeroth
mass can destroy positivity even when the cutoff moments have a positive
representing measure.
-/

open scoped BigOperators Matrix ComplexConjugate
open MeasureTheory Polynomial

namespace HTGeometry

noncomputable section

/-- Adjacent parity moments add to one. -/
theorem parityMoment_add_succ (n : ℕ) :
    parityMoment n + parityMoment (n + 1) = 1 := by
  rcases n.even_or_odd with hn | hn
  · rcases hn with ⟨k, rfl⟩
    simp [parityMoment]
  · rcases hn with ⟨k, rfl⟩
    have heven : Even (2 * k + 1 + 1) := ⟨k + 1, by omega⟩
    simp [parityMoment, heven]

/-- The constant rank-one matrix with every entry equal to one. -/
def hankelAllOnes (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.of fun _ _ => 1

/-- The all-ones matrix is positive semidefinite at every size. -/
theorem hankelAllOnes_posSemidef (d : ℕ) :
    (hankelAllOnes d).PosSemidef := by
  let B : Matrix (Fin (d + 1)) (Fin 1) ℝ := Matrix.of fun _ _ => 1
  have heq : hankelAllOnes d = B * Bᴴ := by
    ext i j
    simp [hankelAllOnes, B, Matrix.mul_apply]
  rw [heq]
  exact Matrix.posSemidef_self_mul_conjTranspose B

/-- The unshifted and shifted parity blocks sum to the all-ones matrix. -/
theorem parityMoment_combinedHankel_eq (d : ℕ) :
    parityMomentHankel d + parityMomentShiftedHankel d = hankelAllOnes d := by
  ext i j
  simpa [parityMomentHankel, parityMomentShiftedHankel, hankelAllOnes,
    add_assoc] using parityMoment_add_succ ((i : ℕ) + (j : ℕ))

/-- Combined positivity holds although the shifted parity sector is indefinite. -/
theorem parityMoment_combinedHankel_posSemidef (d : ℕ) :
    (parityMomentHankel d + parityMomentShiftedHankel d).PosSemidef := by
  rw [parityMoment_combinedHankel_eq]
  exact hankelAllOnes_posSemidef d

/-- Adjacent terms of the delayed parity sequence also add to one. -/
theorem shiftedParityMoment_add_succ (n : ℕ) :
    shiftedParityMoment n + shiftedParityMoment (n + 1) = 1 := by
  cases n with
  | zero => simp [shiftedParityMoment, parityMoment]
  | succ n =>
      simpa [shiftedParityMoment] using parityMoment_add_succ n

/-- The delayed parity blocks also sum to the all-ones matrix. -/
theorem shiftedParityMoment_combinedHankel_eq (d : ℕ) :
    shiftedParityMomentHankel d + shiftedParityMomentShiftedHankel d =
      hankelAllOnes d := by
  ext i j
  simpa [shiftedParityMomentHankel, shiftedParityMomentShiftedHankel,
    hankelAllOnes, add_assoc] using
      shiftedParityMoment_add_succ ((i : ℕ) + (j : ℕ))

/-- Combined positivity holds although the unshifted delayed-parity sector is indefinite. -/
theorem shiftedParityMoment_combinedHankel_posSemidef (d : ℕ) :
    (shiftedParityMomentHankel d + shiftedParityMomentShiftedHankel d).PosSemidef := by
  rw [shiftedParityMoment_combinedHankel_eq]
  exact hankelAllOnes_posSemidef d

/-- At every nontrivial order, combined positivity can hide either indefinite graded sector. -/
theorem combinedSquareTestPositivity_insufficient (d : ℕ) (hd : 1 ≤ d) :
    (parityMomentHankel d + parityMomentShiftedHankel d).PosSemidef ∧
      (parityMomentHankel d).PosSemidef ∧
      ¬ (parityMomentShiftedHankel d).PosSemidef ∧
      (shiftedParityMomentHankel d + shiftedParityMomentShiftedHankel d).PosSemidef ∧
      ¬ (shiftedParityMomentHankel d).PosSemidef ∧
      (shiftedParityMomentShiftedHankel d).PosSemidef :=
  ⟨parityMoment_combinedHankel_posSemidef d,
    parityMomentHankel_posSemidef' d,
    parityMomentShiftedHankel_not_posSemidef hd,
    shiftedParityMoment_combinedHankel_posSemidef d,
    shiftedParityMomentHankel_not_posSemidef hd,
    shiftedParityMomentShiftedHankel_posSemidef d⟩

/-- A continuation that preserves a prefix but assigns the three moments needed for a delayed
negative square test. -/
def badMomentContinuation (N n : ℕ) (a : Fin (N + 1) → ℝ) : ℕ → ℝ := fun k =>
  if h : k ≤ N then a ⟨k, by omega⟩
  else if k = n then a ⟨0, by omega⟩
  else if k = 2 * n then a ⟨0, by omega⟩ / 4
  else a ⟨0, by omega⟩

theorem badMomentContinuation_prefix (N n : ℕ) (a : Fin (N + 1) → ℝ)
    (k : ℕ) (hk : k ≤ N) :
    badMomentContinuation N n a k = a ⟨k, by omega⟩ := by
  simp [badMomentContinuation, hk]

theorem badMomentContinuation_at_delayed (N n : ℕ) (a : Fin (N + 1) → ℝ)
    (hn : N < n) :
    badMomentContinuation N n a n = a ⟨0, by omega⟩ := by
  have hnle : ¬ n ≤ N := by omega
  simp [badMomentContinuation, hnle]

theorem badMomentContinuation_at_twice_delayed (N n : ℕ)
    (a : Fin (N + 1) → ℝ) (hn : N < n) :
    badMomentContinuation N n a (2 * n) = a ⟨0, by omega⟩ / 4 := by
  have h2nle : ¬ 2 * n ≤ N := by omega
  have h2nne : 2 * n ≠ n := by omega
  simp [badMomentContinuation, h2nle, h2nne]

/-- The delayed polynomial test `1 - 2*X^n` has value `-2*a_0`. -/
theorem badMomentContinuation_delayedSquareTest (N n : ℕ)
    (a : Fin (N + 1) → ℝ) (hn : N < n) :
    badMomentContinuation N n a 0 -
        4 * badMomentContinuation N n a n +
        4 * badMomentContinuation N n a (2 * n) =
      -2 * a ⟨0, by omega⟩ := by
  rw [badMomentContinuation_prefix N n a 0 (by omega),
    badMomentContinuation_at_delayed N n a hn,
    badMomentContinuation_at_twice_delayed N n a hn]
  ring

theorem momentFunctional_one_sub_two_X_pow_square (s : ℕ → ℝ) (n : ℕ) :
    momentFunctional s (((1 : Polynomial ℝ) - (2 : ℝ) • X ^ n) ^ 2) =
      s 0 - 4 * s n + 4 * s (2 * n) := by
  have hpoly : ((1 : Polynomial ℝ) - (2 : ℝ) • X ^ n) ^ 2 =
      X ^ 0 + (-4 : ℝ) • X ^ n + (4 : ℝ) • X ^ (2 * n) := by
    norm_num [Polynomial.smul_eq_C_mul, Polynomial.C_ofNat]
    ring
  rw [hpoly]
  simp only [momentFunctional_add, momentFunctional_smul, momentFunctional_X_pow]
  ring

/-- No positive measure can represent the delayed bad continuation. -/
theorem badMomentContinuation_not_momentSequence (N n : ℕ)
    (a : Fin (N + 1) → ℝ) (ha0 : 0 < a ⟨0, by omega⟩) (hn : N < n) :
    ¬ ∃ μ : Measure ℝ,
      (∀ k, badMomentContinuation N n a k = ∫ x, x ^ k ∂μ) ∧
      (∀ k, Integrable (fun x : ℝ => x ^ k) μ) := by
  rintro ⟨mu, hs, hint⟩
  have hnonneg := momentFunctional_pow_two_nonneg
    (badMomentContinuation N n a) hs hint
      ((1 : Polynomial ℝ) - (2 : ℝ) • X ^ n)
  rw [momentFunctional_one_sub_two_X_pow_square,
    badMomentContinuation_delayedSquareTest N n a hn] at hnonneg
  linarith

/-- Any finite real prefix with positive initial term admits a continuation that agrees with the
prefix but fails a square test beyond any prescribed later index. -/
theorem exists_continuation_preserving_prefix_not_momentSequence
    (N n : ℕ) (a : Fin (N + 1) → ℝ) (ha0 : 0 < a ⟨0, by omega⟩) (hn : N < n) :
    ∃ b : ℕ → ℝ,
      (∀ k (hk : k ≤ N), b k = a ⟨k, by omega⟩) ∧
      ¬ ∃ μ : Measure ℝ,
        (∀ k, b k = ∫ x, x ^ k ∂μ) ∧
        (∀ k, Integrable (fun x : ℝ => x ^ k) μ) := by
  exact ⟨badMomentContinuation N n a,
    badMomentContinuation_prefix N n a,
    badMomentContinuation_not_momentSequence N n a ha0 hn⟩

/-- Moments after discarding only the zeroth moment of `delta_1`. -/
def poleCancelledMoment : ℕ → ℝ
  | 0 => 0
  | _ + 1 => 1

/-- The cutoff moments of `L * delta_0 + delta_1`. -/
def poleCutoffMoment (L : ℝ) : ℕ → ℝ
  | 0 => L + 1
  | _ + 1 => 1

/-- The positive cutoff measure whose zeroth mass is later cancelled. -/
def poleCutoffMeasure (L : ℝ) : Measure ℝ :=
  ENNReal.ofReal L • Measure.dirac 0 + Measure.dirac 1

theorem poleCutoffMoment_integrable (L : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (poleCutoffMeasure L) := by
  rw [poleCutoffMeasure, MeasureTheory.integrable_add_measure]
  constructor
  · exact (MeasureTheory.integrable_dirac (by simp)).smul_measure (by simp)
  · exact MeasureTheory.integrable_dirac (by simp)

theorem poleCutoffMoment_eq_integral (L : ℝ) (hL : 0 ≤ L) (n : ℕ) :
    poleCutoffMoment L n = ∫ x, x ^ n ∂poleCutoffMeasure L := by
  have hzero : Integrable (fun x : ℝ => x ^ n)
      (ENNReal.ofReal L • Measure.dirac 0) :=
    (MeasureTheory.integrable_dirac (by simp)).smul_measure (by simp)
  have hone : Integrable (fun x : ℝ => x ^ n) (Measure.dirac 1) :=
    MeasureTheory.integrable_dirac (by simp)
  rw [poleCutoffMeasure, MeasureTheory.integral_add_measure hzero hone]
  cases n with
  | zero => simp [poleCutoffMoment, hL]
  | succ n => simp [poleCutoffMoment]

theorem poleCancelledMoment_values :
    poleCancelledMoment 0 = 0 ∧ poleCancelledMoment 1 = 1 ∧
      poleCancelledMoment 2 = 1 := by
  simp [poleCancelledMoment]

theorem momentFunctional_one_sub_X_square (s : ℕ → ℝ) :
    momentFunctional s (((1 : Polynomial ℝ) - X) ^ 2) =
      s 0 - 2 * s 1 + s 2 := by
  have hpoly : ((1 : Polynomial ℝ) - X) ^ 2 =
      X ^ 0 + (-2 : ℝ) • X ^ 1 + X ^ 2 := by
    norm_num [Polynomial.smul_eq_C_mul, Polynomial.C_ofNat]
    ring
  rw [hpoly]
  simp only [momentFunctional_add, momentFunctional_smul, momentFunctional_X_pow]
  ring

/-- Removing only the divergent zeroth moment leaves a negative square test. -/
theorem poleCancelledMoment_one_sub_X_square :
    momentFunctional poleCancelledMoment (((1 : Polynomial ℝ) - X) ^ 2) = -1 := by
  rw [momentFunctional_one_sub_X_square]
  norm_num [poleCancelledMoment]

/-- The pole-cancelled sequence is not represented by any positive measure. -/
theorem poleCancelledMoment_not_momentSequence :
    ¬ ∃ μ : Measure ℝ,
      (∀ k, poleCancelledMoment k = ∫ x, x ^ k ∂μ) ∧
      (∀ k, Integrable (fun x : ℝ => x ^ k) μ) := by
  rintro ⟨mu, hs, hint⟩
  have hnonneg := momentFunctional_pow_two_nonneg poleCancelledMoment hs hint
    ((1 : Polynomial ℝ) - X)
  rw [poleCancelledMoment_one_sub_X_square] at hnonneg
  norm_num at hnonneg

/-- A positive cutoff moment sequence can lose moment positivity when only its zeroth mass is
cancelled. -/
theorem poleCancellation_can_destroy_momentPositivity (L : ℝ) (hL : 0 ≤ L) :
    (∃ μ : Measure ℝ,
        (∀ k, poleCutoffMoment L k = ∫ x, x ^ k ∂μ) ∧
        (∀ k, Integrable (fun x : ℝ => x ^ k) μ)) ∧
      poleCancelledMoment 0 = 0 ∧
      (∀ k, poleCancelledMoment (k + 1) = poleCutoffMoment L (k + 1)) ∧
      ¬ ∃ μ : Measure ℝ,
        (∀ k, poleCancelledMoment k = ∫ x, x ^ k ∂μ) ∧
        (∀ k, Integrable (fun x : ℝ => x ^ k) μ) := by
  exact ⟨⟨poleCutoffMeasure L, poleCutoffMoment_eq_integral L hL,
      poleCutoffMoment_integrable L⟩,
    rfl, fun k => by simp [poleCancelledMoment, poleCutoffMoment],
    poleCancelledMoment_not_momentSequence⟩

end

end HTGeometry
