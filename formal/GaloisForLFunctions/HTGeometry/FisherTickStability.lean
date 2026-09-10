import GaloisForLFunctions.HTGeometry.QuantumBilinearNullActivation

/-!
# Distinguishability-per-tick stability and its stationary boundary

The empirical version of arXiv:2605.03958, equations (47)--(48), for arbitrary
finite frequency schedules. Extended nonnegative reciprocals represent
infinite stability correctly. Perfect stability means constant absolute
frequency, which includes stationary schedules and schedules with reversals.
-/
open scoped BigOperators ENNReal
noncomputable section
namespace HTGeometry

/-- Average Fisher distance per unit-duration qubit tick. -/
def fisherTickMean {n : ℕ} (frequency : Fin (n + 1) → ℝ) : ℝ :=
  (∑ i, |frequency i|) / (n + 1)

/-- Empirical variance of the actual distinguishability rates. -/
def fisherTickVariance {n : ℕ} (frequency : Fin (n + 1) → ℝ) : ℝ :=
  (∑ i, (|frequency i| - fisherTickMean frequency) ^ 2) / (n + 1)

/-- Extended stability; zero variance has value infinity. -/
def fisherTickStability {n : ℕ} (frequency : Fin (n + 1) → ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (fisherTickVariance frequency))⁻¹

theorem fisherTickVariance_nonneg {n : ℕ} (frequency : Fin (n + 1) → ℝ) :
    0 ≤ fisherTickVariance frequency := by
  unfold fisherTickVariance
  positivity

theorem fisherTickVariance_zero_iff_mean {n : ℕ} (frequency : Fin (n + 1) → ℝ) :
    fisherTickVariance frequency = 0 ↔ ∀ i, |frequency i| = fisherTickMean frequency := by
  rw [fisherTickVariance, div_eq_zero_iff]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [or_iff_left hn, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)]
  simp only [Finset.mem_univ, forall_const, sq_eq_zero_iff, sub_eq_zero]

/-- Perfect stability is exactly equality of all absolute frequencies. -/
theorem fisherTickVariance_zero_iff {n : ℕ} (frequency : Fin (n + 1) → ℝ) :
    fisherTickVariance frequency = 0 ↔ ∀ i j, |frequency i| = |frequency j| := by
  rw [fisherTickVariance_zero_iff_mean]
  constructor
  · intro h i j
    exact (h i).trans (h j).symm
  · intro h i
    unfold fisherTickMean
    have hs : (∑ j, |frequency j|) = (n + 1) * |frequency i| := by
      calc
        (∑ j, |frequency j|) = ∑ _j : Fin (n + 1), |frequency i| :=
          Finset.sum_congr rfl (fun j _ => h j i)
        _ = (n + 1) * |frequency i| := by simp
    rw [hs]
    field_simp

/-- Finite schedules need no variance or positivity assumptions in the stability classification. -/
theorem fisherTickStability_eq_top_iff {n : ℕ} (frequency : Fin (n + 1) → ℝ) :
    fisherTickStability frequency = ⊤ ↔ ∀ i j, |frequency i| = |frequency j| := by
  rw [fisherTickStability, ENNReal.inv_eq_top, ENNReal.ofReal_eq_zero]
  constructor
  · intro h
    exact (fisherTickVariance_zero_iff frequency).mp
      (le_antisymm h (fisherTickVariance_nonneg frequency))
  · intro h
    exact ((fisherTickVariance_zero_iff frequency).mpr h).le

/-- Independently reversing any ticks leaves distinguishability variance unchanged. -/
theorem fisherTickVariance_reverse {n : ℕ} (frequency : Fin (n + 1) → ℝ)
    (reverse : Fin (n + 1) → Bool) :
    fisherTickVariance (fun i => if reverse i then -frequency i else frequency i) =
      fisherTickVariance frequency := by
  have he : ∀ i, |if reverse i then -frequency i else frequency i| = |frequency i| := by
    intro i
    split <;> simp
  simp only [fisherTickVariance, fisherTickMean, he]

/-- Zero-motion clocks receive infinite regularity under the variance-only criterion. -/
theorem fisherTickStability_stationary (n : ℕ) :
    fisherTickStability (fun _ : Fin (n + 1) => (0 : ℝ)) = ⊤ ∧
      fisherTickMean (fun _ : Fin (n + 1) => (0 : ℝ)) = 0 := by
  constructor
  · exact (fisherTickStability_eq_top_iff _).mpr (by intros; rfl)
  · simp [fisherTickMean]

/-- With ordinary real division, the published reciprocal gives zero at a perfectly regular clock. -/
theorem fisherTick_real_reciprocal_constant (n : ℕ) (frequency : ℝ) :
    (fisherTickVariance (fun _ : Fin (n + 1) => frequency))⁻¹ = 0 := by
  rw [(fisherTickVariance_zero_iff _).mpr (by intros; rfl), inv_zero]

/-- A finite clock has positive average distinguishability exactly when some tick moves. -/
theorem fisherTickMean_pos_iff {n : ℕ} (frequency : Fin (n + 1) → ℝ) :
    0 < fisherTickMean frequency ↔ ∃ i, frequency i ≠ 0 := by
  rw [fisherTickMean, div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < n + 1)]
  rw [Finset.sum_pos_iff_of_nonneg (fun i _ => abs_nonneg _)]
  simp only [Finset.mem_univ, true_and, abs_pos]

end HTGeometry
