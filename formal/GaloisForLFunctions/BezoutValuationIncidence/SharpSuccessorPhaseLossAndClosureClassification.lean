import GaloisForLFunctions.BezoutValuationIncidence.OptimalSuccessorPredictionAndExactPhaseLoss
import GaloisForLFunctions.BezoutValuationIncidence.SixModeStabilityAndSharpQuarterDecorrelation

/-!
# Sharp arithmetic phase loss and exact successor closure

At every level, the best one-step prediction loses between three quarters and
all variance above parity. Equality at the lower endpoint permits exactly modes
3 and 6; equality at the upper endpoint erases every squarefree mode above 2.
Both constants are sharp. Exact divisor-sieve closure under succession occurs
precisely for raw weights supported on the constant and parity divisors.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section

/-- Variance outside the constant and parity components. -/
def sieveVarianceAboveParity (N : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Icc 3 N, (q.totient : ℝ) * (selbergMultiplesCoord N c q)^2

private theorem above_parity_nonneg (N : ℕ) (c : ℕ → ℝ) :
    0 ≤ sieveVarianceAboveParity N c :=
  sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

/-- Constant and parity have exactly zero one-step loss, uniformly at all sieve levels. -/
theorem successorPhaseLoss_eq_above_parity (N : ℕ) (c : ℕ → ℝ) :
    successorPhaseLoss N c =
      ∑ q ∈ Icc 3 N, ((q.totient : ℝ) - (moebiusReal q)^2 / (q.totient : ℝ)) *
        (selbergMultiplesCoord N c q)^2 := by
  unfold successorPhaseLoss
  symm
  apply sum_subset
  · intro q hq
    exact mem_Icc.mpr ⟨by have := (mem_Icc.mp hq).1; omega, (mem_Icc.mp hq).2⟩
  · intro q hq hn
    have hq12 : q = 1 ∨ q = 2 := by simp only [mem_Icc] at hq hn; omega
    rcases hq12 with rfl | rfl <;>
      norm_num [moebiusReal, moebius_apply_prime Nat.prime_two]

private theorem phase_totient_ge_two {q : ℕ} (hq : 3 ≤ q) : (2 : ℝ) ≤ q.totient := by
  have hp := Nat.totient_pos.mpr (show 0 < q by omega)
  have hd := even_iff_two_dvd.mp (Nat.totient_even hq)
  exact_mod_cast Nat.le_of_dvd hp hd

private theorem phase_weight_bounds {q : ℕ} (hq : 3 ≤ q) :
    (3 / 4 : ℝ) * q.totient ≤ (q.totient : ℝ) - (moebiusReal q)^2 / q.totient ∧
      (q.totient : ℝ) - (moebiusReal q)^2 / q.totient ≤ q.totient := by
  have ht := phase_totient_ge_two hq
  have hp : (0 : ℝ) < q.totient := by linarith
  have hm := (moebiusReal_le_one q).1
  have hdiv : (moebiusReal q)^2 / q.totient ≤ (q.totient : ℝ) / 4 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [sq_nonneg ((q.totient : ℝ) - 2)]
  have hn := div_nonneg (sq_nonneg (moebiusReal q)) hp.le
  constructor <;> linarith

private theorem phase_small_values :
    Nat.totient 4 = 2 ∧ moebiusReal 4 = 0 ∧ Nat.totient 6 = 2 ∧ moebiusReal 6 = 1 := by
  obtain ⟨h4, h6, hm4, hm6⟩ := wall11_totient_degeneracy_broken_by_bezout
  rw [h4] at hm4
  rw [h6] at hm6
  refine ⟨h4, ?_, h6, ?_⟩ <;> norm_num at hm4 hm6 ⊢ <;> linarith

private theorem phase_weight_lower_eq_iff {q : ℕ} (hq : 3 ≤ q) :
    (q.totient : ℝ) - (moebiusReal q)^2 / q.totient = (3 / 4 : ℝ) * q.totient ↔
      q = 3 ∨ q = 6 := by
  constructor
  · intro h
    have ht := phase_totient_ge_two hq
    have hp : (q.totient : ℝ) ≠ 0 := by linarith
    have hm := (moebiusReal_le_one q).1
    have hh := h
    field_simp at hh
    have ht2 : (q.totient : ℝ) ≤ 2 := by nlinarith
    have hn : q.totient ≤ 2 := by exact_mod_cast ht2
    rcases (GaloisForLFunctions.HTGeometry.totient_le_two_iff (by omega)).mp hn with
      h1 | h2 | h3 | h4 | h6
    · omega
    · omega
    · exact Or.inl h3
    · subst q
      rw [phase_small_values.1, phase_small_values.2.1] at h
      norm_num at h
    · exact Or.inr h6
  · rintro (rfl | rfl)
    · norm_num [Nat.totient_prime Nat.prime_three, moebiusReal, moebius_apply_prime Nat.prime_three]
    · rw [phase_small_values.2.2.1, phase_small_values.2.2.2]
      norm_num

/-- Sharp universal phase-loss interval above parity. -/
theorem successorPhaseLoss_bounds (N : ℕ) (c : ℕ → ℝ) :
    (3 / 4 : ℝ) * sieveVarianceAboveParity N c ≤ successorPhaseLoss N c ∧
      successorPhaseLoss N c ≤ sieveVarianceAboveParity N c := by
  rw [successorPhaseLoss_eq_above_parity]
  unfold sieveVarianceAboveParity
  rw [mul_sum]
  constructor
  · apply sum_le_sum
    intro q hq
    have h := mul_le_mul_of_nonneg_right (phase_weight_bounds (mem_Icc.mp hq).1).1
      (sq_nonneg (selbergMultiplesCoord N c q))
    simpa only [mul_assoc] using h
  · apply sum_le_sum
    intro q hq
    exact mul_le_mul_of_nonneg_right (phase_weight_bounds (mem_Icc.mp hq).1).2 (sq_nonneg _)

/-- Minimum phase loss occurs exactly on the two arithmetic modes 3 and 6 above parity. -/
theorem successorPhaseLoss_lower_eq_iff (N : ℕ) (c : ℕ → ℝ) :
    successorPhaseLoss N c = (3 / 4 : ℝ) * sieveVarianceAboveParity N c ↔
      ∀ q ∈ Icc 3 N, q ≠ 3 → q ≠ 6 → selbergMultiplesCoord N c q = 0 := by
  have he : successorPhaseLoss N c - (3 / 4 : ℝ) * sieveVarianceAboveParity N c =
      ∑ q ∈ Icc 3 N, ((q.totient : ℝ) - (moebiusReal q)^2 / q.totient -
        (3 / 4 : ℝ) * q.totient) * (selbergMultiplesCoord N c q)^2 := by
    rw [successorPhaseLoss_eq_above_parity, sieveVarianceAboveParity, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro q _
    ring
  rw [← sub_eq_zero, he, sum_eq_zero_iff_of_nonneg (fun q hq =>
    mul_nonneg (sub_nonneg.mpr (phase_weight_bounds (mem_Icc.mp hq).1).1) (sq_nonneg _))]
  constructor
  · intro h q hq h3 h6
    have hn : (q.totient : ℝ) - (moebiusReal q)^2 / q.totient - (3 / 4 : ℝ) * q.totient ≠ 0 := by
      intro hz
      exact (phase_weight_lower_eq_iff (mem_Icc.mp hq).1).mp (sub_eq_zero.mp hz) |>.elim h3 h6
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp (h q hq)).resolve_left hn)
  · intro h q hq
    by_cases h3 : q = 3
    · rw [(phase_weight_lower_eq_iff (mem_Icc.mp hq).1).mpr (Or.inl h3)]
      ring
    by_cases h6 : q = 6
    · rw [(phase_weight_lower_eq_iff (mem_Icc.mp hq).1).mpr (Or.inr h6)]
      ring
    rw [h q hq h3 h6]
    ring

/-- Total phase loss above parity occurs exactly when its squarefree coordinates vanish. -/
theorem successorPhaseLoss_upper_eq_iff (N : ℕ) (c : ℕ → ℝ) :
    successorPhaseLoss N c = sieveVarianceAboveParity N c ↔
      ∀ q ∈ Icc 3 N, Squarefree q → selbergMultiplesCoord N c q = 0 := by
  have he : sieveVarianceAboveParity N c - successorPhaseLoss N c =
      ∑ q ∈ Icc 3 N, ((moebiusReal q)^2 / q.totient) * (selbergMultiplesCoord N c q)^2 := by
    rw [successorPhaseLoss_eq_above_parity, sieveVarianceAboveParity, ← sum_sub_distrib]
    apply sum_congr rfl
    intro q _
    ring
  rw [eq_comm, ← sub_eq_zero, he, sum_eq_zero_iff_of_nonneg (fun q _ =>
    mul_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _))]
  constructor
  · intro h q hq hs
    have hm : moebiusReal q ≠ 0 := by
      change (μ q : ℝ) ≠ 0
      exact_mod_cast moebius_ne_zero_iff_squarefree.mpr hs
    have ht : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr (by have := (mem_Icc.mp hq).1; omega)).ne'
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp (h q hq)).resolve_left (div_ne_zero (pow_ne_zero _ hm) ht))
  · intro h q hq
    by_cases hs : Squarefree q
    · rw [h q hq hs]
      ring
    · simp [moebiusReal, moebius_eq_zero_of_not_squarefree hs]

/-- Zero irreducible loss is exactly the raw constant-plus-parity subspace. -/
theorem successorPhaseLoss_eq_zero_iff (N : ℕ) (c : ℕ → ℝ) :
    successorPhaseLoss N c = 0 ↔ ∀ d ∈ Icc 3 N, c d = 0 := by
  rw [successorPhaseLoss_eq_above_parity]
  have hp : ∀ q ∈ Icc 3 N,
      0 < (q.totient : ℝ) - (moebiusReal q)^2 / q.totient := by
    intro q hq
    have ht := phase_totient_ge_two (mem_Icc.mp hq).1
    have h := (phase_weight_bounds (mem_Icc.mp hq).1).1
    linarith
  rw [sum_eq_zero_iff_of_nonneg (fun q hq => mul_nonneg (hp q hq).le (sq_nonneg _))]
  have hz : (∀ q ∈ Icc 3 N,
      ((q.totient : ℝ) - (moebiusReal q)^2 / q.totient) * (selbergMultiplesCoord N c q)^2 = 0) ↔
      ∀ q ∈ Icc 3 N, selbergMultiplesCoord N c q = 0 := by
    constructor
    · intro h q hq
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp (h q hq)).resolve_left (hp q hq).ne')
    · intro h q hq
      rw [h q hq]
      ring
  exact hz.trans (selbergMultiplesCoord_tail_zero_iff N 2 c)

/-- Exact closure obstruction and positive survivor for the actual integer successor. -/
theorem sieve_successor_representable_iff (N : ℕ) (c : ℕ → ℝ) :
    (∃ b, ∀ k, sieveSeq N c (k + 1) = sieveSeq N b k) ↔
      ∀ d ∈ Icc 3 N, c d = 0 := by
  constructor
  · rintro ⟨b, hb⟩
    have hz := (successorPredictionError_eq_zero_iff N c b).mpr hb
    have hm := successorPredictionError_minimal N c b
    rw [successorPredictionError_optimal_value, hz] at hm
    have hl := (successorPhaseLoss_bounds N c).1
    have hn := above_parity_nonneg N c
    exact (successorPhaseLoss_eq_zero_iff N c).mp (by linarith)
  · intro hc
    refine ⟨sieveSuccessorPredictor N c, (successorPredictionError_eq_zero_iff N c _).mp ?_⟩
    rw [successorPredictionError_optimal_value, (successorPhaseLoss_eq_zero_iff N c).mpr hc]

private theorem phase_pure_mode (m : ℕ) (hm : 3 ≤ m) :
    let c := pmRamanujanResidueCoeff (fun q => if q = m then (1 : ℝ) else 0) m
    sieveVarianceAboveParity m c = m.totient ∧
      successorPhaseLoss m c = (m.totient : ℝ) - (moebiusReal m)^2 / m.totient := by
  dsimp only
  have hi : m ∈ Icc 3 m := mem_Icc.mpr ⟨hm, le_rfl⟩
  have hi1 : m ∈ Icc 1 m := mem_Icc.mpr ⟨by omega, le_rfl⟩
  rw [successorPhaseLoss_eq_above_parity]
  constructor
  · unfold sieveVarianceAboveParity
    rw [sum_eq_single m]
    · simp [selbergMultiplesCoord_ramanujan_inverse, hi1]
    · intro q _ hq
      simp [selbergMultiplesCoord_ramanujan_inverse, hq]
    · exact fun h => (h hi).elim
  · rw [sum_eq_single m]
    · simp [selbergMultiplesCoord_ramanujan_inverse, hi1]
    · intro q _ hq
      simp [selbergMultiplesCoord_ramanujan_inverse, hq]
    · exact fun h => (h hi).elim

/-- Complete classification of all uniform lower phase-loss constants. -/
theorem universal_successor_phase_loss_lower_iff (A : ℝ) :
    (∀ N c, A * sieveVarianceAboveParity N c ≤ successorPhaseLoss N c) ↔ A ≤ 3 / 4 := by
  constructor
  · intro h
    have hv := phase_pure_mode 3 (by omega)
    dsimp only at hv
    have hh := h 3 (pmRamanujanResidueCoeff (fun q => if q = 3 then (1 : ℝ) else 0) 3)
    rw [hv.1, hv.2] at hh
    norm_num [Nat.totient_prime Nat.prime_three, moebiusReal, moebius_apply_prime Nat.prime_three] at hh
    linarith
  · intro h N c
    exact (mul_le_mul_of_nonneg_right h (above_parity_nonneg N c)).trans (successorPhaseLoss_bounds N c).1

/-- Complete classification of all uniform upper phase-loss constants. -/
theorem universal_successor_phase_loss_upper_iff (A : ℝ) :
    (∀ N c, successorPhaseLoss N c ≤ A * sieveVarianceAboveParity N c) ↔ 1 ≤ A := by
  constructor
  · intro h
    have hv := phase_pure_mode 4 (by omega)
    dsimp only at hv
    have hh := h 4 (pmRamanujanResidueCoeff (fun q => if q = 4 then (1 : ℝ) else 0) 4)
    rw [hv.1, hv.2, phase_small_values.1, phase_small_values.2.1] at hh
    norm_num at hh
    linarith
  · intro h N c
    have hh := mul_le_mul_of_nonneg_right h (above_parity_nonneg N c)
    rw [one_mul] at hh
    exact (successorPhaseLoss_bounds N c).2.trans hh

end
end GaloisForLFunctions.BezoutValuationIncidence
