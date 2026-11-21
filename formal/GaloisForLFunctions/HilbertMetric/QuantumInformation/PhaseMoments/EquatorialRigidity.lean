import Mathlib.Analysis.Convex.Mul
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Diagonal rigidity of symmetric product mixtures

Two endpoint second differences of the group-weight profile detect the
equatorial restriction in Qian and Zhang (arXiv:2611.24473, Theorem 4(b)).
Their sum is a weighted squared imbalance and controls even approximately
flat profiles. The levels may include unnormalized local amplitudes.
-/

open scoped BigOperators NNReal

namespace GaloisForLFunctions.HilbertMetric.PhaseMoments

variable {ι : Type*} [Fintype ι]

/-- Diagonal coefficient for a block with s zero bits and t one bits. -/
def productDiagonal (p a b : ι → ℝ≥0) (s t : ℕ) : ℝ :=
  ∑ i, (p i : ℝ) * (a i : ℝ) ^ s * (b i : ℝ) ^ t

/-- The second difference along a fixed total Hamming weight profile is
a sum of squared local imbalances. -/
theorem productDiagonal_secondDifference (p a b : ι → ℝ≥0) (s t : ℕ) :
    productDiagonal p a b (s + 2) t - 2 * productDiagonal p a b (s + 1) (t + 1) +
        productDiagonal p a b s (t + 2) =
      ∑ i, (p i : ℝ) * (a i : ℝ) ^ s * (b i : ℝ) ^ t * ((a i : ℝ) - b i) ^ 2 := by
  simp only [productDiagonal, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pow_succ]
  ring

/-- Combined curvature at the two ends of a block of size m + 2. -/
def endpointCurvature (p a b : ι → ℝ≥0) (m : ℕ) : ℝ :=
  (productDiagonal p a b (m + 2) 0 - 2 * productDiagonal p a b (m + 1) 1 +
    productDiagonal p a b m 2) +
  (productDiagonal p a b 2 m - 2 * productDiagonal p a b 1 (m + 1) +
    productDiagonal p a b 0 (m + 2))

theorem endpointCurvature_eq_sum (p a b : ι → ℝ≥0) (m : ℕ) :
    endpointCurvature p a b m =
      ∑ i, (p i : ℝ) * ((a i : ℝ) ^ m + (b i : ℝ) ^ m) * ((a i : ℝ) - b i) ^ 2 := by
  unfold endpointCurvature
  rw [productDiagonal_secondDifference p a b m 0, productDiagonal_secondDifference p a b 0 m,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pow_zero, mul_one]
  ring

/-- The curvature detects every positive-weight atom, including atoms
whose amplitude on one of the two levels vanishes. -/
theorem endpointCurvature_eq_zero_iff (p a b : ι → ℝ≥0) (m : ℕ) :
    endpointCurvature p a b m = 0 ↔ ∀ i, 0 < p i → a i = b i := by
  rw [endpointCurvature_eq_sum]
  constructor
  · intro h i hi
    have ht := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => show 0 ≤ (p j : ℝ) * ((a j : ℝ) ^ m + (b j : ℝ) ^ m) *
        ((a j : ℝ) - b j) ^ 2 by positivity)).mp h i (Finset.mem_univ _)
    have hp : 0 < (p i : ℝ) := hi
    by_contra hab
    have hab' : (a i : ℝ) ≠ b i := fun he => hab (Subtype.ext he)
    have hpow : 0 < (a i : ℝ) ^ m + (b i : ℝ) ^ m := by
      rcases lt_or_gt_of_ne hab' with hl | hr
      · have hb : 0 < (b i : ℝ) := (a i).coe_nonneg.trans_lt hl
        exact add_pos_of_nonneg_of_pos (by positivity) (pow_pos hb _)
      · have ha : 0 < (a i : ℝ) := (b i).coe_nonneg.trans_lt hr
        exact add_pos_of_pos_of_nonneg (pow_pos ha _) (by positivity)
    exact (mul_pos (mul_pos hp hpow) (sq_pos_of_ne_zero (sub_ne_zero.mpr hab'))).ne' ht
  · intro h
    apply Finset.sum_eq_zero
    intro i _
    rcases eq_or_lt_of_le (show 0 ≤ p i from bot_le) with hp | hp
    · simp [← hp]
    · simp [h i hp]

/-- Exact converse to constant diagonals on a symmetric block with at least two sites. -/
theorem productDiagonal_flat_iff (p a b : ι → ℝ≥0) (m : ℕ) :
    (∀ s t, s + t = m + 2 → productDiagonal p a b s t = productDiagonal p a b (m + 2) 0) ↔
      ∀ i, 0 < p i → a i = b i := by
  constructor
  · intro h
    apply (endpointCurvature_eq_zero_iff p a b m).mp
    unfold endpointCurvature
    rw [h (m + 1) 1 (by omega), h m 2 (by omega), h 2 m (by omega),
      h 1 (m + 1) (by omega), h 0 (m + 2) (by omega)]
    ring
  · intro h s t hst
    unfold productDiagonal
    apply Finset.sum_congr rfl
    intro i _
    rcases eq_or_lt_of_le (show 0 ≤ p i from bot_le) with hp | hp
    · simp [← hp]
    · rw [h i hp, mul_assoc, ← pow_add, hst, pow_zero, mul_one]

private theorem midpoint_pow_le (a b : ℝ≥0) (m : ℕ) :
    2 * (((a : ℝ) + b) / 2) ^ m ≤ (a : ℝ) ^ m + (b : ℝ) ^ m := by
  have hh : (0 : ℝ) ≤ 1 / 2 := by positivity
  have hc := (convexOn_pow (𝕜 := ℝ) m).2 (Set.mem_Ici.mpr a.coe_nonneg)
    (Set.mem_Ici.mpr b.coe_nonneg) hh hh (by linarith)
  simp only [smul_eq_mul,
    show (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b = ((a : ℝ) + b) / 2 by ring] at hc
  linarith only [hc]

/-- A mass-sensitive lower bound on the squared imbalance from just the
two endpoint differences. For normalized levels the coefficient is
the constant 2 * (1/2)^m on every atom. -/
theorem weighted_imbalance_le_endpointCurvature (p a b : ι → ℝ≥0) (m : ℕ) :
    (∑ i, (p i : ℝ) * (2 * (((a i : ℝ) + b i) / 2) ^ m) * ((a i : ℝ) - b i) ^ 2) ≤
      endpointCurvature p a b m := by
  rw [endpointCurvature_eq_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (midpoint_pow_le (a i) (b i) m) (p i).coe_nonneg)
      (sq_nonneg _)

#print axioms productDiagonal_secondDifference
#print axioms productDiagonal_flat_iff
#print axioms weighted_imbalance_le_endpointCurvature

end GaloisForLFunctions.HilbertMetric.PhaseMoments
