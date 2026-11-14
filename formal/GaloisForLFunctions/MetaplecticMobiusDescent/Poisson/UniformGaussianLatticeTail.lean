import GaloisForLFunctions.TransThresholdPairCorrelation.CosineTransformLogarithmicTransport
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Uniform decay on the punctured Gaussian lattice

A telescoping reciprocal-square envelope controls a positive integer ray at
both the inverse-scale and inverse-square-scale rates. Separating the two
coordinates then bounds the fourth-order planar decay kernel uniformly after
multiplication by the squared scale. Removing the origin is essential.
-/

noncomputable section
open scoped Classical
open Finset Filter

namespace GaloisForLFunctions.MetaplecticMobiusDescent.QuarticPoisson

/-- A strictly positive lattice frequency scale. -/
abbrev PositiveScale := {s : ℝ // 0 < s}

private def natTailTerm (s : PositiveScale) (n : ℕ) : ℝ :=
  1 / (1 + s.val * ((n : ℝ) + 1)) ^ 2

/-- Mass of the positive reciprocal-square ray. -/
def positiveTail (s : PositiveScale) : ℝ := ∑' n : ℕ, natTailTerm s n

private theorem summable_natTailTerm (s : PositiveScale) : Summable (natTailTerm s) := by
  apply summable_of_sum_range_le (fun n => by unfold natTailTerm; positivity)
  intro N
  exact TransThresholdPairCorrelation.sum_inverse_square_affine_le s.property N

/-- The positive ray is bounded by the reciprocal scale. -/
theorem positiveTail_le_inv (s : PositiveScale) : positiveTail s ≤ 1 / s.val :=
  le_of_tendsto (summable_natTailTerm s).hasSum.tendsto_sum_nat
    (Eventually.of_forall (fun N =>
      TransThresholdPairCorrelation.sum_inverse_square_affine_le s.property N))

private theorem reciprocal_nat_square_bound :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) ∧
      (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) ≤ 2 := by
  let u : PositiveScale := ⟨1, zero_lt_one⟩
  let g : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) ^ 2
  have hshift : (fun n => g (n + 1)) = natTailTerm u := by
    funext n
    simp [g, natTailTerm, u, add_comm, add_left_comm]
  have hg : Summable g := (summable_nat_add_iff 1).mp (hshift.symm ▸ summable_natTailTerm u)
  refine ⟨hg, ?_⟩
  have hsum := hg.sum_add_tsum_nat_add 1
  rw [hshift] at hsum
  have hb := positiveTail_le_inv u
  change positiveTail u ≤ 1 / 1 at hb
  simp only [g, sum_range_one, Nat.cast_zero, zero_add, one_pow, div_one] at hsum
  change 1 + positiveTail u = ∑' n, g n at hsum
  change (∑' n, g n) ≤ 2
  linarith only [hsum, hb]

/-- The same ray also has inverse-square decay at large scales. -/
theorem positiveTail_le_two_inv_sq (s : PositiveScale) :
    positiveTail s ≤ 2 / s.val ^ 2 := by
  obtain ⟨hg, hgsum⟩ := reciprocal_nat_square_bound
  have hs : 0 < s.val := s.property
  have hterm (n : ℕ) : natTailTerm s n ≤
      (1 / s.val ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) := by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    calc
      natTailTerm s n ≤ 1 / (s.val * ((n : ℝ) + 1)) ^ 2 := by
        apply one_div_le_one_div_of_le (sq_pos_of_pos (mul_pos hs hn))
        exact pow_le_pow_left₀ (mul_nonneg hs.le hn.le) (by linarith) 2
      _ = _ := by simp only [mul_pow, one_div, mul_inv_rev]; ring
  calc
    positiveTail s ≤ ∑' n : ℕ, (1 / s.val ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) :=
      Summable.tsum_le_tsum hterm (summable_natTailTerm s) (hg.mul_left _)
    _ = (1 / s.val ^ 2) * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := tsum_mul_left
    _ ≤ (1 / s.val ^ 2) * 2 := mul_le_mul_of_nonneg_left hgsum (by positivity)
    _ = _ := by ring

/-- Reciprocal-square envelope on the full integer lattice. -/
def integerEnvelope (s : PositiveScale) (n : ℤ) : ℝ :=
  1 / (1 + s.val * |(n : ℝ)|) ^ 2

private theorem integerEnvelope_nat (s : PositiveScale) (n : ℕ) :
    integerEnvelope s n = 1 / (1 + s.val * (n : ℝ)) ^ 2 := by
  simp only [integerEnvelope, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)]

private theorem integerEnvelope_neg (s : PositiveScale) (n : ℤ) :
    integerEnvelope s (-n) = integerEnvelope s n := by
  simp only [integerEnvelope, Int.cast_neg, abs_neg]

private theorem summable_integerEnvelope_nat (s : PositiveScale) :
    Summable (fun n : ℕ => integerEnvelope s n) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [integerEnvelope_nat, natTailTerm, Nat.cast_add, Nat.cast_one] using
    summable_natTailTerm s

/-- The integer envelope is genuinely summable at every positive scale. -/
theorem summable_integerEnvelope (s : PositiveScale) : Summable (integerEnvelope s) := by
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨summable_integerEnvelope_nat s, ?_⟩
  simpa only [integerEnvelope_neg] using summable_integerEnvelope_nat s

/-- Splitting the two integer rays separates their mass from the zero frequency. -/
theorem tsum_integerEnvelope (s : PositiveScale) :
    (∑' n : ℤ, integerEnvelope s n) = 1 + 2 * positiveTail s := by
  have hn := summable_integerEnvelope_nat s
  have hneg : (fun n : ℕ => integerEnvelope s (-((n : ℤ) + 1))) = natTailTerm s := by
    funext n
    rw [show -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) by simp,
      integerEnvelope_neg, integerEnvelope_nat]
    simp only [natTailTerm, Nat.cast_add, Nat.cast_one]
  have hnatsum : (∑' n : ℕ, integerEnvelope s n) = 1 + positiveTail s := by
    rw [← hn.sum_add_tsum_nat_add 1]
    simp only [sum_range_one, integerEnvelope_nat, Nat.cast_zero, mul_zero, add_zero,
      one_pow, div_one, positiveTail, natTailTerm, Nat.cast_add, Nat.cast_one]
  rw [tsum_of_nat_of_neg_add_one hn (hneg.symm ▸ summable_natTailTerm s), hnatsum, hneg]
  change 1 + positiveTail s + positiveTail s = _
  ring

end GaloisForLFunctions.MetaplecticMobiusDescent.QuarticPoisson
