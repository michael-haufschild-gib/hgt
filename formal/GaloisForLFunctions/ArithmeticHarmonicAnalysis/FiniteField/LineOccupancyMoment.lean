import GaloisForLFunctions.RHTower.QuasiRHSubfieldProjection
import Mathlib.Algebra.Order.Chebyshev

/-!
# A fourth-moment floor from affine-line occupancy

A character trivial on the base field reads an exact occupancy imbalance on
each affine line. Convexity preserves this contribution when the remaining
character phases are unknown. Summing over parallel lines gives a necessary
quantitative condition for any fourth-moment upper estimate.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

open Finset RHTower.QuasiRHShiftCorrelation
open scoped Classical

variable {F K : Type*} [Field F] [Field K] [Fintype F] [Fintype K] [Algebra F K]

/-- The number of shifts on the line through `x` with direction `uF`. -/
def affineLineOccupancy (S : Finset K) (u x : K) : ℕ :=
  (S.filter (fun h => (x - h) / u ∈ Set.range (algebraMap F K))).card

private theorem norm_sum_fourth_le {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ i ∈ s, ‖f i‖ ^ 4 := by
  calc
    _ ≤ (∑ i ∈ s, ‖f i‖) ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 4
    _ ≤ _ := pow_sum_le_card_mul_sum_pow (fun i _ => norm_nonneg (f i)) 3

private theorem norm_real_fourth (x : ℝ) : ‖(x : ℂ)‖ ^ 4 = x ^ 4 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  calc
    |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
    _ = (x ^ 2) ^ 2 := by rw [sq_abs]
    _ = x ^ 4 := by ring

/-- A single line forces a fourth-moment payment determined by its exact occupancy. -/
theorem affineLine_imbalance_fourth_le (χ : MulChar K ℂ) (hnonprincipal : χ ≠ 1)
    (hχ : ∀ a : F, a ≠ 0 → χ (algebraMap F K a) = 1)
    (hcard : Nat.card K = Nat.card F ^ 2) (S : Finset K) (u : K) (hu : u ≠ 0)
    (x : K) :
    ((Fintype.card F : ℝ) * affineLineOccupancy (F := F) S u x - S.card) ^ 4 ≤
      (Fintype.card F : ℝ) ^ 3 *
        ∑ a : F, ‖∑ h ∈ S, χ (x - u * algebraMap F K a - h)‖ ^ 4 := by
  have hsum := subfield_affineLine_packet_sum χ hnonprincipal hχ hcard u hu x S
  have hn : ‖χ u‖ = 1 := by
    have hs := character_norm_sq χ u
    rw [if_neg hu] at hs
    nlinarith only [hs, norm_nonneg (χ u)]
  have he : ‖∑ a : F, ∑ h ∈ S, χ (x - u * algebraMap F K a - h)‖ ^ 4 =
      ((Fintype.card F : ℝ) * affineLineOccupancy (F := F) S u x - S.card) ^ 4 := by
    rw [hsum, norm_mul, hn, one_mul]
    have hcast : (Fintype.card F : ℂ) *
        (S.filter (fun h => (x - h) / u ∈ Set.range (algebraMap F K))).card - S.card =
        (((Fintype.card F : ℝ) * affineLineOccupancy (F := F) S u x - S.card : ℝ) : ℂ) := by
      simp only [affineLineOccupancy, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_natCast]
    rw [hcast, norm_real_fourth]
  rw [← he]
  exact norm_sum_fourth_le univ _

/-- Summing parallel-line imbalances gives an unconditional fourth-moment floor.
Each line occurs once per point on it, accounting for the fourth power of `|F|`. -/
theorem affineLine_occupancy_moment_le (χ : MulChar K ℂ) (hnonprincipal : χ ≠ 1)
    (hχ : ∀ a : F, a ≠ 0 → χ (algebraMap F K a) = 1)
    (hcard : Nat.card K = Nat.card F ^ 2) (S : Finset K) (u : K) (hu : u ≠ 0) :
    (∑ x : K,
      ((Fintype.card F : ℝ) * affineLineOccupancy (F := F) S u x - S.card) ^ 4) ≤
      (Fintype.card F : ℝ) ^ 4 * shiftFourthMoment χ S := by
  calc
    _ ≤ ∑ x : K, (Fintype.card F : ℝ) ^ 3 *
        ∑ a : F, ‖∑ h ∈ S, χ (x - u * algebraMap F K a - h)‖ ^ 4 :=
      sum_le_sum fun x _ => affineLine_imbalance_fourth_le χ hnonprincipal hχ hcard S u hu x
    _ = (Fintype.card F : ℝ) ^ 3 *
        ∑ a : F, ∑ x : K, ‖∑ h ∈ S, χ (x - u * algebraMap F K a - h)‖ ^ 4 := by
      rw [← mul_sum, sum_comm]
    _ = (Fintype.card F : ℝ) ^ 3 * ∑ _a : F, shiftFourthMoment χ S := by
      congr 1
      apply sum_congr rfl
      intro a _
      exact (Equiv.subRight (u * algebraMap F K a)).sum_comp
        (fun x => ‖∑ h ∈ S, χ (x - h)‖ ^ 4)
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]; ring

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
