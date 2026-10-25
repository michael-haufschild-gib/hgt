import GaloisForLFunctions.BiarithmeticGeometry.WeightedDigitEnumeration
import GaloisForLFunctions.BiarithmeticGeometry.FiniteGeometricConvolution
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp

/-!
# Prime-five cofactor packets are digit convolutions

Dividing an integer by a power of five removes its low digits. Triangular finite
summation therefore identifies every signed prime-five cofactor packet with the
digit readout of a causal geometric convolution.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- An exact finite cofactor identity, valid for arbitrary signed kernel coefficients. -/
theorem fiveTruncatedDigitReadout_convolution (a : ℝ) (f : ℕ → ℝ) (M n : ℕ)
    (hn : n < 5 ^ (M + 1)) :
    fiveTruncatedDigitReadout (M + 1) (fun l => finiteGeometricConvolution a f l) n =
      ∑ r ∈ range (M + 1), f r * fiveDigitRow a (n / 5 ^ r) := by
  calc
    _ = ∑ l ∈ range (M + 1), ∑ r ∈ range (l + 1),
        f r * a ^ (l - r) * ((n / 5 ^ (r + (l - r)) % 5 : ℕ) : ℝ) := by
      rw [fiveTruncatedDigitReadout,
        Fin.sum_univ_eq_sum_range (fun l : ℕ =>
          ((n / 5 ^ l % 5 : ℕ) : ℝ) * finiteGeometricConvolution a f l) (M + 1)]
      apply sum_congr rfl
      intro l _
      rw [finiteGeometricConvolution, mul_sum]
      apply sum_congr rfl
      intro r hr
      rw [show r + (l - r) = l by have := mem_range.mp hr; omega]
      ring
    _ = ∑ r ∈ range (M + 1), ∑ k ∈ range (M + 1 - r),
        f r * a ^ k * ((n / 5 ^ (r + k) % 5 : ℕ) : ℝ) :=
      sum_range_diag_flip (M + 1)
        (fun r k => f r * a ^ k * ((n / 5 ^ (r + k) % 5 : ℕ) : ℝ))
    _ = _ := by
      apply sum_congr rfl
      intro r hr
      have hrM : r ≤ M + 1 := (mem_range.mp hr).le
      have hq : n / 5 ^ r < 5 ^ (M + 1 - r) := by
        apply (Nat.div_lt_iff_lt_mul (pow_pos (by omega : 0 < 5) r)).mpr
        rw [← pow_add, Nat.sub_add_cancel hrM]
        exact hn
      rw [fiveDigitRow_eq_truncated a (M + 1 - r) _ hq,
        fiveTruncatedDigitReadout,
        Fin.sum_univ_eq_sum_range (fun k : ℕ =>
          ((n / 5 ^ r / 5 ^ k % 5 : ℕ) : ℝ) * a ^ k) (M + 1 - r), mul_sum]
      apply sum_congr rfl
      intro k _
      rw [Nat.div_div_eq_div_mul, ← pow_add]
      ring

/-- The full finite digit row is the actual prime-five packet at its natural cutoff. -/
theorem fiveWeightedDigitRow_convolution (a : ℝ) (f : ℕ → ℝ) (n : ℕ) :
    fiveWeightedDigitRow (fun l => finiteGeometricConvolution a f l) n =
      ∑ r ∈ range (Nat.log 5 n + 1), f r * fiveDigitRow a (n / 5 ^ r) := by
  exact fiveTruncatedDigitReadout_convolution a f (Nat.log 5 n) n
    (Nat.lt_pow_succ_log_self (by omega : 1 < 5) n)

/-- Factoring the geometric weight gives the exact partial-pole-sum coefficient. -/
theorem finiteGeometricConvolution_eq_partialPoleSum (a : ℝ) (ha : a ≠ 0)
    (f : ℕ → ℝ) (M : ℕ) :
    finiteGeometricConvolution a f M = a ^ M *
      ∑ r ∈ range (M + 1), f r / a ^ r := by
  rw [finiteGeometricConvolution, mul_sum]
  apply sum_congr rfl
  intro r hr
  have hrM : r ≤ M := by have := mem_range.mp hr; omega
  have hp : a ^ M = a ^ (M - r) * a ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hrM]
  rw [hp]
  field_simp [ha]

end GaloisForLFunctions.BiarithmeticGeometry
