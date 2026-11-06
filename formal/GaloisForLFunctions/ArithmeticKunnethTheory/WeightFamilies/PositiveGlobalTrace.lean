import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.TensorGrowth
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.UpperLefschetzBoundsAreBlindOnlyToRealZeros

/-!
# Positivity bounds a virtual spectral trace

For a nonnegative difference of two finite spectral traces, a bound on the positive
spectrum also bounds the negative spectrum. Positivity supplies an upper bound on
its real power sums; finite spectral rigidity then controls every eigenvalue.
Consequently a global trace dominating a local tensor moment supplies that moment's
exponential bound without a separate weight theorem for the negative cohomology.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

/-- The real trace of a difference of two finite spectra. -/
def virtualTrace (a : ι → ℂ) (b : κ → ℂ) (n : ℕ) : ℝ :=
  (∑ i, a i ^ n).re - (∑ j, b j ^ n).re

private theorem powerSum_norm_le (a : ι → ℂ) {B : ℝ}
    (ha : ∀ i, ‖a i‖ ≤ B) (n : ℕ) :
    ‖∑ i, a i ^ n‖ ≤ (Fintype.card ι : ℝ) * B ^ n := by
  calc ‖∑ i, a i ^ n‖ ≤ ∑ i, ‖a i ^ n‖ := norm_sum_le _ _
    _ ≤ ∑ _ : ι, B ^ n := by
      apply sum_le_sum
      intro i _
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (ha i) n
    _ = _ := by simp

/-- Nonnegative virtual traces force the negative spectrum inside the positive radius.
No condition at extension degree zero is needed. -/
theorem negative_spectrum_norm_le (a : ι → ℂ) (b : κ → ℂ) {B : ℝ}
    (hB : 0 < B) (ha : ∀ i, ‖a i‖ ≤ B)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 ≤ virtualTrace a b n) : ∀ j, ‖b j‖ ≤ B := by
  apply ArithmeticCastelnuovoSeveri.norm_le_of_re_sum_pow_le b hB
    (C := (Fintype.card ι : ℝ) + Fintype.card κ)
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [pow_zero, sum_const, nsmul_eq_mul, mul_one, Complex.natCast_re]
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  · have ht := hpos n (Nat.one_le_iff_ne_zero.mpr hn)
    have ha' := (Complex.re_le_norm (∑ i, a i ^ n)).trans (powerSum_norm_le a ha n)
    have hc : 0 ≤ (Fintype.card κ : ℝ) * B ^ n := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hB.le n)
    dsimp only [virtualTrace] at ht
    nlinarith only [ht, ha', hc]

/-- A nonnegative virtual trace grows at the positive spectrum's radius, with the sum
of the two dimensions as an explicit constant. -/
theorem positive_virtualTrace_le (a : ι → ℂ) (b : κ → ℂ) {B : ℝ}
    (hB : 0 < B) (ha : ∀ i, ‖a i‖ ≤ B)
    (hpos : ∀ n : ℕ, 1 ≤ n → 0 ≤ virtualTrace a b n) (n : ℕ) :
    virtualTrace a b n ≤ ((Fintype.card ι : ℝ) + Fintype.card κ) * B ^ n := by
  have hb := negative_spectrum_norm_le a b hB ha hpos
  have hpa := (Complex.re_le_norm (∑ i, a i ^ n)).trans (powerSum_norm_le a ha n)
  have hpb := (neg_le_abs ((∑ j, b j ^ n).re)).trans
    ((Complex.abs_re_le_norm _).trans (powerSum_norm_le b hb n))
  dsimp only [virtualTrace]
  nlinarith only [hpa, hpb]

/-- Global domination of a local tensor moment bounds every local tensor eigenvalue.
The global trace need only be defined at positive extension degrees. -/
theorem tensor_norm_pow_le_of_global_trace (z : ν → ℂ) (m : ℕ)
    (a : ι → ℂ) (b : κ → ℂ) {B : ℝ} (hB : 0 < B)
    (ha : ∀ i, ‖a i‖ ≤ B)
    (hdom : ∀ n : ℕ, 1 ≤ n → ‖∑ i, z i ^ n‖ ^ m ≤ virtualTrace a b n)
    (i : ν) : ‖z i‖ ^ m ≤ B := by
  have hpos : ∀ n : ℕ, 1 ≤ n → 0 ≤ virtualTrace a b n :=
    fun n hn => (pow_nonneg (norm_nonneg _) m).trans (hdom n hn)
  have hbound := positive_virtualTrace_le a b hB ha hpos
  apply norm_pow_le_of_tensor_moment_bound z m hB.le
    (C := (Fintype.card ι : ℝ) + Fintype.card κ + (Fintype.card ν : ℝ) ^ m) _ i
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [pow_zero, sum_const, nsmul_eq_mul, mul_one]
    rw [Complex.norm_natCast]
    exact le_add_of_nonneg_left (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · have ht := (hdom n (Nat.one_le_iff_ne_zero.mpr hn)).trans (hbound n)
    have hc : 0 ≤ (Fintype.card ν : ℝ) ^ m * B ^ n :=
      mul_nonneg (pow_nonneg (Nat.cast_nonneg _) m) (pow_nonneg hB.le n)
    nlinarith only [ht, hc]

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
