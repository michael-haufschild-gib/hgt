import GaloisForLFunctions.RHTower.WeilKloostermanBound

/-!
# The exponential rate of tensor trace moments

A bound for the `m`-th power of the absolute trace bounds the `m`-th power of each
eigenvalue modulus at the same exponential rate. Expand the trace power as a power
sum on the tensor spectrum, then apply finite power-sum rigidity. Thus a fixed
exponential rate for every even tensor degree forces all eigenvalues into the unit disk.
-/

open Finset Filter
noncomputable section
namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies

variable {ι : Type*} [Fintype ι]

/-- The eigenvalue associated with one word in a tensor power. -/
def tensorEigenvalue (z : ι → ℂ) (m : ℕ) (a : Fin m → ι) : ℂ := ∏ j, z (a j)

/-- The power sum on the tensor spectrum is the power of the original trace. -/
theorem tensor_powerSum (z : ι → ℂ) (m n : ℕ) :
    ∑ a : Fin m → ι, tensorEigenvalue z m a ^ n = (∑ i, z i ^ n) ^ m := by
  simp only [tensorEigenvalue, ← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun (_ : Fin m) (i : ι) => z i ^ n)]
  simp

/-- Exponential trace control bounds each tensor eigenvalue, including repeated words. -/
theorem norm_pow_le_of_tensor_moment_bound (z : ι → ℂ) (m : ℕ) {B C : ℝ}
    (hB : 0 ≤ B) (h : ∀ n : ℕ, ‖∑ i, z i ^ n‖ ^ m ≤ C * B ^ n) (i : ι) :
    ‖z i‖ ^ m ≤ B := by
  have hb := RHTower.WeilKloosterman.norm_le_of_power_sums_bound univ
    (tensorEigenvalue z m) (C := C) (m0 := 0) hB (fun n _ => ?_) (fun _ => i) (mem_univ _)
  · simpa [tensorEigenvalue, norm_pow] using hb
  · rw [tensor_powerSum, norm_pow]
    exact h n

/-- The optimal exponential rate of a positive tensor degree is the largest powered modulus. -/
theorem tensor_moment_bound_iff (z : ι → ℂ) (m : ℕ) (hm : m ≠ 0) {B : ℝ}
    (hB : 0 ≤ B) :
    (∃ C : ℝ, ∀ n : ℕ, ‖∑ i, z i ^ n‖ ^ m ≤ C * B ^ n) ↔
      ∀ i, ‖z i‖ ^ m ≤ B := by
  classical
  refine ⟨fun ⟨C, hC⟩ i => norm_pow_le_of_tensor_moment_bound z m hB hC i, ?_⟩
  intro hz
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, fun n => by simp [hm]⟩
  · obtain ⟨i₀, _, hmax⟩ := univ.exists_max_image (fun i => ‖z i‖) univ_nonempty
    refine ⟨(Fintype.card ι : ℝ) ^ m, fun n => ?_⟩
    have ht : ‖∑ i, z i ^ n‖ ≤ (Fintype.card ι : ℝ) * ‖z i₀‖ ^ n := by
      calc ‖∑ i, z i ^ n‖ ≤ ∑ i, ‖z i ^ n‖ := norm_sum_le _ _
        _ ≤ ∑ _ : ι, ‖z i₀‖ ^ n := by
          apply sum_le_sum
          intro i hi
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (hmax i hi) n
        _ = _ := by simp
    calc ‖∑ i, z i ^ n‖ ^ m ≤ ((Fintype.card ι : ℝ) * ‖z i₀‖ ^ n) ^ m :=
        pow_le_pow_left₀ (norm_nonneg _) ht m
      _ = (Fintype.card ι : ℝ) ^ m * (‖z i₀‖ ^ m) ^ n := by
        rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm n m]
      _ ≤ (Fintype.card ι : ℝ) ^ m * B ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (hz i₀) n) (by positivity)

/-- A tensor-order-independent exponential rate is exactly confinement to the unit disk. -/
theorem fixed_base_tensor_bound_iff (z : ι → ℂ) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
      ‖∑ i, z i ^ n‖ ^ (2 * (k + 1)) ≤ C * B ^ n) ↔ ∀ i, ‖z i‖ ≤ 1 := by
  constructor
  · rintro ⟨B, hB, hb⟩ i
    by_contra hi
    have hgt : 1 < ‖z i‖ := lt_of_not_ge hi
    have hsq : 1 < ‖z i‖ ^ 2 := by nlinarith only [hgt]
    obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hsq).eventually_gt_atTop B).exists
    obtain ⟨C, hC⟩ := hb k
    have hle := norm_pow_le_of_tensor_moment_bound z (2 * (k + 1)) hB hC i
    have hinc : (‖z i‖ ^ 2) ^ k ≤ (‖z i‖ ^ 2) ^ (k + 1) := by
      exact pow_le_pow_right₀ hsq.le (Nat.le_succ k)
    rw [pow_mul] at hle
    exact (hk.trans_le (hinc.trans hle)).false
  · intro hz
    refine ⟨1, zero_le_one, fun k => ⟨(Fintype.card ι : ℝ) ^ (2 * (k + 1)), fun n => ?_⟩⟩
    have htrace : ‖∑ i, z i ^ n‖ ≤ (Fintype.card ι : ℝ) := by
      calc ‖∑ i, z i ^ n‖ ≤ ∑ i, ‖z i ^ n‖ := norm_sum_le _ _
        _ ≤ ∑ _ : ι, (1 : ℝ) := by
          apply sum_le_sum
          intro i _
          rw [norm_pow]
          exact (pow_le_pow_left₀ (norm_nonneg _) (hz i) n).trans_eq (one_pow n)
        _ = _ := by simp
    simpa only [one_pow, mul_one] using
      pow_le_pow_left₀ (norm_nonneg _) htrace (2 * (k + 1))

end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
