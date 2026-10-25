import GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorDiagonalsAreHorizonEnergyRatios
import GaloisForLFunctions.ArithmeticDefectRigidity.WhiteNoiseAndAntipodalEscapeData

/-!
# Horizon order excludes prime-deleted white noise

Deleting the even cofactors preserves positivity and every multiplicative
packet contraction, but violates the numeric horizon order of actual limits.
-/

section

noncomputable section
set_option autoImplicit false
open Finset

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- White noise restricted to cofactors not divisible by two. -/
def oddWhiteNoiseKernel (j k : ℕ+) : ℝ :=
  if 2 ∣ (j : ℕ) then 0 else whiteNoiseKernel j k

theorem oddWhiteNoiseKernel_one_one : oddWhiteNoiseKernel 1 1 = 1 := by
  norm_num [oddWhiteNoiseKernel, whiteNoiseKernel]

theorem oddWhiteNoiseKernel_symm (j k : ℕ+) :
    oddWhiteNoiseKernel j k = oddWhiteNoiseKernel k j := by
  by_cases h : j = k
  · subst k
    rfl
  · simp only [oddWhiteNoiseKernel, whiteNoiseKernel, if_neg h, if_neg (Ne.symm h),
      ite_self]

theorem abs_oddWhiteNoiseKernel_le (j k : ℕ+) :
    |oddWhiteNoiseKernel j k| ≤ cofactorGramRadius j k := by
  by_cases hj : 2 ∣ (j : ℕ)
  · rw [oddWhiteNoiseKernel, if_pos hj, abs_zero]
    unfold cofactorGramRadius
    positivity
  · rw [oddWhiteNoiseKernel, if_neg hj]
    exact abs_whiteNoiseKernel_le j k

/-- The deleted white-noise packet is a sum of nonnegative diagonal energies. -/
theorem oddWhiteNoiseKernel_quadratic_eq (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    (∑ j ∈ S, ∑ k ∈ S, c j * c k * oddWhiteNoiseKernel j k) =
      ∑ j ∈ S, if 2 ∣ (j : ℕ) then 0 else c j ^ 2 / (j : ℝ) := by
  apply sum_congr rfl
  intro j hj
  by_cases h : 2 ∣ (j : ℕ)
  · simp only [oddWhiteNoiseKernel, if_pos h, mul_zero, sum_const_zero]
  · simp only [oddWhiteNoiseKernel, if_neg h, whiteNoiseKernel, mul_ite, mul_zero]
    rw [sum_ite_eq, if_pos hj]
    ring

theorem oddWhiteNoiseKernel_quadratic_nonneg (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    0 ≤ ∑ j ∈ S, ∑ k ∈ S, c j * c k * oddWhiteNoiseKernel j k := by
  rw [oddWhiteNoiseKernel_quadratic_eq]
  apply sum_nonneg
  intro j _
  split_ifs <;> positivity

/-- Dilation either kills the deleted white noise or has exact critical scaling. -/
theorem oddWhiteNoiseKernel_dilation (p j k : ℕ+) :
    oddWhiteNoiseKernel (p * j) (p * k) =
      if 2 ∣ (p : ℕ) then 0 else (1 / (p : ℝ)) * oddWhiteNoiseKernel j k := by
  by_cases hp : 2 ∣ (p : ℕ)
  · have hpj : 2 ∣ ((p * j : ℕ+) : ℕ) := by
      change 2 ∣ (p : ℕ) * (j : ℕ)
      exact dvd_mul_of_dvd_left hp _
    rw [oddWhiteNoiseKernel, if_pos hpj, if_pos hp]
  · have hdiv : 2 ∣ ((p * j : ℕ+) : ℕ) ↔ 2 ∣ (j : ℕ) := by
      rw [PNat.mul_coe, Nat.prime_two.dvd_mul]
      simp only [hp, false_or]
    simp only [if_neg hp, oddWhiteNoiseKernel, hdiv]
    by_cases hj : 2 ∣ (j : ℕ)
    · rw [if_pos hj, if_pos hj, mul_zero]
    · rw [if_neg hj, if_neg hj, whiteNoiseKernel_dilation]

/-- The deleted kernel satisfies every multiplicative packet contraction of actual limits. -/
theorem oddWhiteNoiseKernel_packet_dilation_le (p : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    (∑ j ∈ S, ∑ k ∈ S, c j * c k * oddWhiteNoiseKernel (p * j) (p * k)) ≤
      (1 / (p : ℝ)) * (∑ j ∈ S, ∑ k ∈ S, c j * c k * oddWhiteNoiseKernel j k) := by
  simp only [oddWhiteNoiseKernel_dilation]
  by_cases hp : 2 ∣ (p : ℕ)
  · simp only [if_pos hp, mul_zero, sum_const_zero]
    exact mul_nonneg (by positivity) (oddWhiteNoiseKernel_quadratic_nonneg S c)
  · simp only [if_neg hp, mul_sum]
    apply le_of_eq
    exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring

theorem isPSDKernel_oddWhiteNoise :
    HTGeometry.IsPSDKernel (fun j k => (oddWhiteNoiseKernel j k : ℂ)) :=
  HTGeometry.isPSDKernel_of_real_packet_nonneg oddWhiteNoiseKernel
    oddWhiteNoiseKernel_symm oddWhiteNoiseKernel_quadratic_nonneg

/-- Numeric horizon order excludes a kernel that passes every abstract cofactor contraction. -/
theorem actual_kernel_ne_oddWhiteNoise {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    L.kernel ≠ oddWhiteNoiseKernel := by
  intro h
  have hanti := L.scaled_diagonal_antitone (show (2 : ℕ+) ≤ 3 by decide)
  rw [h] at hanti
  norm_num [oddWhiteNoiseKernel, whiteNoiseKernel] at hanti

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.isPSDKernel_oddWhiteNoise
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.actual_kernel_ne_oddWhiteNoise
end
end
