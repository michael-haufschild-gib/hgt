import GaloisForLFunctions.RHTower.SquareSampledDivisorHyperbola
import GaloisForLFunctions.RHTower.MobiusSquareDivisorKernel
import GaloisForLFunctions.RHTower.DivisorHyperbolaAbelBound

/-!
# Square-sampled divisor remainder with exact dilations

The ordinary divisor remainder differs from minus twice the centered
hyperbola by a logarithmically bounded smooth term. This transfers the
sparse moving-interval estimate to the actual remainder used in the
square bilinear kernel, for every positive dilation.
-/

set_option autoImplicit false
open scoped BigOperators
open Finset

namespace RHTower

theorem abs_mobiusSquareDivisorRemainder_add_centered_le (X : ℕ) :
    |mobiusSquareDivisorRemainder X + 2 * centeredDivisorHyperbola X| ≤
      7 + 2 * Real.log ((X : ℝ) + 1) := by
  by_cases hX : X = 0
  · subst X
    norm_num [mobiusSquareDivisorRemainder, mobiusSquareDivisorSummatory,
      mobiusSquareDivisorMainTerm, centeredDivisorHyperbola]
  have hX1 : 1 ≤ X := by omega
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hcount : mobiusSquareDivisorSummatory X =
      ∑ k ∈ Icc 1 X, ((X / k : ℕ) : ℝ) := by
    have hset : Ioc 0 X = Icc 1 X := by
      ext n
      simp only [mem_Ioc, mem_Icc]
      omega
    have h := ArithmeticFunction.sum_Ioc_sigma0_eq_sum_div X
    rw [hset] at h
    simp_rw [ArithmeticFunction.sigma_zero_apply] at h
    unfold mobiusSquareDivisorSummatory
    exact_mod_cast h
  let E : ℝ := (∑ m ∈ Icc 1 X, Real.log m) - (X : ℝ) * Real.log X + X
  have hstep : (X : ℝ) * (Real.log ((X : ℝ) + 1) - Real.log X) ≤ 1 := by
    have hl := Real.log_le_sub_one_of_pos (show 0 < ((X : ℝ) + 1) / X by positivity)
    rw [Real.log_div (by positivity) (ne_of_gt hXpos)] at hl
    have hm := mul_le_mul_of_nonneg_left hl hXpos.le
    have he : (X : ℝ) * (((X : ℝ) + 1) / X - 1) = 1 := by
      field_simp [ne_of_gt hXpos]
      ring
    rw [he] at hm
    exact hm
  have hlo := stirling_le_sum_log X hX1
  have hhi := sum_log_le_stirling X hX1
  have hE0 : 0 ≤ E := by dsimp [E]; linarith only [hlo]
  have hE : E ≤ 1 + Real.log ((X : ℝ) + 1) := by
    dsimp [E]
    nlinarith only [hhi, hstep]
  have hid := divisorHyperbolaSmooth_add_centered X
  rw [← hcount] at hid
  have he : mobiusSquareDivisorRemainder X + 2 * centeredDivisorHyperbola X =
      E - divisorHyperbolaSmoothRemainder X := by
    dsimp [mobiusSquareDivisorRemainder, mobiusSquareDivisorMainTerm, E]
    linarith only [hid]
  rw [he]
  calc
    _ ≤ |E| + |divisorHyperbolaSmoothRemainder X| := abs_sub _ _
    _ ≤ (1 + Real.log ((X : ℝ) + 1)) + (6 + Real.log ((X : ℝ) + 1)) :=
      add_le_add (by simpa only [abs_of_nonneg hE0] using hE)
        (abs_divisorHyperbolaSmoothRemainder_le hX1)
    _ = _ := by ring

/-- The actual divisor error has uniform square-sampled cancellation at every positive dilation. -/
theorem abs_sum_mobiusSquareDivisorRemainder_square_quotient_le
    (N : ℕ) {q : ℕ} (hq : 0 < q) :
    |∑ s ∈ range N, mobiusSquareDivisorRemainder (s ^ 2 / q)| ≤
      (N : ℝ) * (7 + 2 * Real.log ((N : ℝ) ^ 2 + 1)) +
        16 * ((N : ℝ) + (q * squareSampledHyperbolaCutoff N q : ℕ)) *
          Real.sqrt (squareSampledHyperbolaCutoff N q) *
            (1 + Real.log (q * squareSampledHyperbolaCutoff N q : ℕ)) ^ 4 := by
  have hsmall : |∑ s ∈ range N,
      (mobiusSquareDivisorRemainder (s ^ 2 / q) +
        2 * centeredDivisorHyperbola (s ^ 2 / q))| ≤
      (N : ℝ) * (7 + 2 * Real.log ((N : ℝ) ^ 2 + 1)) := by
    calc
      _ ≤ ∑ s ∈ range N,
          |mobiusSquareDivisorRemainder (s ^ 2 / q) +
            2 * centeredDivisorHyperbola (s ^ 2 / q)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _s ∈ range N, (7 + 2 * Real.log ((N : ℝ) ^ 2 + 1)) := by
        apply sum_le_sum
        intro s hs
        have hsN : s ≤ N := by have := mem_range.mp hs; omega
        have hs2 : s ^ 2 ≤ N ^ 2 := by
          simpa only [pow_two] using Nat.mul_le_mul hsN hsN
        have hx : s ^ 2 / q ≤ N ^ 2 := (Nat.div_le_self (s ^ 2) q).trans hs2
        have hlog : Real.log (((s ^ 2 / q : ℕ) : ℝ) + 1) ≤
            Real.log ((N : ℝ) ^ 2 + 1) :=
          Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hx 1)
        have h := abs_mobiusSquareDivisorRemainder_add_centered_le (s ^ 2 / q)
        linarith only [h, hlog]
      _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]
  have he : (∑ s ∈ range N, mobiusSquareDivisorRemainder (s ^ 2 / q)) =
      (∑ s ∈ range N, (mobiusSquareDivisorRemainder (s ^ 2 / q) +
        2 * centeredDivisorHyperbola (s ^ 2 / q))) -
        2 * ∑ s ∈ range N, centeredDivisorHyperbola (s ^ 2 / q) := by
    simp only [sum_add_distrib, ← mul_sum]
    ring
  rw [he]
  calc
    _ ≤ |∑ s ∈ range N, (mobiusSquareDivisorRemainder (s ^ 2 / q) +
          2 * centeredDivisorHyperbola (s ^ 2 / q))| +
        |2 * ∑ s ∈ range N, centeredDivisorHyperbola (s ^ 2 / q)| := abs_sub _ _
    _ = |∑ s ∈ range N, (mobiusSquareDivisorRemainder (s ^ 2 / q) +
          2 * centeredDivisorHyperbola (s ^ 2 / q))| +
        2 * |∑ s ∈ range N, centeredDivisorHyperbola (s ^ 2 / q)| := by
      rw [abs_mul]
      norm_num
    _ ≤ (N : ℝ) * (7 + 2 * Real.log ((N : ℝ) ^ 2 + 1)) +
        2 * (8 * ((N : ℝ) + (q * squareSampledHyperbolaCutoff N q : ℕ)) *
          Real.sqrt (squareSampledHyperbolaCutoff N q) *
            (1 + Real.log (q * squareSampledHyperbolaCutoff N q : ℕ)) ^ 4) :=
      add_le_add hsmall (mul_le_mul_of_nonneg_left
        (abs_sum_centeredDivisorHyperbola_square_quotient_le N hq) (by norm_num))
    _ = _ := by ring

end RHTower
