import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiSecondGradeAsymptotic
import GaloisForLFunctions.RHTower.PsiRemainderRecursion

/-!
# The Route-P Chebyshev square in the exact second-grade hyperbola law

At a square cutoff, the literal von-Mangoldt hyperbola identity retains the
rectangular Chebyshev square and a signed future-error pairing. Passing from
integer quotients to their polar main terms also retains a nonnegative floor
remainder, bounded by the actual Chebyshev mass.

This identity isolates the signed comparison needed by a proposed hyperbola
payment of Route P. It gives no critical bound for the future-error pairing
and does not establish the native-history linear floor.
-/

open scoped BigOperators
open ArithmeticFunction
namespace RHTower
noncomputable section

def routePHyperbolaFloorRemainder (n : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 n, vonMangoldt d *
    ((n : ℝ) ^ 2 / (d : ℝ) - ((n ^ 2 / d : ℕ) : ℝ))

def routePHarmonicPrimeError (n : ℕ) : ℝ :=
  (∑ d ∈ Finset.Icc 1 n, vonMangoldt d / (d : ℝ)) - Real.log n +
    Real.eulerMascheroniConstant

theorem routeP_hyperbola_half_error (n : ℕ) :
    vonMangoldtSelfConvolutionHyperbolaHalf (n ^ 2) + routePHyperbolaFloorRemainder n =
      (n : ℝ) ^ 2 * (∑ d ∈ Finset.Icc 1 n, vonMangoldt d / (d : ℝ)) +
        ∑ d ∈ Finset.Icc 1 n, vonMangoldt d * psiRemainder (n ^ 2 / d) := by
  rw [vonMangoldtSelfConvolutionHyperbolaHalf, Nat.sqrt_eq', routePHyperbolaFloorRemainder,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  unfold psiRemainder
  ring

theorem routeP_hyperbola_joint_error (n : ℕ) :
    selbergSecondGradePrefixDiscrepancy (n ^ 2) +
        2 * (n : ℝ) * psiRemainder n + psiRemainder n ^ 2 +
        2 * routePHyperbolaFloorRemainder n =
      2 * (n : ℝ) ^ 2 * routePHarmonicPrimeError n +
        2 * ∑ d ∈ Finset.Icc 1 n, vonMangoldt d * psiRemainder (n ^ 2 / d) := by
  have h := sum_vonMangoldt_selfConv_add_sqrtPsi_sq (n ^ 2)
  rw [Nat.sqrt_eq'] at h
  have hh := routeP_hyperbola_half_error n
  unfold psiRemainder at hh
  unfold selbergSecondGradePrefixDiscrepancy routePHarmonicPrimeError psiRemainder
  simp only [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [h, hh]

theorem routeP_hyperbola_floor_remainder_bounds (n : ℕ) :
    0 ≤ routePHyperbolaFloorRemainder n ∧
      routePHyperbolaFloorRemainder n ≤ chebyshevPsi n := by
  have hcell (d : ℕ) (hd : d ∈ Finset.Icc 1 n) :
      0 ≤ (n : ℝ)^2 / d - ((n^2/d : ℕ) : ℝ) ∧
      (n : ℝ)^2 / d - ((n^2/d : ℕ) : ℝ) ≤ 1 := by
    have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hid : ((n^2 % d : ℕ) : ℝ) + (d : ℝ) * ((n^2/d : ℕ) : ℝ) = (n : ℝ)^2 := by
      exact_mod_cast Nat.mod_add_div (n^2) d
    have hm : ((n^2 % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast Nat.mod_lt (n^2) hd0
    have he : (n : ℝ)^2 / d - ((n^2/d : ℕ) : ℝ) = ((n^2 % d : ℕ) : ℝ) / d := by
      field_simp
      nlinarith only [hid]
    rw [he]
    exact ⟨div_nonneg (Nat.cast_nonneg _) hdR.le, (div_le_one hdR).mpr hm.le⟩
  constructor
  · exact Finset.sum_nonneg fun d hd => mul_nonneg vonMangoldt_nonneg (hcell d hd).1
  · apply Finset.sum_le_sum
    intro d hd
    exact (mul_le_mul_of_nonneg_left (hcell d hd).2 vonMangoldt_nonneg).trans_eq (mul_one _)

end
end RHTower
