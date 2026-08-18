import GaloisForLFunctions.RHTower.Sieve.LogMoebiusHarmonicFloor
import GaloisForLFunctions.RHTower.MoebiusFloorSummatory
import GaloisForLFunctions.HTGeometry.HarmonicLogWindow

/-!
# The harmonic-floor defect sum is bounded

The error sum of `sum_moebius_log_div_eq_one_sub_error` is `O(1)`, with an explicit constant.  The
Euler constant is peeled off by the tree's `|∑_{d ≤ N} μ(d)/d| ≤ 1`, and what is left is bounded
termwise: the harmonic defect is at most `1/⌊N/d⌋`, the floor defect of the logarithm is at most
`1/⌊N/d⌋` as well, and `N ≤ 2 ⌊N/d⌋ d`, so each term is at most `4/N` and there are `N` of them.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

theorem two_mul_natDiv_mul_ge {N d : ℕ} (hd : 1 ≤ d) (hdN : d ≤ N) :
    N ≤ 2 * (N / d) * d := by
  have h1 : 1 ≤ N / d := (Nat.one_le_div_iff (by omega)).mpr hdN
  have h2 : N < (N / d + 1) * d := by
    have hmod : d * (N / d) + N % d = N := Nat.div_add_mod N d
    have hlt : N % d < d := Nat.mod_lt _ (by omega)
    calc N = d * (N / d) + N % d := hmod.symm
      _ < d * (N / d) + d := by omega
      _ = (N / d + 1) * d := by ring
  have h3 : N / d + 1 ≤ 2 * (N / d) := by omega
  have h4 : N < 2 * (N / d) * d := lt_of_lt_of_le h2 (Nat.mul_le_mul_right d h3)
  omega

/-- **The harmonic-floor defect at one modulus.** -/
theorem abs_harmonic_floor_defect_le {N d : ℕ} (hd : 1 ≤ d) (hdN : d ≤ N) :
    |((harmonic (N / d) : ℚ) : ℝ) - Real.log ((N : ℝ) / (d : ℝ))
        - Real.eulerMascheroniConstant| ≤ 2 / ((N / d : ℕ) : ℝ) := by
  have hm : 1 ≤ N / d := (Nat.one_le_div_iff (by omega)).mpr hdN
  have hmR : (0 : ℝ) < ((N / d : ℕ) : ℝ) := by exact_mod_cast hm
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hharm := HTGeometry.abs_harmonic_sub_log_sub_eulerMascheroni_le hm
  have hxm : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
  have hmx : (N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ) ≤ 1 := by
    have hlt : (N : ℝ) / (d : ℝ) < ((N / d : ℕ) : ℝ) + 1 := by
      have hnat : N < (N / d + 1) * d := by
        have hmod : d * (N / d) + N % d = N := Nat.div_add_mod N d
        have hlt' : N % d < d := Nat.mod_lt _ (by omega)
        calc N = d * (N / d) + N % d := hmod.symm
          _ < d * (N / d) + d := by omega
          _ = (N / d + 1) * d := by ring
      have hcast : (N : ℝ) < (((N / d : ℕ) : ℝ) + 1) * (d : ℝ) := by
        have := (Nat.cast_lt (α := ℝ)).mpr hnat
        push_cast at this
        linarith
      rw [div_lt_iff₀ hdR]
      exact hcast
    linarith
  have hlogdiff : Real.log ((N : ℝ) / (d : ℝ)) - Real.log ((N / d : ℕ) : ℝ)
      ≤ 1 / ((N / d : ℕ) : ℝ) := by
    have hpos : (0 : ℝ) < (N : ℝ) / (d : ℝ) := lt_of_lt_of_le hmR hxm
    have hratio : Real.log (((N : ℝ) / (d : ℝ)) / ((N / d : ℕ) : ℝ))
        ≤ ((N : ℝ) / (d : ℝ)) / ((N / d : ℕ) : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hsplit : Real.log (((N : ℝ) / (d : ℝ)) / ((N / d : ℕ) : ℝ))
        = Real.log ((N : ℝ) / (d : ℝ)) - Real.log ((N / d : ℕ) : ℝ) :=
      Real.log_div (ne_of_gt hpos) (ne_of_gt hmR)
    rw [hsplit] at hratio
    have hbound : ((N : ℝ) / (d : ℝ)) / ((N / d : ℕ) : ℝ) - 1
        ≤ 1 / ((N / d : ℕ) : ℝ) := by
      rw [div_sub_one (ne_of_gt hmR), div_le_div_iff_of_pos_right hmR]
      linarith
    linarith
  have hlognonneg : 0 ≤ Real.log ((N : ℝ) / (d : ℝ)) - Real.log ((N / d : ℕ) : ℝ) := by
    have := Real.log_le_log hmR hxm
    linarith
  have htwo : (1 : ℝ) / ((N / d : ℕ) : ℝ) + 1 / ((N / d : ℕ) : ℝ)
      = 2 / ((N / d : ℕ) : ℝ) := by
    field_simp
    norm_num
  rw [abs_le] at hharm ⊢
  constructor
  · linarith [hharm.1, hharm.2, htwo]
  · linarith [hharm.1, hharm.2, htwo]

end RHTower.Sieve
