import GaloisForLFunctions.RHTower.Sieve.DirichletSigmaShape
import GaloisForLFunctions.RHTower.Sieve.DirichletConstantOrder

/-!
# Endpoint reduction off the line

All four per-block hypotheses of the rectangle shape are monotone in the block index, so with a
constant order they reduce to checks at the two ends: the factorial bound, the upper `t`-bound and
the depth criterion at the bottom block, the lower `t`-bound at the top.

The depth criterion is monotone only when its bracket is nonnegative, that is when
`1 - σ ≤ 1/(3·2^K)`.  That condition is not bookkeeping: it is the width of the strip on which the
estimate holds at all.
-/

namespace RHTower.Sieve

open Finset

/-- **Endpoint form of the rectangle shape.** -/
theorem norm_dirichlet_sigma_littlewood_endpoints {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (ht : 0 < t) {C R : ℕ} (hC : 3 ≤ C) (hR : 1 ≤ R) (K : ℕ) {ε : ℝ} (hε : 0 < ε) (hK : 2 ≤ K)
    (hwidth : 1 - σ ≤ 1 / (3 * (2 : ℝ) ^ K))
    (hfac0 : Nat.factorial (K - 1) ≤ C)
    (hlowTop : 8 * Real.pi * ((C * 2 ^ (R - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh0 : t ≤ 2 * Real.pi * 2 ^ K * ((C : ℕ) : ℝ) ^ (K - 1) * ((C : ℕ) : ℝ) ^ (-(1 / 3) : ℝ))
    (hdeep0 : Real.log (2560 / ε)
      ≤ (1 / (3 * (2 : ℝ) ^ K) - (1 - σ)) * Real.log ((C : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (C * 2 ^ R), (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ (1 + (((C - 1 : ℕ) : ℝ) ^ (1 - σ) - 1) / (1 - σ) + ((C - 1 : ℕ) : ℝ) ^ (-σ))
        + (R : ℝ) * ε := by
  have hCpos : 1 ≤ C := by omega
  have hNmono : ∀ r r' : ℕ, r ≤ r' → C * 2 ^ r ≤ C * 2 ^ r' := fun r r' h =>
    Nat.mul_le_mul_left C (Nat.pow_le_pow_right (by norm_num) h)
  have hNpos : ∀ r : ℕ, 1 ≤ C * 2 ^ r := fun r => by
    calc 1 = 1 * 1 := (Nat.one_mul 1).symm
      _ ≤ C * 2 ^ r := Nat.mul_le_mul hCpos Nat.one_le_two_pow
  have hC0 : C * 2 ^ 0 = C := by simp
  refine norm_dirichlet_sigma_littlewood_shape hσ0 hσ1 ht hC K hε hK ?_ ?_ ?_ ?_
  · -- factorial bound
    intro r _
    calc Nat.factorial (K - 1) ≤ C := hfac0
      _ ≤ C * 2 ^ r := by simpa using hNmono 0 r (Nat.zero_le r)
  · -- lower `t`-bound
    intro r hrR
    have hle : C * 2 ^ r ≤ C * 2 ^ (R - 1) := hNmono r (R - 1) (by omega)
    have hleR : ((C * 2 ^ r : ℕ) : ℝ) ≤ ((C * 2 ^ (R - 1) : ℕ) : ℝ) := by exact_mod_cast hle
    calc 8 * Real.pi * ((C * 2 ^ r : ℕ) : ℝ) ^ ((1 : ℝ) / 3)
        ≤ 8 * Real.pi * ((C * 2 ^ (R - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := by
          refine mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Nat.cast_nonneg _) hleR (by norm_num)) ?_
          have := Real.pi_pos
          positivity
      _ ≤ t := hlowTop
  · -- upper `t`-bound
    intro r _
    refine le_trans hhigh0 ?_
    have hle : C ≤ C * 2 ^ r := by simpa using hNmono 0 r (Nat.zero_le r)
    simpa [hC0] using schedule_upper_bound_mono hK hCpos hle
  · -- depth criterion
    intro r _
    have hbr : (0 : ℝ) ≤ 1 / (3 * (2 : ℝ) ^ K) - (1 - σ) := by linarith
    have hlogle : Real.log ((C : ℕ) : ℝ) ≤ Real.log ((C * 2 ^ r : ℕ) : ℝ) := by
      refine Real.log_le_log ?_ ?_
      · exact_mod_cast hCpos
      · exact_mod_cast (by simpa using hNmono 0 r (Nat.zero_le r) : C ≤ C * 2 ^ r)
    calc Real.log (2560 / ε)
        ≤ (1 / (3 * (2 : ℝ) ^ K) - (1 - σ)) * Real.log ((C : ℕ) : ℝ) := hdeep0
      _ ≤ (1 / (3 * (2 : ℝ) ^ K) - (1 - σ)) * Real.log ((C * 2 ^ r : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hlogle hbr

end RHTower.Sieve
