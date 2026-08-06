import GaloisForLFunctions.RHTower.Sieve.DirichletLittlewoodShape

/-!
# Endpoint reduction of the schedule hypotheses

Four of the five hypotheses of the Littlewood shape are monotone in the block index once the order
schedule is antitone: raising the block raises `N` and lowers `k`.  So the order bound and the
factorial bound bind at the bottom block, the lower `t`-bound binds at the top block, and the depth
criterion binds at the bottom block.  Only the upper `t`-bound genuinely varies — it is what the
order at each block is chosen to satisfy.

Reducing the verification from `R - S` checks to two endpoint checks is what makes an explicit
parameter choice tractable.
-/

namespace RHTower.Sieve

open Finset

/-- **Endpoint form of the Littlewood shape.**  With an antitone order schedule, the order bound,
the factorial bound and the depth criterion are checked only at the bottom block, and the lower
`t`-bound only at the top block. -/
theorem norm_dirichlet_partial_littlewood_endpoints {t : ℝ} (ht : 0 < t) {A S R : ℕ} (hA : 1 ≤ A)
    (hSR : S < R) (k : ℕ → ℕ) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 2560)
    (hkanti : ∀ r, S ≤ r → r < R → k r ≤ k S)
    (hktop : ∀ r, S ≤ r → r < R → 2 ≤ k r)
    (hfacS : Nat.factorial (k S - 1) ≤ A * 2 ^ S)
    (hlowTop : 8 * Real.pi * ((A * 2 ^ (R - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhigh : ∀ r, S ≤ r → r < R →
      t ≤ 2 * Real.pi * 2 ^ (k r) * ((A * 2 ^ r : ℕ) : ℝ) ^ (k r - 1)
        * ((A * 2 ^ r : ℕ) : ℝ) ^ (-(1 / 3) : ℝ))
    (hdeepS : 3 * (2 : ℝ) ^ (k S) * Real.log (2560 / ε) ≤ Real.log ((A * 2 ^ S : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.Ico 1 (A * 2 ^ R), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ (1 + Real.log ((A * 2 ^ S - 1 : ℕ) : ℝ)) + ((R - S : ℕ) : ℝ) * ε := by
  have hlogpos : 0 ≤ Real.log (2560 / ε) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hε]
    linarith
  -- monotonicity of the block base point
  have hNmono : ∀ r r' : ℕ, r ≤ r' → A * 2 ^ r ≤ A * 2 ^ r' := fun r r' h =>
    Nat.mul_le_mul_left A (Nat.pow_le_pow_right (by norm_num) h)
  have hNpos : ∀ r : ℕ, 1 ≤ A * 2 ^ r := fun r => by
    calc 1 = 1 * 1 := (Nat.one_mul 1).symm
      _ ≤ A * 2 ^ r := Nat.mul_le_mul hA Nat.one_le_two_pow
  refine norm_dirichlet_partial_littlewood_shape ht hA (by omega) k hε hktop ?_ ?_ hhigh ?_
  · -- factorial bound
    intro r hrS hrR
    calc Nat.factorial (k r - 1) ≤ Nat.factorial (k S - 1) :=
          Nat.factorial_le (by have := hkanti r hrS hrR; omega)
      _ ≤ A * 2 ^ S := hfacS
      _ ≤ A * 2 ^ r := hNmono S r hrS
  · -- lower `t`-bound
    intro r hrS hrR
    have hle : A * 2 ^ r ≤ A * 2 ^ (R - 1) := hNmono r (R - 1) (by omega)
    have hleR : ((A * 2 ^ r : ℕ) : ℝ) ≤ ((A * 2 ^ (R - 1) : ℕ) : ℝ) := by exact_mod_cast hle
    have h0 : (0 : ℝ) ≤ ((A * 2 ^ r : ℕ) : ℝ) := Nat.cast_nonneg _
    calc 8 * Real.pi * ((A * 2 ^ r : ℕ) : ℝ) ^ ((1 : ℝ) / 3)
        ≤ 8 * Real.pi * ((A * 2 ^ (R - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0 hleR (by norm_num)) ?_
          positivity
      _ ≤ t := hlowTop
  · -- depth criterion
    intro r hrS hrR
    have hkle : k r ≤ k S := hkanti r hrS hrR
    have hpow : (2 : ℝ) ^ (k r) ≤ (2 : ℝ) ^ (k S) := pow_le_pow_right₀ (by norm_num) hkle
    have hlogle : Real.log ((A * 2 ^ S : ℕ) : ℝ) ≤ Real.log ((A * 2 ^ r : ℕ) : ℝ) := by
      refine Real.log_le_log ?_ ?_
      · exact_mod_cast hNpos S
      · exact_mod_cast hNmono S r hrS
    calc 3 * (2 : ℝ) ^ (k r) * Real.log (2560 / ε)
        ≤ 3 * (2 : ℝ) ^ (k S) * Real.log (2560 / ε) := by
          refine mul_le_mul_of_nonneg_right ?_ hlogpos
          exact mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ ≤ Real.log ((A * 2 ^ S : ℕ) : ℝ) := hdeepS
      _ ≤ Real.log ((A * 2 ^ r : ℕ) : ℝ) := hlogle

end RHTower.Sieve
