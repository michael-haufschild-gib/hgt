import GaloisForLFunctions.RHTower.Sieve.DirichletEndpointReduction

/-!
# A constant order schedule suffices

The upper `t`-bound of the derivative-test schedule is monotone in the base point: on a block of
base `N` it reads `t ≤ 2π·2^k·N^(k - 4/3)`, and for `k ≥ 2` the exponent is positive, so satisfying
it at the bottom block satisfies it everywhere above.

Combined with the endpoint reduction — which needs the schedule antitone, and a constant schedule
trivially is — this collapses *all five* hypotheses of the Littlewood shape to conditions at the two
endpoints.  No block-dependent order is needed, and the remaining verification is four numeric
inequalities.
-/

namespace RHTower.Sieve

open Finset

/-- The upper `t`-bound of the schedule is monotone in the base point: its right-hand side is
`2π·2^K·N^(K - 4/3)`, with positive exponent once `K ≥ 2`. -/
theorem schedule_upper_bound_mono {K N N' : ℕ} (hK : 2 ≤ K) (hN : 1 ≤ N) (hNN' : N ≤ N') :
    2 * Real.pi * 2 ^ K * ((N : ℕ) : ℝ) ^ (K - 1) * ((N : ℕ) : ℝ) ^ (-(1 / 3) : ℝ)
      ≤ 2 * Real.pi * 2 ^ K * ((N' : ℕ) : ℝ) ^ (K - 1) * ((N' : ℕ) : ℝ) ^ (-(1 / 3) : ℝ) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN'0 : (0 : ℝ) < (N' : ℝ) := lt_of_lt_of_le hN0 (by exact_mod_cast hNN')
  have hmerge : ∀ M : ℕ, 0 < (M : ℝ) →
      ((M : ℝ)) ^ (K - 1) * ((M : ℝ)) ^ (-(1 / 3) : ℝ)
        = ((M : ℝ)) ^ (((K - 1 : ℕ) : ℝ) - 1 / 3) := by
    intro M hM
    rw [← Real.rpow_natCast ((M : ℝ)) (K - 1), ← Real.rpow_add hM]
    ring_nf
  have hexp : (0 : ℝ) ≤ ((K - 1 : ℕ) : ℝ) - 1 / 3 := by
    have h1 : (1 : ℝ) ≤ ((K - 1 : ℕ) : ℝ) := by
      have : 1 ≤ K - 1 := by omega
      exact_mod_cast this
    linarith
  have hle : ((N : ℝ)) ^ (((K - 1 : ℕ) : ℝ) - 1 / 3)
      ≤ ((N' : ℝ)) ^ (((K - 1 : ℕ) : ℝ) - 1 / 3) :=
    Real.rpow_le_rpow hN0.le (by exact_mod_cast hNN') hexp
  have hcoef : (0 : ℝ) ≤ 2 * Real.pi * 2 ^ K := by positivity
  calc 2 * Real.pi * 2 ^ K * ((N : ℝ)) ^ (K - 1) * ((N : ℝ)) ^ (-(1 / 3) : ℝ)
      = 2 * Real.pi * 2 ^ K * (((N : ℝ)) ^ (K - 1) * ((N : ℝ)) ^ (-(1 / 3) : ℝ)) := by ring
    _ = 2 * Real.pi * 2 ^ K * ((N : ℝ)) ^ (((K - 1 : ℕ) : ℝ) - 1 / 3) := by
        rw [hmerge N hN0]
    _ ≤ 2 * Real.pi * 2 ^ K * ((N' : ℝ)) ^ (((K - 1 : ℕ) : ℝ) - 1 / 3) :=
        mul_le_mul_of_nonneg_left hle hcoef
    _ = 2 * Real.pi * 2 ^ K * (((N' : ℝ)) ^ (K - 1) * ((N' : ℝ)) ^ (-(1 / 3) : ℝ)) := by
        rw [hmerge N' hN'0]
    _ = 2 * Real.pi * 2 ^ K * ((N' : ℝ)) ^ (K - 1) * ((N' : ℝ)) ^ (-(1 / 3) : ℝ) := by ring

/-- **Littlewood shape with a constant order.**  All five hypotheses become endpoint conditions:
three at the bottom block, one at the top. -/
theorem norm_dirichlet_partial_littlewood_const {t : ℝ} (ht : 0 < t) {A S R K : ℕ} (hA : 1 ≤ A)
    (hSR : S < R) {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 2560) (hK : 2 ≤ K)
    (hfacS : Nat.factorial (K - 1) ≤ A * 2 ^ S)
    (hlowTop : 8 * Real.pi * ((A * 2 ^ (R - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t)
    (hhighS : t ≤ 2 * Real.pi * 2 ^ K * ((A * 2 ^ S : ℕ) : ℝ) ^ (K - 1)
      * ((A * 2 ^ S : ℕ) : ℝ) ^ (-(1 / 3) : ℝ))
    (hdeepS : 3 * (2 : ℝ) ^ K * Real.log (2560 / ε) ≤ Real.log ((A * 2 ^ S : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.Ico 1 (A * 2 ^ R), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ (1 + Real.log ((A * 2 ^ S - 1 : ℕ) : ℝ)) + ((R - S : ℕ) : ℝ) * ε := by
  have hNpos : ∀ r : ℕ, 1 ≤ A * 2 ^ r := fun r => by
    calc 1 = 1 * 1 := (Nat.one_mul 1).symm
      _ ≤ A * 2 ^ r := Nat.mul_le_mul hA Nat.one_le_two_pow
  refine norm_dirichlet_partial_littlewood_endpoints ht hA hSR (fun _ => K) hε hε'
    (fun _ _ _ => le_refl K) (fun _ _ _ => hK) hfacS hlowTop ?_ hdeepS
  intro r hrS _
  refine le_trans hhighS ?_
  exact schedule_upper_bound_mono hK (hNpos S)
    (Nat.mul_le_mul_left A (Nat.pow_le_pow_right (by norm_num) hrS))

end RHTower.Sieve
