import GaloisForLFunctions.RHTower.Sieve.DirichletTailDominated

/-!
# A threshold for each order

Both conditions on `(t, K)` are of the form "some quantity depending on `K` alone is below
`log (t / 2π)`", so for each fixed order there is a threshold past which they both hold.  The
estimate then reads

```text
‖∑_{n < 2^(R+1)} n^(-1-it)‖  ≤  1 + log 2 + 2 log (t/2π) / (K - 4/3)   for all large `t`,
```

with the constant `2/(K - 4/3)` arbitrarily small.  No construction of `K` as a function of `t` is
needed for this: the quantitative Littlewood exponent requires that, but the qualitative statement
that the partial sum is `o(log t)` follows from the family of fixed-order bounds alone.
-/

namespace RHTower.Sieve

open Finset

/-- The largeness quantity: the left side of the factorial condition. -/
noncomputable def largenessBound (K : ℕ) : ℝ :=
  ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) * Real.log ((K : ℝ) - 1) + (K : ℝ) * Real.log 2

/-- The balance quantity: the left side of the depth condition, shifted by `K log 2`. -/
noncomputable def balanceBound (K : ℕ) : ℝ :=
  3 * (2 : ℝ) ^ K * ((K : ℝ) - 4 / 3)
      * Real.log (7680 * ((K : ℝ) - 4 / 3) / Real.log 2)
    + (K : ℝ) * Real.log 2

/-- **Threshold form.**  For each order there is a threshold past which the estimate holds. -/
theorem littlewood_threshold (K : ℕ) (hK : 2 ≤ K) :
    ∀ t : ℝ,
      max (16 * Real.pi)
          (2 * Real.pi * Real.exp (max (largenessBound K) (balanceBound K) + 1)) ≤ t →
      ‖∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (topExponent t + 1)),
          (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
        ≤ 1 + Real.log 2 + 2 * Real.log (t / (2 * Real.pi)) / ((K : ℝ) - 4 / 3) := by
  intro t hT
  have hπ := Real.pi_pos
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  set C : ℝ := max (largenessBound K) (balanceBound K) + 1 with hCdef
  have ht16 : 16 * Real.pi ≤ t := le_trans (le_max_left _ _) hT
  have htexp : 2 * Real.pi * Real.exp C ≤ t := le_trans (le_max_right _ _) hT
  have hL : C ≤ Real.log (t / (2 * Real.pi)) := by
    have hquot : Real.exp C ≤ t / (2 * Real.pi) := by
      rw [le_div_iff₀ h2π]
      linarith
    have := Real.log_le_log (Real.exp_pos C) hquot
    rwa [Real.log_exp] at this
  have hlarge : largenessBound K < Real.log (t / (2 * Real.pi)) := by
    have := le_max_left (largenessBound K) (balanceBound K)
    rw [hCdef] at hL
    linarith
  have hbalance : balanceBound K ≤ Real.log (t / (2 * Real.pi)) := by
    have := le_max_right (largenessBound K) (balanceBound K)
    rw [hCdef] at hL
    linarith
  refine norm_dirichlet_partial_littlewood_balanced ht16 hK ?_ ?_
  · exact hlarge
  · have hden : (0 : ℝ) < 3 * (2 : ℝ) ^ K * ((K : ℝ) - 4 / 3) := by
      have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
      have : (0 : ℝ) < (K : ℝ) - 4 / 3 := by linarith
      positivity
    rw [le_div_iff₀ hden]
    rw [balanceBound] at hbalance
    nlinarith [hbalance]

end RHTower.Sieve
