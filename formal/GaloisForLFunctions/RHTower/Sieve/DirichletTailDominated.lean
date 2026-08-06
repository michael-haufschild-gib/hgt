import GaloisForLFunctions.RHTower.Sieve.DirichletExplicitRHS

/-!
# Balancing the two terms

The closed-form bound has a head `L/(K - 4/3)` decreasing in the order and a tail increasing in it.
The tail drops below the head exactly when

```text
(L - K log 2) / (3 · 2^K · (K - 4/3))  ≥  log (7680 (K - 4/3) / log 2),
```

and then the whole estimate is `1 + log 2 + 2 L/(K - 4/3)`, which is the Littlewood shape: for `K`
of size `log₂ log t` it is `O(log t / log log t)`.
-/

namespace RHTower.Sieve

open Finset

/-- **Tail below head.**  Once the order is small enough for the depth to pay, the exponential term
is dominated by the harmonic one. -/
theorem tail_le_head {L M : ℝ} {K : ℕ} (hK : 2 ≤ K) (hL : 0 ≤ L) (hM : M ≤ L)
    (hbal : Real.log (7680 * ((K : ℝ) - 4 / 3) / Real.log 2)
      ≤ (L - (K : ℝ) * Real.log 2) / (3 * (2 : ℝ) ^ K * ((K : ℝ) - 4 / 3))) :
    3 * M / Real.log 2
        * (2560 * Real.exp (-((L - (K : ℝ) * Real.log 2)
            / (3 * (2 : ℝ) ^ K * ((K : ℝ) - 4 / 3)))))
      ≤ L / ((K : ℝ) - 4 / 3) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hden : (0 : ℝ) < (K : ℝ) - 4 / 3 := by linarith
  have hc : (0 : ℝ) < 7680 * ((K : ℝ) - 4 / 3) / Real.log 2 := by positivity
  set A : ℝ := 3 * (2 : ℝ) ^ K * ((K : ℝ) - 4 / 3) with hAdef
  set E : ℝ := Real.exp (-((L - (K : ℝ) * Real.log 2) / A)) with hEdef
  have hE : 0 < E := Real.exp_pos _
  -- `7680 (K - 4/3) E ≤ log 2`
  have hcE : 7680 * ((K : ℝ) - 4 / 3) * E ≤ Real.log 2 := by
    have hexp : E ≤ Real.exp (-Real.log (7680 * ((K : ℝ) - 4 / 3) / Real.log 2)) :=
      Real.exp_le_exp.mpr (by linarith [hbal])
    have hval : Real.exp (-Real.log (7680 * ((K : ℝ) - 4 / 3) / Real.log 2))
        = Real.log 2 / (7680 * ((K : ℝ) - 4 / 3)) := by
      rw [Real.exp_neg, Real.exp_log hc]
      field_simp
    rw [hval] at hexp
    have hpos : (0 : ℝ) < 7680 * ((K : ℝ) - 4 / 3) := by positivity
    rw [le_div_iff₀ hpos] at hexp
    linarith
  have hstep : 3 * M / Real.log 2 * (2560 * E) ≤ 3 * L / Real.log 2 * (2560 * E) := by
    have hfac : (0 : ℝ) ≤ 2560 * E := by positivity
    refine mul_le_mul_of_nonneg_right ?_ hfac
    refine div_le_div_of_nonneg_right ?_ hlog2.le
    linarith
  have hkey : 7680 * E / Real.log 2 ≤ 1 / ((K : ℝ) - 4 / 3) := by
    rw [div_le_div_iff₀ hlog2 hden]
    nlinarith [hcE]
  have hfinal : 3 * L / Real.log 2 * (2560 * E) ≤ L / ((K : ℝ) - 4 / 3) := by
    calc 3 * L / Real.log 2 * (2560 * E) = L * (7680 * E / Real.log 2) := by ring
      _ ≤ L * (1 / ((K : ℝ) - 4 / 3)) := mul_le_mul_of_nonneg_left hkey hL
      _ = L / ((K : ℝ) - 4 / 3) := by ring
  exact le_trans hstep hfinal

/-- **Littlewood shape.**  Under the largeness and balance conditions the partial sum on the line
`Re s = 1` is at most `1 + log 2 + 2 log (t/2π) / (K - 4/3)`. -/
theorem norm_dirichlet_partial_littlewood_balanced {t : ℝ} (ht16 : 16 * Real.pi ≤ t) {K : ℕ}
    (hK : 2 ≤ K)
    (hcond : ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) * Real.log ((K : ℝ) - 1)
      + (K : ℝ) * Real.log 2 < Real.log (t / (2 * Real.pi)))
    (hbal : Real.log (7680 * ((K : ℝ) - 4 / 3) / Real.log 2)
      ≤ (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
          / (3 * (2 : ℝ) ^ K * ((K : ℝ) - 4 / 3))) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (topExponent t + 1)),
        (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 1 + Real.log 2 + 2 * Real.log (t / (2 * Real.pi)) / ((K : ℝ) - 4 / 3) := by
  have hπ := Real.pi_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht : 0 < t := lt_of_lt_of_le (by positivity) ht16
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have h8π : (0 : ℝ) < 8 * Real.pi := by positivity
  have hLnn : 0 ≤ Real.log (t / (2 * Real.pi)) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ h2π]
    linarith
  have hMle : Real.log (t / (8 * Real.pi)) ≤ Real.log (t / (2 * Real.pi)) := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_div_iff₀ h8π h2π]
    nlinarith
  have hexp := norm_dirichlet_partial_littlewood_explicit ht16 hK hcond
  have htail := tail_le_head (L := Real.log (t / (2 * Real.pi)))
    (M := Real.log (t / (8 * Real.pi))) hK hLnn hMle hbal
  have hden : (0 : ℝ) < (K : ℝ) - 4 / 3 := by
    have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  have hsum : Real.log (t / (2 * Real.pi)) / ((K : ℝ) - 4 / 3)
      + Real.log (t / (2 * Real.pi)) / ((K : ℝ) - 4 / 3)
      = 2 * Real.log (t / (2 * Real.pi)) / ((K : ℝ) - 4 / 3) := by
    field_simp
    ring
  linarith [hexp, htail, hsum]

end RHTower.Sieve
