import GaloisForLFunctions.RHTower.Sieve.DirichletSigmaHeadSimplify
import GaloisForLFunctions.RHTower.Sieve.DirichletTopExponentChoice

/-!
# The assembled rectangle bound

The two bounds on `t` off the line are the same ones the line case solves: the split point is the
ceiling of the balance point, the top of the range the floor of `3 log(t/8π)/log 2`.  With
`C = 2^S` and the range running up to `2^(T+1)` the estimate becomes a bound in `t`, the order `K`
and `σ` alone.

Writing `θ = S/(6·2^K)`, the two terms of the result are

```text
2^θ · S log 2      (head)          and        R · 2560 · 2^(-θ)      (tail),
```

so the same exponent controls both, with opposite signs: pushing the split point up widens the head
and shrinks each block's contribution.  Being uniform for every `σ` in `1 - 1/(6·2^K) ≤ σ < 1`,
this is a growth bound on a rectangle left of `Re s = 1`.
-/

namespace RHTower.Sieve

open Finset

/-- A power of two raised to a natural power and to a real power, merged into one real exponent. -/
private theorem two_pow_merge' (m j : ℕ) (c : ℝ) :
    ((2 ^ m : ℕ) : ℝ) ^ j * ((2 ^ m : ℕ) : ℝ) ^ (c : ℝ)
      = (2 : ℝ) ^ (((m : ℝ) * (j : ℝ)) + (m : ℝ) * c) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hcast : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ (m : ℕ) := by push_cast; ring
  rw [hcast, ← Real.rpow_natCast (2 : ℝ) m, ← Real.rpow_natCast ((2 : ℝ) ^ ((m : ℕ) : ℝ)) j,
    ← Real.rpow_mul h2.le, ← Real.rpow_mul h2.le, ← Real.rpow_add h2]

/-- **Assembled rectangle bound.**  Both exponents are the canonical choices, so only the order `K`
and the abscissa `σ` remain free. -/
theorem norm_dirichlet_sigma_littlewood_assembled {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (ht8 : 8 * Real.pi ≤ t) {K : ℕ} (hK : 2 ≤ K)
    (hstrip : 1 - σ ≤ 1 / (6 * (2 : ℝ) ^ K))
    (hS2 : 2 ≤ splitExponent t K)
    (hSR : splitExponent t K ≤ topExponent t)
    (hfac : Nat.factorial (K - 1) ≤ 2 ^ (splitExponent t K)) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (topExponent t + 1)),
        (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 2 + ((2 ^ splitExponent t K : ℕ) : ℝ) ^ (1 - σ)
            * Real.log ((2 ^ splitExponent t K : ℕ) : ℝ)
        + ((topExponent t + 1 - splitExponent t K : ℕ) : ℝ)
            * stripTargetEps (2 ^ splitExponent t K) K := by
  have hπ := Real.pi_pos
  have ht : 0 < t := lt_of_lt_of_le (by positivity) ht8
  set S : ℕ := splitExponent t K with hSdef
  set T : ℕ := topExponent t with hTdef
  set C : ℕ := 2 ^ S with hCdef
  set R : ℕ := T + 1 - S with hRdef
  have h4C : 4 ≤ C := by
    rw [hCdef]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) hS2
  have hC3 : 3 ≤ C := by omega
  have hR1 : 1 ≤ R := by omega
  have hsum : C * 2 ^ R = 2 ^ (T + 1) := by
    rw [hCdef, hRdef, ← pow_add]
    congr 1
    omega
  have hlowIdx : C * 2 ^ (R - 1) = 2 ^ T := by
    rw [hCdef, hRdef, ← pow_add]
    congr 1
    omega
  have hlowTop : 8 * Real.pi * ((C * 2 ^ (R - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / 3) ≤ t := by
    rw [hlowIdx]
    have hcast : ((2 ^ T : ℕ) : ℝ) = (2 : ℝ) ^ (T : ℕ) := by push_cast; ring
    have hthird : (T : ℝ) * (1 / 3) = (T : ℝ) / 3 := by ring
    rw [hcast, ← Real.rpow_natCast (2 : ℝ) T, ← Real.rpow_mul (by norm_num), hthird]
    exact topExponent_bound ht8
  have hhigh0 : t ≤ 2 * Real.pi * 2 ^ K * ((C : ℕ) : ℝ) ^ (K - 1)
      * ((C : ℕ) : ℝ) ^ (-(1 / 3) : ℝ) := by
    have hKcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
      have h1 : 1 ≤ K := by omega
      push_cast [Nat.cast_sub h1]
      ring
    have hmerge : ((C : ℕ) : ℝ) ^ (K - 1) * ((C : ℕ) : ℝ) ^ (-(1 / 3) : ℝ)
        = (2 : ℝ) ^ ((S : ℝ) * ((K : ℝ) - 4 / 3)) := by
      rw [hCdef, two_pow_merge' S (K - 1) (-(1 / 3) : ℝ), hKcast]
      congr 1
      ring
    have hsplit : 2 * Real.pi * (2 : ℝ) ^ ((S : ℝ) * ((K : ℝ) - 4 / 3) + (K : ℝ))
        = 2 * Real.pi * 2 ^ K * (2 : ℝ) ^ ((S : ℝ) * ((K : ℝ) - 4 / 3)) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_natCast]
      ring
    calc t ≤ 2 * Real.pi * (2 : ℝ) ^ ((S : ℝ) * ((K : ℝ) - 4 / 3) + (K : ℝ)) :=
          le_two_pow_splitExponent ht hK
      _ = 2 * Real.pi * 2 ^ K * (2 : ℝ) ^ ((S : ℝ) * ((K : ℝ) - 4 / 3)) := hsplit
      _ = 2 * Real.pi * 2 ^ K * (((C : ℕ) : ℝ) ^ (K - 1) * ((C : ℕ) : ℝ) ^ (-(1 / 3) : ℝ)) := by
          rw [hmerge]
      _ = 2 * Real.pi * 2 ^ K * ((C : ℕ) : ℝ) ^ (K - 1) * ((C : ℕ) : ℝ) ^ (-(1 / 3) : ℝ) := by
          ring
  have hmain := norm_dirichlet_sigma_littlewood_strip_head hσ0 hσ1 ht hC3 hR1 K hK hstrip
    hfac hlowTop hhigh0
  rwa [hsum] at hmain

/-- The exponent that controls both terms of the assembled bound. -/
noncomputable def stripTheta (t : ℝ) (K : ℕ) : ℝ :=
  ((splitExponent t K : ℕ) : ℝ) / (6 * (2 : ℝ) ^ K)

/-- At a power-of-two split point the canonical target is an explicit power of two. -/
theorem stripTargetEps_two_pow (S K : ℕ) :
    stripTargetEps (2 ^ S) K = 2560 * (2 : ℝ) ^ (-((S : ℝ) / (6 * (2 : ℝ) ^ K))) := by
  have hcast : ((2 ^ S : ℕ) : ℝ) = (2 : ℝ) ^ (S : ℕ) := by push_cast; ring
  rw [stripTargetEps, hcast, Real.log_pow, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 1
  congr 1
  ring

/-- The head at a power-of-two split point, bounded through the strip condition. -/
theorem two_pow_rpow_head_le {σ : ℝ} {S K : ℕ}
    (hstrip : 1 - σ ≤ 1 / (6 * (2 : ℝ) ^ K)) :
    ((2 ^ S : ℕ) : ℝ) ^ (1 - σ) * Real.log ((2 ^ S : ℕ) : ℝ)
      ≤ (2 : ℝ) ^ ((S : ℝ) / (6 * (2 : ℝ) ^ K)) * (S : ℝ) * Real.log 2 := by
  have hcast : ((2 ^ S : ℕ) : ℝ) = (2 : ℝ) ^ (S : ℕ) := by push_cast; ring
  have hlog : Real.log ((2 ^ S : ℕ) : ℝ) = (S : ℝ) * Real.log 2 := by
    rw [hcast, Real.log_pow]
  have hpow : ((2 ^ S : ℕ) : ℝ) ^ (1 - σ) = (2 : ℝ) ^ ((S : ℝ) * (1 - σ)) := by
    rw [hcast, ← Real.rpow_natCast (2 : ℝ) S, ← Real.rpow_mul (by norm_num)]
  have hS : (0 : ℝ) ≤ (S : ℝ) := Nat.cast_nonneg S
  have hexp : (S : ℝ) * (1 - σ) ≤ (S : ℝ) / (6 * (2 : ℝ) ^ K) := by
    have hmul := mul_le_mul_of_nonneg_left hstrip hS
    calc (S : ℝ) * (1 - σ) ≤ (S : ℝ) * (1 / (6 * (2 : ℝ) ^ K)) := hmul
      _ = (S : ℝ) / (6 * (2 : ℝ) ^ K) := by ring
  have hmono : (2 : ℝ) ^ ((S : ℝ) * (1 - σ)) ≤ (2 : ℝ) ^ ((S : ℝ) / (6 * (2 : ℝ) ^ K)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [hpow, hlog]
  calc (2 : ℝ) ^ ((S : ℝ) * (1 - σ)) * ((S : ℝ) * Real.log 2)
      ≤ (2 : ℝ) ^ ((S : ℝ) / (6 * (2 : ℝ) ^ K)) * ((S : ℝ) * Real.log 2) :=
        mul_le_mul_of_nonneg_right hmono (by positivity)
    _ = (2 : ℝ) ^ ((S : ℝ) / (6 * (2 : ℝ) ^ K)) * (S : ℝ) * Real.log 2 := by ring

/-- **The rectangle bound in trade-off form.**  One exponent `θ = S/(6·2^K)` controls the head and
the per-block saving, with opposite signs. -/
theorem norm_dirichlet_sigma_littlewood_theta {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (ht8 : 8 * Real.pi ≤ t) {K : ℕ} (hK : 2 ≤ K)
    (hstrip : 1 - σ ≤ 1 / (6 * (2 : ℝ) ^ K))
    (hS2 : 2 ≤ splitExponent t K)
    (hSR : splitExponent t K ≤ topExponent t)
    (hfac : Nat.factorial (K - 1) ≤ 2 ^ (splitExponent t K)) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (topExponent t + 1)),
        (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 2 + (2 : ℝ) ^ (stripTheta t K) * ((splitExponent t K : ℕ) : ℝ) * Real.log 2
        + ((topExponent t + 1 - splitExponent t K : ℕ) : ℝ)
            * (2560 * (2 : ℝ) ^ (-stripTheta t K)) := by
  have hmain := norm_dirichlet_sigma_littlewood_assembled hσ0 hσ1 ht8 hK hstrip hS2 hSR hfac
  have hhead := two_pow_rpow_head_le (σ := σ) (S := splitExponent t K) (K := K) hstrip
  have htail : stripTargetEps (2 ^ splitExponent t K) K
      = 2560 * (2 : ℝ) ^ (-stripTheta t K) := by
    rw [stripTheta]
    exact stripTargetEps_two_pow _ _
  have hRnn : (0 : ℝ) ≤ ((topExponent t + 1 - splitExponent t K : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [htail] at hmain
  simp only [stripTheta] at hmain ⊢
  linarith

end RHTower.Sieve
