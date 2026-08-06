import GaloisForLFunctions.RHTower.Sieve.DirichletSigmaAssembled
import GaloisForLFunctions.RHTower.Sieve.DirichletOrderRate

/-!
# The rectangle estimate at the order chosen from `t`

The three structural hypotheses of the assembled rectangle bound — the split point at least `2`, the
split point below the top of the range, and the factorial bound — are the same three the line case
discharges, because the split point and the top exponent are the same functions of `t`.  Only the
first needs strengthening: off the line the split point must be at least `2`, and for `K ≥ 3` the
largeness condition already gives it.

Feeding the order chosen from `t` then produces a growth bound valid uniformly on the rectangle

```text
1 - 1/(6·2^(littlewoodOrder t))  ≤  σ < 1,
```

whose width is `≍ 1/log t` because `2^(littlewoodOrder t) ≍ log t`.  That is the shape and the width
of the classical zero-free region.
-/

namespace RHTower.Sieve

open Finset

/-- For `K ≥ 3` the largeness condition already forces the split point past `1`. -/
theorem two_le_splitExponent {t : ℝ} {K : ℕ} (hK : 3 ≤ K)
    (hcond : ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) * Real.log ((K : ℝ) - 1)
      + (K : ℝ) * Real.log 2 ≤ Real.log (t / (2 * Real.pi))) :
    2 ≤ splitExponent t K := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKR : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have ha : (0 : ℝ) < (K : ℝ) - 4 / 3 := by linarith
  have hden : (0 : ℝ) < ((K : ℝ) - 4 / 3) * Real.log 2 := by positivity
  have hlogK : Real.log 2 ≤ Real.log ((K : ℝ) - 1) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlognn : (0 : ℝ) ≤ Real.log ((K : ℝ) - 1) := by linarith
  have hbc : Real.log 2 < ((K : ℝ) - 1) * Real.log ((K : ℝ) - 1) := by
    have h2 : (2 : ℝ) * Real.log ((K : ℝ) - 1) ≤ ((K : ℝ) - 1) * Real.log ((K : ℝ) - 1) := by
      nlinarith [hlognn]
    linarith
  have hprod : ((K : ℝ) - 4 / 3) * Real.log 2
      < ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) * Real.log ((K : ℝ) - 1) := by
    have hmul := mul_lt_mul_of_pos_left hbc ha
    nlinarith [hmul]
  have hx : (1 : ℝ) < (Real.log (t / (2 * Real.pi)) - (K : ℝ) * Real.log 2)
      / (((K : ℝ) - 4 / 3) * Real.log 2) := by
    rw [lt_div_iff₀ hden]
    linarith
  have hlt : 1 < splitExponent t K := by
    rw [splitExponent]
    refine Nat.lt_ceil.mpr ?_
    exact_mod_cast hx
  omega

/-- The split point does not exceed the top of the range. -/
theorem splitExponent_le_topExponent {t : ℝ} {K : ℕ} (hK : 2 ≤ K) (ht16 : 16 * Real.pi ≤ t)
    (hbig : 2 * Real.pi * (2 : ℝ) ^ (K : ℕ) ≤ t) (hS1 : 1 ≤ splitExponent t K) :
    splitExponent t K ≤ topExponent t := by
  have h := splitExponent_sub_one_lt_topExponent hK ht16 hbig hS1
  omega

/-- **Rectangle capstone.**  Two explicit conditions on `t` and `K`, plus the strip condition on
`σ`, give the rectangle estimate outright. -/
theorem norm_dirichlet_sigma_littlewood_capstone {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (ht16 : 16 * Real.pi ≤ t) {K : ℕ} (hK : 3 ≤ K)
    (hstrip : 1 - σ ≤ 1 / (6 * (2 : ℝ) ^ K))
    (hcond : ((K : ℝ) - 1) * ((K : ℝ) - 4 / 3) * Real.log ((K : ℝ) - 1)
      + (K : ℝ) * Real.log 2 < Real.log (t / (2 * Real.pi))) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (topExponent t + 1)),
        (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 2 + (2 : ℝ) ^ (stripTheta t K) * ((splitExponent t K : ℕ) : ℝ) * Real.log 2
        + ((topExponent t + 1 - splitExponent t K : ℕ) : ℝ)
            * (2560 * (2 : ℝ) ^ (-stripTheta t K)) := by
  have hπ := Real.pi_pos
  have ht : 0 < t := lt_of_lt_of_le (by positivity) ht16
  have hK2 : 2 ≤ K := by omega
  have hbig := two_pow_lt_of_factorial_cond hK2 ht hcond
  have hS1 : 1 ≤ splitExponent t K := one_le_splitExponent hK2 hbig
  have hS2 : 2 ≤ splitExponent t K := two_le_splitExponent hK hcond.le
  have hSR : splitExponent t K ≤ topExponent t :=
    splitExponent_le_topExponent hK2 ht16 hbig.le hS1
  have hfac := factorial_le_two_pow_splitExponent hK2 hcond.le
  exact norm_dirichlet_sigma_littlewood_theta hσ0 hσ1 (by linarith) hK2 hstrip hS2 hSR hfac

/-- Any admissible order witnesses that the chosen order is admissible. -/
theorem orderThreshold_littlewoodOrder_le_of {t : ℝ} {K₀ : ℕ} (hK₀ : 2 ≤ K₀)
    (ht : orderThreshold K₀ ≤ Real.log (t / (2 * Real.pi))) :
    orderThreshold (littlewoodOrder t) ≤ Real.log (t / (2 * Real.pi)) := by
  have h1 : ((K₀ : ℕ) : ℝ) ≤ Real.log (t / (2 * Real.pi)) :=
    le_trans (cast_le_orderThreshold hK₀) ht
  have h2 : ((K₀ : ℕ) : ℝ) ≤ ((⌈Real.log (t / (2 * Real.pi))⌉₊ : ℕ) : ℝ) :=
    le_trans h1 (Nat.le_ceil _)
  have hb : K₀ ≤ ⌈Real.log (t / (2 * Real.pi))⌉₊ := by exact_mod_cast h2
  exact Nat.findGreatest_spec (P := fun K => orderThreshold K ≤ Real.log (t / (2 * Real.pi)))
    hb ht

/-- **The rectangle estimate at the order chosen from `t`.**  Valid uniformly for every `σ` in the
strip `1 - 1/(6·2^(littlewoodOrder t)) ≤ σ < 1`, whose width is `≍ 1/log t`. -/
theorem norm_dirichlet_sigma_littlewood_order {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (ht16 : 16 * Real.pi ≤ t)
    (ht3 : orderThreshold 3 ≤ Real.log (t / (2 * Real.pi)))
    (hstrip : 1 - σ ≤ 1 / (6 * (2 : ℝ) ^ (littlewoodOrder t))) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (topExponent t + 1)),
        (n : ℂ) ^ (-(σ : ℂ) - Complex.I * (t : ℂ))‖
      ≤ 2 + (2 : ℝ) ^ (stripTheta t (littlewoodOrder t))
            * ((splitExponent t (littlewoodOrder t) : ℕ) : ℝ) * Real.log 2
        + ((topExponent t + 1 - splitExponent t (littlewoodOrder t) : ℕ) : ℝ)
            * (2560 * (2 : ℝ) ^ (-stripTheta t (littlewoodOrder t))) := by
  have hK3 : 3 ≤ littlewoodOrder t := le_littlewoodOrder (by norm_num) ht3
  have hthr := orderThreshold_littlewoodOrder_le_of (K₀ := 3) (by norm_num) ht3
  have hmax : largenessBound (littlewoodOrder t)
      ≤ max (largenessBound (littlewoodOrder t)) (balanceBound (littlewoodOrder t)) :=
    le_max_left _ _
  rw [orderThreshold] at hthr
  have hcond : largenessBound (littlewoodOrder t) < Real.log (t / (2 * Real.pi)) := by linarith
  rw [largenessBound] at hcond
  exact norm_dirichlet_sigma_littlewood_capstone hσ0 hσ1 ht16 hK3 hstrip hcond

end RHTower.Sieve
