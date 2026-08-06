# Cycle 16: the infinite-volume bridge — U2 CLOSED (2026-08-06)

Card: `squarefree-gibbs-parity-vortex.md` (cycle-16).
Lean: `formal/GaloisForLFunctions/RHTower/GibbsInfiniteVolume.lean`, wired, built, no
sorry, axioms clean.

## THE BRIDGE (closes the U2 limitation from cycle 8)
`moebiusLaplace x := ∑' n, μ(n)·e^{−x n}`, `primesUpTo y := (range (y+1)).filter Nat.Prime`.
**`abs_moebiusLaplace_sub_gibbs_le`**: for x > 0 and any y,
  |Φ(x) − gibbsDiag (primesUpTo y) x (−1)| ≤ e^{−x}^{y+1} / (1 − e^{−x}).
Proof: cycle-15 anchor makes the gas ∑_{d∣m} μ(d)e^{−dx}; divisors of m = ∏ primesUpTo y
are exactly the squarefree integers with all prime factors ≤ y; any n outside with μ(n) ≠ 0
is squarefree with a prime factor > y hence n > y (`dvd_prod_primesUpTo`: squarefree n ≤ y
⟹ n ∣ primorial). Difference supported beyond y, dominated by the geometric tail.

Consequence: ALL finite-volume results of cycles 1–15 transfer to the true Φ with explicit
exponentially small error. y ≍ C·log(1/x)/x gives error O(x^C) — far below (G2)-relevant
powers. The two-sided condensation law now constrains the genuine Möbius–Laplace transform.

## Lean traps (tsum work)
- `set F : ℕ → ℝ := fun n => …` ⟹ `rw [hF]` FAILS on applied occurrences (no beta). Use
  `simp only [hF]`.
- AVOID `norm_tsum_le_tsum_norm` here — it triggered whnf timeouts (200k) with `set`-bound
  Finset `divisors` in context. Instead sandwich: −h ≤ g ≤ h pointwise, apply
  `Summable.tsum_le_tsum` twice, `rw [tsum_neg]`, then `abs_le`.
- `hasSum_sum_of_ne_finset_zero (h : ∀ b ∉ s, f b = 0) : HasSum f (∑ b ∈ s, f b)` gives BOTH
  the summability (`.summable`) and the tsum-equals-Finset-sum identity (`.tsum_eq`).
- `Summable.of_nonneg_of_le hnonneg hle hSummableMajorant` (majorant is the LAST arg).
- `Summable.sum_add_tsum_nat_add k : ∑ i ∈ range k, f i + ∑' i, f (i+k) = ∑' i, f i`.
- |μ n| ≤ 1: by_cases Squarefree; `moebius_apply_of_squarefree` then abs_pow/abs_neg, else
  `moebius_eq_zero_of_not_squarefree`.
