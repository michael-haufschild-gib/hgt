# Littlewood Z4 opened: truncation keeping the partial sum intact (2026-08-06)

`formal/GaloisForLFunctions/RHTower/Sieve/ZetaPartialSumTruncation.lean` — built, wired, axioms
`[propext, Classical.choice, Quot.sound]`, zero warnings. Namespace `RHTower.Sieve`.

## Asset audit correction (the card was wrong)

The card said Z4's truncation would come from vendored `PNTPlus` (`Zeta0EqZeta`,
`riemannZeta0_apply`). **The corpus already owns it**: `Sieve/ZetaTruncated.riemannZeta_eq_sum_add_tail`
gives for `re w > 0`, `w ≠ 1`, `N ≥ 1`:
`ζ(w) = ∑_{k≤N} k^{−w} + N^{1−w}/(w−1) − w∫_N^∞ fract(x)x^{−w−1}dx`.

**The real gap**: the existing `norm_riemannZeta_le_truncated` applies `norm_sum_le` to the head,
replacing the complex sum by the sum of moduli — discarding all cancellation, so it can only ever
yield the trivial logarithmic size. Z3 bounds the *oscillating* sum, so the head must survive.

## Added

- `norm_riemannZeta_le_partialSum` :
  `‖ζ(w)‖ ≤ ‖∑_{k≤N} k^{−w}‖ + N^{1−re w}/‖w−1‖ + ‖w‖·(N^{−re w}/re w)`.
- `norm_riemannZeta_one_add_I_mul_le` (t > 0, N ≥ 1) :
  `‖ζ(1+It)‖ ≤ ‖∑_{k≤N} k^{−(1+It)}‖ + 1/t + ‖1+It‖/N`.

Tail terms are harmless at the Z3 truncation point: `N = 2^{topExponent t+1} − 1 ≈ 2(t/8π)³`, so
`‖1+It‖/N ≈ t/N → 0`. `Finset.Icc 1 N = Finset.Ico 1 (N+1)` matches the Z3 range exactly.

**Z4 now reduces to a cast/index reconciliation plus two vanishing terms.**

## Lesson

Before trusting a card's asset line, grep the corpus: the truncation existed, and the true obstacle
was a *lossy step inside an existing bound*, not a missing theorem. Cf.
[[mr-path-gap-status]] — "header gap notes in this corpus are unreliable".
