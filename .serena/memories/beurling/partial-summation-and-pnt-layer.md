# Beurling: partial summation, PNT consequences, transition asymptotic

The Route E Beurling firewall card is **fully formalized** and now lives in
`docs/drafts/pipeline/3-formalized/route-e-beurling-local-axiom-firewall.md`
with companion `...-formalized.md`.

## What is corpus-owned now (do not rebuild)

`RHTower.BeurlingSystemPartialSummation`
- `primeCount` / `primeCountLt` (`Set.ncard` of the norm balls), `HasPrimePNT`, `primeWindow`.
- `finite_primeBall` — primes inject into integers by `p ↦ {p}`, so `IsDiscrete` transfers.
- `sum_labelNorm_weight` — partial summation over ANY finite family of labels.
- `sum_primeWindow_eq_sub_sub_integral` — the Abel identity
  `∑_{Y<|p|≤X} f(|p|) = π(X)f(X) − π(Y)f(Y) − ∫_Y^X f'(t)π(t)dt`.
- `intervalIntegrable_mul_of_bounded` / `..._mul_primeCount` — bounded measurable multipliers.

`RHTower.BeurlingSystemPrimeSumAsymptotic`
- `pntError` (`π(t)log t/t − 1`), `primeCount_eq_mul` (`π = (t/log t)(1+E)`), `tendsto_pntError`,
  `integrableOn_pntError`.
- `tendsto_primeRpowSum` — `∑_{2<|p|≤X}|p|^{a-1} ~ X^a/(a log X)` for every `a > 0`.

`RHTower.BeurlingSystemMertensWindow`
- `hasDerivAt_logLog`, `integral_invDivLog` (iterated-log primitive), `log_log_rpow_sub`.
- `tendsto_primeCount_div` (`π(t)/t → 0`).
- `tendsto_primeInvWindowSum` — `∑_{X^{1/u}<|p|≤X}|p|^{-1} → log u`.

`RHTower.BeurlingSystemTransitionAsymptotic`
- two-sided `eventually_primeCount_le` / `eventually_le_primeCount` / `..._le_two_mul`.
- `integral_linear_exp` (primitive `−(u/t+1/t²)e^{−(u−1)t}`), `sum_primeWindow_exp_le`,
  `largeTail_le`, `le_largeTail`.
- `tendsto_largeTailBound`, `tendsto_primeCountWindow`, `tendsto_rpow_div_log_atTop`,
  `nonempty_largeLabel`.
- `tendsto_transition_ratio` = `(BF8)`: `z τ_z / log z → 1` for ANY `τ` with `τ_z>0` and
  `largeTail z (τ_z) = 1`.  Stated over an arbitrary transition function — no choice needed.

`HTGeometry.LogWeightedRpowIntegral`
- NEW `tendsto_logKernelRemainder`: `g → 0` and `|K t| ≤ C·t^(a-1)/log t` give
  `(∫_2^x g K)·(a log x)/x^a → 0`.  The private `tendsto_abelRemainder` of
  `RHTower.PrimeRpowSumAsymptotic` is now one line on top of it.

## Traps hit

- The crude layer bound `∑_g e^{−x|g|} ≲ C/x²` (what `summable_expNegNorm` gives) is NOT sharp
  enough for the `(BF8)` upper bound — it only reaches `c > 2`.  Partial summation against `π_P`
  reaches every `c > 1`.  Do not try to bound the prime tail by the integer tail.
- Bounding a tsum over the subtype `{p // z < |p|}` by window sums: use `Real.tsum_le_of_sum_le`
  (needs only nonnegativity), map the finite subset with `Finset.sum_image` (pin the summand with
  `(f := ...)`, higher-order unification fails otherwise), and kill the `X`-boundary term with
  `ge_of_tendsto` — not with a uniform bound, which does not exist.
- `Set.indicator_of_mem h` unifies `h : t ≤ c` as `Real.le t ∈ ...`; always write
  `(show t ∈ {x | x ≤ c} from h)`.
- `intervalIntegral.integral_indicator` is stated with `{x | x ≤ a₂}`, not `Set.Iic a₂`; pass
  `(s := {x : ℝ | x ≤ ...})` explicitly when supplying the measurability side condition.
- `div_le_div_iff` is now `div_le_div_iff₀`.
