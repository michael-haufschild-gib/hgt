# Corpus owns a full sieve-theory layer (2026-08-03)

`formal/GaloisForLFunctions/RHTower/Sieve/` — 23 modules, namespace `RHTower.Sieve`, **all
unconditional** (`propext, Classical.choice, Quot.sound` only), all wired into
`GaloisForLFunctions/RHTower.lean`.

Before this date the corpus had **no sieve and no Mertens estimate**, and neither does mathlib:
`Mathlib/NumberTheory/SelbergSieve.lean` stops at the diagonalized Λ² quadratic form — no
optimized level, no fundamental lemma, no Brun–Titchmarsh; mathlib has **no** Bonferroni
inequality and **no** Mertens theorem (`rg -il mertens` hits only `RingTheory/.../ContentIdeal`).
The corpus's many `Mertens`-named modules are about `M(x)=∑μ(n)`, not `∑_{p≤x} 1/p`.

## Layers

**Sieve core** — `IntervalMultiples` (`card_filter_dvd_Ioc`, `abs_card_filter_dvd_Ioc_sub_lt`,
`cast_div_bounds`), `TruncatedMoebius` (`alternating_choose_partialSum`, exact truncated Möbius
value, both **Bonferroni** inequalities), `BrunPure` (`truncDivisors`, `card_coprime_Ioc_le`,
`le_card_coprime_Ioc`), `MainTerm` (`sum_divisors_moebius_div_eq_prod`, `card_truncDivisors`),
`TruncationDefect` (`sum_divisors_pow_card_primeFactors_div_eq_prod`, capstones
`card_coprime_Ioc_le_prod` / `prod_sub_le_card_coprime_Ioc`).

**Mertens** — `Mertens` (Chebyshev `∑_{p≤n} log p ≤ n log 4`, Euler/exp comparisons,
`primeFactors_primorial_eq`), `MertensFirst` (`mertensFirst_upper/lower`), `LogLogTelescope`
(`log_sub_log_le`, `le_log_sub_log`, `logLog`, `logLogIncrementSum`, `sum_Ico_telescope`),
`MertensSecond` (`mertensS`, `mertensS_eq_abel`, `mertensSecond_upper/lower`, constants
`mertensFirstConst`, `mertensSecondUpperConst`, `mertensSecondLowerConst`).

**Fundamental lemma** — `RoughCount` (`card_rough_Ioc_le`, `coprime_primorial_iff`).

**Smooth/rough** — `SmoothRough` (`smoothPart`, `roughPart`, `primeFactors_smoothPart`,
`pow_card_primeFactors_roughPart_le`), `SmoothSum` (`sum_smoothUpTo_le`, `sum_smoothWeight_le`),
`SmoothTilt` (`prod_one_add_mul_le_exp`, `sum_inv_pred_primesLE_le`,
`sum_smoothUpTo_card_le_inv_le_exp`), `SmoothCount`
(`card_smoothUpTo_card_primeFactors_le`).

**ω tails** — `OmegaTail` (`card_omega_le_le_sum`, `card_omega_le_le`: lower tail by fibring),
`OmegaMGF` (`card_divisors_filter_card_primeFactors_eq`, `sum_choose_omegaSmall_eq`,
`binomialPartial_sign`, `card_omegaSmall_ge_mul_pow_le`, `card_omegaSmall_le_mul_pow_le`),
`GeometricMeanDivisor` (`prod_pow_card_le_prod_pow_card`, `pow_prod_le_of_card_mul_le`),
`SmallestPart` (`smallestPart`, `exists_small_divisor`, `bigDivisors`, `card_omegaBig_ge_le`,
`sum_bigDivisors_inv_le`, `omegaSmall_add_card_filter`, `card_omega_ge_le_add`),
`OmegaUpperTail` (`card_omega_ge_le`), `LevelRegroup`
(`sum_pow_mul_sum_levelDivisors_inv`, `card_omega_ge_le_euler`, `card_omega_le_le_euler`),
`ChernoffTails` (`prod_one_sub_mul_primesLE_le`, `prod_one_add_bigPrimeSet_le`,
`card_omega_le_le_chernoff`, `card_omega_ge_le_chernoff`), `RateBridge`
(`pow_div_pow_eq_rate`, `card_omega_le_le_rate`, `card_omega_ge_le_rate`), `OmegaDeviation`
(`omegaDeviation`, `card_omegaDeviation_le`, `card_squarefree_omegaDeviation_le`).

## Four ideas that made this cheap

1. **Exponential tilt, not Maclaurin.** Truncation tails: discarded divisors have `ω d > r`, so
   `λ^r/d ≤ λ^{ω d}/d` and `∑_{d∣m} λ^{ω d}/d = ∏(1+λ/p)` is one `Finset.prod_add`. The same
   device reappears three more times (smooth sums, level sums, big-divisor sums). Never needed
   `j! e_j ≤ S^j`.
2. **No Stirling.** Mertens I needs only `n^n e^{−n} ≤ n! ≤ n^n`; the lower half is one term of
   `Real.sum_le_exp_of_nonneg`.
3. **No integral comparison.** Mertens II: concavity `(b−a)/b ≤ log b − log a ≤ (b−a)/a`
   sandwiches each term between consecutive increments of `log ∘ log`; the sum telescopes.
4. **Truncated factorial moments for the tails.** `[k ≤ w]·u^k ≤ ∑_{i≤k}C(w,i)(u−1)^i` keeps the
   divisor range bounded by the truncation level, so the `+1`-per-divisor sieve error stays
   `X^{o(1)}`. This is what the naive smooth/rough fibring cannot do for the upper tail.

## Key structural fact

`pow_div_pow_eq_rate` : at `m = w·log log z`, `(log z)^{w−1}/w^m = (log z)^{−I(w)}` with
`I(w) = RHTower.woldBreadthDeviationRate w = 1 − w + w log w`. One identity serves both tails
(lower has `w = t ≤ 1`, exponent `−(1−t) = t−1`; upper has `w = u ≥ 1`, exponent `u−1`).

## Traps

- `μ` needs `open scoped ArithmeticFunction.Moebius`; `Finset.sum_boole` does not resolve — use
  `Finset.natCast_card_filter`; `primorial*`, `squarefree_primorial`, `primeFactors_primorial`
  are **root-level**, not under `Nat.`; Legendre lemmas are `Nat.factorization_factorial*`;
  `sum_le_tsum` is `Summable.sum_le_tsum`; `ordProj`/`ordCompl` are camelCase.
- Identifiers `k₋`, `k₊` are **not valid Lean tokens** — use `kLow`, `kHigh`.
- State results in `logLog`, not unfolded `Real.log (Real.log _)`, and write `2 * (C / log 2)`
  not `2 * C / log 2`, so `linarith` keeps the atoms aligned.
- `add_le_add_right` in this mathlib adds on the **left**; prefer `linarith` with an explicit
  multiplied hypothesis.

## Owner card and the one open sharpening

`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/route-e-two-sided-off-normal-wold-breadth-transport.md`
— its `(6)`–`(9)` are now unconditional Lean theorems. The bounds come out as negative powers of
`log z`, and the sieve/counting constraints force `log z ≍ log X / log log X`, so `(7)`–`(8)` carry
an extra `(log log X)^{O(1)}` versus the literal statement. Harmless for the card's theorem, which
uses only `(9)` as `#E = o(H/log log X)`. Recovering the literal `(log X)^{−I(c)}` needs Shiu's own
largest-prime-factor induction with Brun–Titchmarsh in progressions — the one open sharpening.

## Second batch (same day): Brun–Titchmarsh made explicit, and the Hardy–Ramanujan engine

New modules under `formal/GaloisForLFunctions/RHTower/Sieve/`, all wired into `RHTower.lean`,
all `[propext, Classical.choice, Quot.sound]`:

| module | key theorem |
|-|-|
| `DivisorSquareSum.lean` | `card_coprime_Ioc_le_explicit` : `#{n ∈ (a,b] : (z#,n)=1} ≤ 2(b−a)/log Y + Y² e^{4c₁}(log z)^4` |
| `SelbergTail.lean` | `card_rough_Ioc_le_selberg`, `card_omega_le_le_selberg` |
| `LargeSmoothPart.lean` | `exists_divisor_mem_Ioc_of_smooth` (smooth `σ > M` has a divisor in `(M,Mz]`), `card_large_smoothPart_le` |
| `ShiuSharp.lean` | `card_omega_le_le_sum_restricted` (fibring cut at `M`), `card_omega_le_le_sharp` |
| `HardyRamanujanRecursion.lean` | `card_omegaLevel_mul_le` : `j·S_j(a,b) ≤ ∑_{q ≤ b} S_{j−1}(a/q,b/q)` |
| `HardyRamanujanCut.lean` | `card_omegaLevel_mul_le_cut` : same with `q ≤ Q` and `(j−R)` on the left, given `b < Q^{R+1}` |
| `PrimePowerSum.lean` | `sum_inv_primePowerSet_le` : `∑_{q=p^e ≤ b} 1/q ≤ mertensS b + 1` |
| `HardyRamanujanStep.lean` | `card_omegaLevel_step` : the recursion in `A·length + B` shape |

### Corrected diagnosis (important, supersedes the earlier note)

The `(log log X)^{1−c}` loss in the Shiu-type tail bound is **not** a level-of-distribution defect
of Brun's sieve.  No sieve by primes `≤ z` can beat density `1/log z` — the Selberg mass of the
interval sieve is `≤ ∏_{p≤z}(1+1/p) ≍ log z` for every level `Y`, and `Y ≤ z` is essential.  The
loss comes from bounding `t^{ω(rough part)} ≤ 1`; keeping that factor makes `log z` cancel exactly
and gives the literal `(log X)^{−I(t)}`.

### The viable route to the sharp bound

Hardy–Ramanujan recursion **with a cut**: choose `log Q = log b/(εj)` so `R = εj`; then the error
per step is `≍ Q = b^{o(1)}` (negligible against `b−a ≥ √b`) and the per-step loss `(1−ε)^{−1}`
compounds to `e^{O(1/t)}`, an absolute constant, when `ε = C/(t log log b)`.  Summing `j ≤ t log log b`
with the tilt gives `(b−a)(log b)^{−I(t)}/log log b`.  Remaining: base case `S_1` from
Brun–Titchmarsh + prime powers of exponent ≥ 2, and the numerical closing of the induction.

### Traps hit

- `Σ` is not a legal Lean identifier ("unexpected token").
- `rintro ⟨n,p⟩` leaves `⟨n,p⟩.fst` in hypotheses — `rw [Finset.mem_sigma]` keeps it, `simp only`
  reduces it; omega treats the unreduced form as a distinct atom.
- `set q := p ^ n.factorization p` makes later `have`s use the unfolded form; `rw [← hq]` before omega.
- `Nat.Ico_succ_right` does not exist on this toolchain; prove `Icc 1 L = Ico 1 (L+1)` by `ext; simp`.
- `positivity` cannot prove `p ^ e ≠ 0` for `p : ℕ` prime; use `pow_ne_zero _ hprime.pos.ne'`.
