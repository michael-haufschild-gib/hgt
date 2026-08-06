# Mertens' theorems with an exponential error term

**Status:** in progress.
**Depends on:** `RHTower/Sieve/ChebyshevThetaBigO.lean` (`chebyshevTheta_sub_id_isBigO`).

## The claim

The corpus already owns Mertens' second theorem with a decaying error
(`RHTower/Sieve/MertensSecondSharp.lean`):

```
|mertensS N − logLog N − meisselMertensConst| ≤ (2·mertensFirstConst + 1/2) / log N .
```

With `θ(x) = x + O(x·exp(−c√(log x)))` now available, the error improves to
`exp(−c′√(log N))` — faster than every power of `1/log N`.

## Why `1/log N` is not the truth

The corpus proof bounds the Mertens-first remainder by a constant,
`|mertensA i − log i| ≤ mertensFirstConst`, and that constant is then charged to the error.
But the true statement is

```
mertensA x = log x + c₁ + ε(x),        ε(x) → 0 fast,
```

and in the summation by parts `c₁` appears **twice with opposite signs**: once in the boundary
term `mertensA(N)/log N = 1 + c₁/log N + …`, and once in
`∑_{i<N} c₁·invLogVar i = c₁·(1/log 2 − 1/log N)`.  The two `c₁/log N` cancel exactly, leaving only
the genuinely decaying `ε`.

This is the corpus's own recorded lesson — *constants must telescope, not add* — one level up from
where it was first recorded (`mertens-decaying-error`).  Charging `c₁` to the error is what pins the
bound at `1/log N`; it is not slack in the estimate, it is a lost cancellation.

## Route

**Step 1 — the tail brick** (`RHTower/Sieve/SqrtLogTailIntegral.lean`).
An explicit antiderivative removes any need for a change of variables:

```
G(t) = (2/c²)·(1 + c√(log t))·exp(−c√(log t)),      G′(t) = −exp(−c√(log t))/t .
```

So `∫_x^∞ exp(−c√(log t))/t dt = G(x)`, and `G(x) ≤ B·exp(−(c/2)√(log x))` because
`1 + c√L ≤ B·exp((c/2)√L)`.  This also supplies integrability on `Ioi 2`, hence the convergence of
every constant below.

**Step 2 — Mertens first with a rate** (`RHTower/Sieve/MertensFirstExpRate.lean`).
mathlib's `sum_mul_eq_sub_integral_mul₁` with `c k = if k.Prime then log k else 0` and `f t = 1/t`
gives, with no new summation-by-parts work,

```
mertensA ⌊b⌋ = θ(b)/b + ∫_{(2,b]} θ(t)/t² dt .
```

Substituting `θ(t) = t + E(t)`:

```
mertensA x − log x = (1 − log 2) + E(x)/x + ∫_2^x E(t)/t² dt ,
```

so `c₁ := (1 − log 2) + ∫_2^∞ E(t)/t² dt` exists and

```
|mertensA x − log x − c₁| ≤ |E(x)|/x + ∫_x^∞ |E(t)|/t² dt = O(exp(−c′√(log x))) .
```

**Step 3 — the second theorem** (`RHTower/Sieve/MertensSecondExpRate.lean`).
Feed step 2 into the corpus's own decomposition (`mertensS_decomposition`,
`sum_range_mertensRemTerm`, `logLogIncrementSum_eq`), tracking the `c₁` cancellation described
above.  The constant is pinned to `meisselMertensConst` by uniqueness of limits against the
corpus's `abs_mertensS_sub_logLog_sub_const_le`, so the sharp form is stated with the corpus's own
constant rather than a fresh existential.

## Assets that must not be rebuilt

- `Nat.primesLE`, `Chebyshev.theta_eq_sum_primesLE_log`, `Chebyshev.theta_eq_theta_coe_floor`.
- mathlib `Mathlib/NumberTheory/AbelSummation.lean` — `sum_mul_eq_sub_integral_mul₁` is the exact
  shape needed (`c 0 = c 1 = 0`, integral over `Ioc 2 b`).
- `RHTower/Sieve/MertensSecond.lean` — `mertensA`, `mertensS`, `mertensFirstConst`.
- `RHTower/Sieve/MertensSecondSharp.lean` — `invLogVar`, `mertensRemTerm`, `logLogDefect`,
  `mertensS_decomposition`, `meisselMertensConst`.
- `RHTower/Sieve/LogLogTelescope.lean` — `logLog`, `logLogIncrementSum`.
- `RHTower/Sieve/SqrtLogDecayIntegral.lean` — `exists_bound_setIntegral_sqrt_log_decay`,
  `sqrt_log_sqrt_le`; `ChebyshevThetaBigO.sqrt_mul_log_le_shape`.

mathlib has **no** Mertens theorem of either kind — `Mathlib/NumberTheory/SumPrimeReciprocals.lean`
proves only divergence.

## Progress

**Step 1 — done.** `RHTower/Sieve/SqrtLogTailIntegral.lean`, unconditional:

```
sqrtLogTail c t          = 2/c² · (1 + c√(log t)) · exp(−c√(log t))
hasDerivAt_neg_sqrtLogTail : HasDerivAt (fun x => −sqrtLogTail c x) (exp(−c√(log t))/t) t
integrableOn_expSqrtLog_div_Ioi : IntegrableOn (fun t => exp(−c√(log t))/t) (Ioi a)      (1 < a)
integral_expSqrtLog_div_Ioi     : ∫ t in Ioi a, exp(−c√(log t))/t = sqrtLogTail c a
sqrtLogTail_le                  : sqrtLogTail c t ≤ 4/c² · exp(−(c/2)√(log t))
```

The antiderivative makes `integrableOn_Ioi_deriv_of_nonneg` and
`integral_Ioi_of_hasDerivAt_of_tendsto` do all the work — no change of variables, no comparison
test, and the improper integral is an *equality*, not an estimate.

**Step 2 — done.**

`RHTower/Sieve/MertensFirstAbel.lean`:

```
mertensA_eq_theta_div_add_setIntegral (hb : 2 ≤ b) :
  mertensA ⌊b⌋₊ = θ(b)/b + ∫ t in Ioc 2 b, θ(t)/t²
```

compiled on the first attempt — mathlib's `sum_mul_eq_sub_integral_mul₁` is the exact shape, with
`primeLogCoeff 0 = primeLogCoeff 1 = 0` discharging its two hypotheses (neither `0` nor `1` is
prime) and `Chebyshev.theta_eq_sum_Icc` identifying the partial sums.

`RHTower/Sieve/MertensThetaErrorIntegral.lean`: `thetaErrorDensity t = (θ(t) − t)/t²` is integrable
on `(2,∞)`.  `θ` is **monotone**, which gives both halves cheaply — `Monotone.measurable` for the
domination argument on the tail, `MonotoneOn.integrableOn_isCompact` for the initial segment.  Going
through PNTPlus's `chebyshev_asymptotic''` for integrability, as the `π` chain did, is unnecessary
here.

`RHTower/Sieve/MertensFirstExpRate.lean`:

```
exists_mertensA_sub_log_exp_rate :
  ∃ c₁ B c, 0 < c ∧ 0 ≤ B ∧ ∀ᶠ x in atTop,
    |mertensA ⌊x⌋₊ − log x − c₁| ≤ B · exp(−c·√(log x))
```

This already strictly refines the corpus's `abs_mertensA_sub_log_le`, which only bounds
`|mertensA N − log N|` by the constant `mertensFirstConst`: the constant `c₁` is now *identified*
(as `1 − log 2 + ∫_{(2,∞)} (θ(t)−t)/t² dt`) and what is left decays faster than every power of
`1/log x`.

All `#print axioms` are `[propext, Classical.choice, Quot.sound]`.

**Step 3 — next.** The second theorem, via the `c₁` cancellation.

**Step 3 — done.**

`RHTower/Sieve/MertensDefectTail.lean`:

```
logLogDefect_le_div       : logLogDefect i ≤ (1/i)·invLogVar i
tsum_logLogDefect_add_le  : ∑_{i≥N} logLogDefect i ≤ (1/N)·(1/log N)
```

The corpus's `logLogDefect_le` relaxes the same factor `log(i+1) − log i` to `1/2`, which is enough
for summability and throws the whole decay away.  Its own proof already establishes `≤ 1/i`
(`hstep`); keeping that instead of weakening it to `1/2` is the entire content here.

`RHTower/Sieve/MertensSecondExpRate.lean`:

```
mertensS_sub_logLog_sub_const_eq (hN : 2 ≤ N) :
  mertensS N − logLog N − meisselMertensConst
    = (mertensA N − log N)/log N + ∑_{i≥N} logLogDefect i − ∑_{i≥N} mertensRemTerm i

tsum_mertensRemTerm_add_eq (hN : 2 ≤ N) (c₁) :
  ∑_{i≥N} mertensRemTerm i
    = c₁·(1/log N) + ∑_{i≥N} invLogVar i · (mertensA i − log i − c₁)

exists_mertensS_sub_logLog_sub_const_exp_rate :
  ∃ B c, 0 < c ∧ 0 ≤ B ∧ ∀ᶠ N in atTop,
    |mertensS N − logLog N − meisselMertensConst| ≤ B·exp(−c·√(log N))
```

**The constant is the corpus's own `meisselMertensConst`** — this is a strict refinement of
`abs_mertensS_sub_logLog_sub_const_le`, not a parallel statement with a fresh existential.

The cancellation is visible in `tsum_mertensRemTerm_add_eq`: it emits `c₁·(1/log N)` because
`∑_{i≥N} invLogVar i = 1/log N` exactly (`tsum_invLogVar_add`), and the decomposition *subtracts*
this tail, while `(mertensA N − log N)/log N = c₁/log N + …` *adds* it.  After `hfrac` and `hsplit`
the whole `c₁` disappears by `ring`.

All `#print axioms` are `[propext, Classical.choice, Quot.sound]`; the RHTower umbrella builds.

## Lean notes

- `tsum_le_tsum` is gone; the comparison is `Summable.tsum_mono hf hg h`.
- `∑' i, f (i + N)` forces the cast `Real.log ↑(i + N)`.  Writing `Real.log (i + N)` in a statement
  elaborates to `Real.log (↑i + ↑N)`, which then fails to unify with `summable_nat_add_iff`'s
  output.  Write `Real.log ((i + N : ℕ) : ℝ)`.
- `Summable.norm_tsum_le_tsum_norm_of_le` does not exist; use `norm_tsum_le_tsum_norm` plus
  `Summable.tsum_mono`, with the summability of the norms from `Summable.of_nonneg_of_le`.
- `rw [...] at *` rewrote the hypotheses out from under the goal in `one_div_le_exp_neg_sqrt_log`;
  the fix was a `calc` through `exp 0 ≤ exp(log x − c√(log x))`.
