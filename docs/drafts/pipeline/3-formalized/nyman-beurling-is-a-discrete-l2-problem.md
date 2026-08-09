# The Nyman–Beurling criterion is a discrete ℓ² problem

Status: formalized (Lean, unconditional)
Date: 2026-08-09

## The observation

`BaezDuarteGramDiscrete` showed `bdGenReal (1/m) v = (⌊v⌋ mod m)/(m·v)`, and the target is `1/v`. Both have
the shape

`stepFun s : v ↦ s(⌊v⌋)/v`  for a bounded sequence `s : ℕ → ℝ`,

the generator with `s n = (n mod m)/m` and the target with `s ≡ 1`. Once that shape is developed once, the
integral disappears from the problem.

## What is proved

`RHTower/StepFunctionCarrier.lean`:

* `stepFun`, `memLp_stepFun`, `stepVec` — bounded sequences embed in the carrier;
* **`hasSum_stepGram` — `⟪stepFun s₁, stepFun s₂⟫ = ∑_{n≥1} s₁(n)·s₂(n)/(n(n+1))`**, and `inner_stepVec`
  identifying the carrier inner product with it.  So the step subspace is `ℓ²(ℕ≥1, w)` with the *rational*
  weights `w_n = 1/(n(n+1))`;
* `bdGen_eq_stepVec`, `bdTarget_eq_stepVec`, `bdGen_bdDiscrete_eq_stepVec` — the Báez-Duarte data are step
  vectors: the generators are the modular sequences, the target is the constant sequence `1` (whose norm is
  `∑1/(n(n+1)) = 1`, matching `norm_bdTarget`);
* **`riemannHypothesis_of_constStep_mem_closedSpan`** — if the constant sequence lies in the closed span of
  the modular sequences, the Riemann hypothesis holds.

`hasSum_stepGram` subsumes both earlier series computations: `hasSum_bdGram_discrete` is the case of two
modular sequences and `hasSum_pairing_discrete` the case of a modular sequence against the constant one.
(Those were proved directly first; this is the law they are instances of.)

## Why it matters

The criterion now reads, with no integral, no measure theory and no zeta function in the statement:

> **RH holds if the constant sequence `1` lies in the closed span of `{n ↦ (n mod m)/m : m ≥ 1}` in
> `ℓ²(ℕ≥1, 1/(n(n+1)))`.**

Every object in that sentence is elementary arithmetic. This is the endpoint of the reduction begun in
`nyman-beurling-carrier-no-hardy-space.md`: the analytic scaffolding (Mellin transforms, detectors, the
Hardy-space wall, the Gram integrals) has all been discharged, and what is left is a statement about
approximating a constant sequence by modular sequences in a weighted `ℓ²` space with rational weights.

Two honest caveats. The statement is *equivalent* to RH, so being elementary does not make it easy — the
difficulty has moved, not shrunk. And the sufficient direction is the only one proved; nothing here says the
approximation is possible.

## Addendum (same day): a second, arithmetic obstruction

`RHTower/ArithmeticEvaluationObstruction.lean`. In the discrete picture a second obstruction mechanism
appears, of the same *shape* as the Mellin detector but arithmetic rather than analytic.

The modular sequence `g_m` vanishes exactly on the multiples of `m`. So if `n₀` is divisible by every modulus
of a family, the functional "evaluate the sequence at `n₀`" annihilates every generator while on the target
it is `1/(n₀(n₀+1)) ≠ 0`. Evaluation is bounded because it *is* an inner product — with `δ` the indicator
sequence at `n₀`, `hasSum_stepGram` collapses to a single term:

* `stepGram_deltaSeq` — `⟪stepVec δ, stepVec s⟫ = s(n₀)/(n₀(n₀+1))`;
* `norm_sq_stepVec_deltaSeq` — `‖stepVec δ‖² = 1/(n₀(n₀+1))`;
* `notMem_closedSpan_of_forall_dvd` — the target is not in the closed span of any family of moduli with a
  common multiple;
* `dist_floor_of_forall_dvd` — quantitatively, `dist ≥ √(1/(n₀(n₀+1)))`.

Taking `n₀ = lcm` of a finite section, **every finite-section Báez-Duarte distance is strictly positive**:
the approximation in `d_N → 0` is asymptotic and never exact, for a purely divisibility reason.

This does not threaten the criterion: for the *infinite* family no `n₀` is divisible by every modulus, so the
argument does not reach the full span. And the bound is worthless quantitatively — with `n₀ = lcm(1..N) ≈ e^N`
it gives `d_N ≳ e^{-N}` against the true `≍ 1/√(log N)`. Its value is structural: the same
"bounded functional kills the family but not the target" mechanism that produced the zero-based floor also
runs on pure divisibility, with no zeta input at all.

## Addendum 2 (same day): the first constructive input

Everything on this lane so far has been an obstruction. `RHTower/MoebiusApproximantResidual.lean` supplies
the other side, and it reuses a result the corpus already had:
`MoebiusFloorSummatory.moebius_floor_summatory` (`∑_{d ≤ N} μ(d)⌊N/d⌋ = 1`).

* `moebius_floor_summatory_le` — the same at an inner point, `∑_{d ≤ N} μ(d)⌊n/d⌋ = 1` for `1 ≤ n ≤ N`
  (terms with `d > n` vanish);
* `modSeq_eq_sub_floor` — `g_d(n) = n/d − ⌊n/d⌋`;
* **`sum_moebius_modSeq` — `∑_{d ≤ N} μ(d)·g_d(n) = n·M₁(N) − 1` for `1 ≤ n ≤ N`**, where
  `M₁(N) = ∑_{d ≤ N} μ(d)/d`;
* **`moebius_residual_eq` — `1 − ∑_{d ≤ N}(−μ(d))·g_d(n) = n·M₁(N)`**: the combination with coefficients
  `−μ(d)` reproduces the target sequence on all of `[1,N]` up to `n·M₁(N)`;
* `abs_moebius_residual_le` — the residual is `≤ n`, from the corpus's `abs_sum_moebius_div_le_one`.

What this does and does not give. It is the exact starting point for analysing any coefficient choice, and it
identifies the single quantity that controls the undamped approximant: `M₁(N)`, whose vanishing is equivalent
to the prime number theorem — which the corpus proves twice (`RHTower/Sieve/ChebyshevPNT.lean` and the
vendored `PNTPlus`), so supplying `M₁(N) → 0` is a follow-up rather than a new obstacle. But even with
`M₁(N) → 0` the residual grows linearly in `n` while the weights decay like `1/n²`, so the undamped Möbius
approximant does **not** converge. The classical remedy is Vasyunin-type damping of the coefficients; this
identity is what any such analysis starts from.

## Addendum 3 (same day): the residual off the range

The previous addendum's identity holds on `[1,N]`, where `moebius_floor_summatory` evaluates the floor sum to
`1`. `RHTower/TruncatedMoebiusResidual.lean` removes that restriction and identifies what replaces the `1`.

* `moebius_residual_eq_general` — for **every** `n`,
  `1 − ∑_{d ≤ N}(−μ(d))·g_d(n) = 1 − F_N(n) + n·M₁(N)`,  `F_N(n) = ∑_{d ≤ N} μ(d)⌊n/d⌋`.
  (No hypothesis on `n`: the `n ≤ N` restriction was only used to evaluate `F_N`, and the case `n = 0` is
  degenerate on both sides.)
* `truncMoebiusDivisorSum N k = ∑_{d ∣ k, d ≤ N} μ(d)` — the **truncated Möbius divisor sum**;
* `sum_moebius_floor_eq_sum_trunc` — counting multiples of `d` in `[1,n]` and swapping the summation order,
  `F_N(n) = ∑_{k ≤ n} truncMoebiusDivisorSum N k`;
* `truncMoebiusDivisorSum_of_le`, `sum_trunc_eq_one_of_le` — below the truncation the sum is the ordinary
  Möbius divisor sum, hence `[k = 1]`, which recovers `F_N(n) = 1` for `n ≤ N` and the previous residual.

So the convergence question for any Möbius-type approximant is exactly: **how large is
`∑_{k ≤ n} truncMoebiusDivisorSum N k` for `n > N`?** That is the Selberg-sieve truncation object. Naming it
is all this file does — the crude bound `|truncMoebiusDivisorSum N k| ≤ d(k)` gives `F_N(n) ≪ n log n`, which
is useless here, and no estimate is attempted.

## Addendum 4 (same day): the residual is the omitted moduli

There is a shorter exact form than Addendum 3's. Splitting `moebius_floor_summatory`'s range at `N`
(`sum_moebius_floor_tail`: `∑_{d ≤ N} μ(d)⌊n/d⌋ = 1 − ∑_{N < d ≤ n} μ(d)⌊n/d⌋`, with the `N = 0`, `N ≥ n` and
`0 < N < n` cases all handled) gives

**`moebius_residual_tail_form` — `1 − ∑_{d ≤ N}(−μ(d))·g_d(n) = ∑_{N < d ≤ n} μ(d)⌊n/d⌋ + n·M₁(N)`.**

So the residual is governed entirely by the moduli the approximant *omitted*, plus the linear Mertens term —
no truncated divisor sums needed. `moebius_residual_tail_form_of_le` recovers `n·M₁(N)` for `n ≤ N`, where the
tail is empty. This supersedes Addendum 3's expansion as the working form (the truncated divisor sum remains
the right object if one wants to see the residual pointwise in `k` rather than summed).

The classical tension is now visible in one line: enlarging `N` shrinks `M₁(N)` (the prime number theorem) but
the tail sum starts at `N`, and the trivial bound `|∑_{N<d≤n} μ(d)⌊n/d⌋| ≤ n log(n/N)` is far too lossy.
Balancing the two is exactly what Vasyunin-type damping of the coefficients is for. Nothing is estimated here.
