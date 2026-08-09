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
