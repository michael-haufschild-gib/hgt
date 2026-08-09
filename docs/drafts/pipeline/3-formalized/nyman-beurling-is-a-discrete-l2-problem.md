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
