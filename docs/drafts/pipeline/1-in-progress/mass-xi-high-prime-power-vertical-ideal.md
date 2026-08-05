# Mass–Xi high-prime-power vertical ideal

## Status

- Lane: `1-in-progress`
- Conjecture: `C31` — Lean scratch proof complete; corpus audit pending
- Target: `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3 exact open core
- Lean target: `formal/GaloisForLFunctions/RHTower/XiMassPrimePowerVerticalIdeal.lean`

## Exact conjecture

Let `g_τ = xiMassAnalyticTest a τ`, with `a>0`, `τ=σ+iu`, `σ>0`. Reindex the
depth-erased centered source atoms by prime powers `p^r`. Then:

1. the critical weights of all valuation depths `r≥3` are summable,
2. their centered atoms are absolutely summable,
3. their total norm has one bound independent of vertical time `u`, and
4. the literal bottom source decomposes exactly as prime layer + square layer + `r≥3` tail.

In formulas, with

```text
H_a(τ) = ∑' (p,k), centeredAtom(a,τ,p^(k+3)),
W(p,k) = ‖LSeries.term Λ (1/2) (p^(k+3))‖,
```

the target bound is

```text
‖H_a(σ+iu)‖ ≤ (∑' (p,k), W(p,k)) · ∫ exp(-σ|x|) dx,
```

and the right side is finite and independent of `u`.

## Attack

Use exact critical weight

```text
W(p,k) = log(p) · p^(-(k+3)/2).
```

Split valuation parity. Even depths reduce to a geometric family with prime base exponent `3/2`;
odd depths reduce to base exponent `2`. Both outer prime sums converge because their exponents are
strictly larger than one. Combine this arithmetic theorem with the uniform `L¹` bound of the mass
test's strip Fourier transform, then reindex the von-Mangoldt support and split the first two
valuation layers exactly.

## Failure criteria

- Parity reindex does not produce a genuinely summable prime majorant.
- Fourier bound retains `u` dependence.
- Exact source reassembly requires a conditional rearrangement.
- Result merely renames the full atom series without removing a cofinal sector.

## Scientific value if proved

This is not an `ℓ¹` reproof of the entropy wall. It classifies the only valuation layers capable of
RH-strength vertical growth: primes and prime squares. Every exponent `r≥3` belongs to a bounded
vertical ideal and can be removed from §9.3 without asymptotic loss.

## Log

- 2026-08-05 — C31 proposed from C30 depth erasure; scratch Lean proof established exact
  prime/square/high decomposition and a vertical-uniform bound for the entire `r≥3` sector.
