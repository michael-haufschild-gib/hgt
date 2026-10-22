# Mangoldt log-Haar capacity

## Status

In progress. Exact literature theorem identified; Lean dependency audit and proof compression underway.

## Target

Discharge the zero-parameter interface

```lean
RHTower.MangoldtLogHaarCapacity
```

from source data, yielding an unconditional theorem

```lean
theorem mangoldtLogHaarCapacity_holds : MangoldtLogHaarCapacity
```

and unconditional versions of every sharp Suzuki transport consumer.

After unfolding, the mathematical core is

\[
\sum_{d\le n}\frac{\Lambda(d)}d\le \log n\qquad(n\ge1).
\]

## Prior-corpus audit

- `RHTower.Mertens.mertens_first` gives only
  `|∑ Λ(d)/d - log n| ≤ log 4 + 4`.
- `Mathlib.NumberTheory.Chebyshev` gives
  `ψ(x) ≤ (log 4 + 4)x` and
  `ψ(x) ≤ log 4*x + 2*sqrt(x)*log(x)`, neither implies the target.
- `RHTower.CreaseBudgetPrimeMass.mertens_first_upper` concerns the prime-only sum and has an additive constant.
- `RHTower.PsiRemainderHarmonicSum` contains the needed discrete Abel identity but only a coarse remainder bound.
- No existing theorem in `formal/`, formalized pipeline cards, or mathlib states the target or Hanson's required `ψ(x) ≤ x log 3`.

## Primary source

Olivier Ramaré and Sebastian Zúñiga-Alterman,
*Möbius function and primes: an identity factory with applications*,
arXiv:2312.05138v3, Theorem 1.3 and Appendix A.

The source proves the real-cutoff statement for every `X ≥ 1`. Its proof writes

\[
\sum_{n\le X}\frac{\Lambda(n)}n=\log X+f(X)
\]

using the paper's integral identity, integrated Stirling formula, a signed fractional-part kernel, Hanson's inequality `ψ(X) ≤ X log 3`, and the exact negative-kernel mass `(1-γ)/2`. It proves `f(X)<0` for `X≥12`, then checks the finitely many jump points below 12.

## Formalization strategy

1. Search for a shorter published proof and existing Lean equivalents of every source lemma.
2. Prefer a natural-cutoff discrete compression of Appendix A; avoid rebuilding real-cutoff machinery that the RHTower consumer does not need.
3. If compression fails, formalize source dependencies as named reusable theorems:
   - Hanson Chebyshev bound;
   - identity-factory summation law;
   - signed fractional-part kernel bound;
   - exact small-cutoff closure.
4. Prove `mangoldtLogHaarCapacity_holds`.
5. Remove `hcap : MangoldtLogHaarCapacity` from all downstream sharp-cell and sharp-transport public interfaces by adding unconditional wrappers, preserving compatibility lemmas only where useful.
6. Audit axioms and wire the module through `GaloisForLFunctions.RHTower`.

## Constraints

- No numerical experimentation or floating-point certification.
- Any finite endpoint closure must use exact symbolic logarithm/product inequalities.
- No new axioms, opaque declarations, `sorry`, `admit`, or `unsafe`.
- Reuse current corpus definitions and identities rather than duplicating them.

