# Möbius Mertens finite-section energy closure

- **ID:** `mobius-mertens-finite-section-energy-closure`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / LEAN TARGET
- **Source:** whole-corpus synthesis of `MobiusMertensLittlewood.lean`, finite Abel summation,
  and `MobiusLaplaceMellinPlancherelBridge.lean`

## Target

Prove unconditionally as a theorem schema

```text
RH → MobiusLaplaceCofinalFiniteSectionEnergyBounded.
```

Consequently close exact RH equivalences for uniform finite Gamma--Hankel sections, one-sided
off-diagonal Gamma--Hankel covariance, and its bounded-return weakening.

## Paper proof

Fix `1/2 < theta < sigma`. Littlewood gives `|M(N)| ≤ C(N+1)^theta`. Finite Abel summation gives,
uniformly in cutoff `N`,

```text
|sum_(n≤N) mu(n)e^(-nx)| ≤ K x^(-theta),       0 < x ≤ 1.
```

Endpoint term uses boundedness of `y^theta e^(-y)`; difference term uses
`1-e^(-x) ≤ x` and the existing real-power exponential-moment estimate. For `x ≥1`, the
absolute geometric majorant is `O(e^(-x))`, uniformly in `N`.

After `x=e^(-u)`, finite logarithmic Mellin sections therefore admit one cutoff-independent
square-integrable envelope:

```text
O(e^(-(sigma-theta)u))  on u≥0,
O(e^((m-sigma)u))       on u≤0, for any integer m>sigma.
```

Thus their `L²` norms have a common finite ceiling. Choosing `theta` and `sigma` cofinally above
`1/2` proves target.

## Corpus/novelty boundary

- Exact finite-section/Gamma--Hankel equivalence and Fatou direction already formalized.
- RH-to-Mertens direction is now formalized in `MobiusMertensLittlewood.lean`.
- No existing theorem found transferring Mertens cancellation uniformly to all finite logarithmic
  sections.
- This is a connector theorem, not claim of external priority.

## Status

- [x] corpus search
- [x] dependency-closed paper proof
- [ ] Lean formalization
- [ ] targeted audit and axiom check
