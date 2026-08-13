# Polynomial-Gaussian global completed-source envelope

- **ID:** `polynomial-gaussian-global-completed-source-envelope`
- **Stage:** 3 — formalized in Lean 4
- **Route:** U, parabolic degree horizon
- **Scientific status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:** `mass-shifted-parabolic-degree-horizon`, PDH.7
- **Lean artifact:** `formal/GaloisForLFunctions/RHTower/PolynomialGaussianGlobalCompletedSourceEnvelope.lean`
- **Axiom audit:** only `propext`, `Classical.choice`, `Quot.sound`

## Exact claim

For every real polynomial `Q`, every `t>0`, and

```text
M_Q(t) = integral_R |Q(x^2)|^2 exp(-t*x^2) dx,
C_Lambda = sum_n Lambda(n) n^(-2),
```

the literal complete half-density prime tail is summable and satisfies

```text
sum_n Lambda(n)/sqrt(n) * |Fhat_(Q,t)(log n)|
  <= C_Lambda * M_Q(t) * exp(8*(natDegree(Q)+t)).            (GSE.1)
```

Consequently the exact polynomial-square Xi heat trace satisfies

```text
(gammaHardyPhaseRate(0)
    - C_Lambda * exp(8*(natDegree(Q)+t))) * M_Q(t)
  <= pi * xiPolynomialGaussianHeatTraceReal(Q,t).           (GSE.2)
```

All quantifiers are unconditional. No zero-location premise, coefficient norm, shell count,
numerical estimate, asymptotic hypothesis, or nonzero-polynomial premise occurs.

## Conjecture--attack--proof loop

Inherited PDH.7 used logarithmic integer shells to obtain an unspecified
`exp(O(natDegree(Q)+t))` source envelope. The stronger conjecture was that the existing Dirichlet
mass `sum Lambda(n)n^(-2)` pays the unrestricted tail directly.

For every real `xi`, two completed squares give

```text
-xi^2/(4t) + 2*sqrt(d)*xi/sqrt(t)
  <= 8*d + 8*t - 2*xi.                                    (GSE.3)
```

The coefficient-uniform Fourier aperture bounds the Fourier transform by the exponential of the
left side times `M_Q(t)`. At `xi=log n`, the right side factors as
`exp(8*(d+t))*n^(-2)`. The half-density divisor only decreases the term because `sqrt(n)>=1` for
`n>=2`; the `n=0,1` terms vanish. Termwise domination by the summable von-Mangoldt Dirichlet
series proves `(GSE.1)` and literal source summability.

For `(GSE.2)`, the exact polynomial-Gaussian completed-source formula splits the trace into Gamma,
polar, and prime terms. The existing every-radius Gamma envelope at radius zero gives
`gammaHardyPhaseRate(0)*M_Q(t)`; the polar square is nonnegative; the real prime source is bounded
by `(GSE.1)`. Combining these inequalities proves the result.

Hostile checks:

- `Q=0` gives equality-compatible bounds and requires no mass division.
- Constant polynomials have degree zero; the completed-square proof still applies.
- Arbitrarily large heat time is covered by the explicit `exp(8t)` cost.
- No prime number theorem or hidden shell cardinality is used.
- `(GSE.2)` can be negative and therefore does not assert global trace positivity.

## Formal theorem surface

- `RHTower.summable_routeUPolynomialGaussianPrimeGlobalAbsoluteTail`
- `RHTower.routeUPolynomialGaussianPrimeGlobalAbsoluteTail_le`
- `RHTower.re_routeUPolynomialGaussianPrimeSource_le_globalAbsoluteTail`
- `RHTower.pi_mul_xiPolynomialGaussianHeatTraceReal_ge_globalEnvelope`

Direct `lake env lean` and named
`lake build GaloisForLFunctions.RHTower.PolynomialGaussianGlobalCompletedSourceEnvelope` pass.
The module is imported by `GaloisForLFunctions/RHTower.lean`. Repository lint reaches this module
but currently fails on unrelated concurrently present modules missing from the same umbrella.

## Frontier delta

PDH.7 and the literal completed-source explicit-formula assembly are now Lean-closed. Remaining
parabolic step is scalar and exact: combine ultraviolet wedge positivity with `(GSE.2)` under the
filtered Gamma clock and prove degree-uniform incomplete-Gamma tail domination. This card proves
neither the parabolic positivity horizon nor RH by itself.
