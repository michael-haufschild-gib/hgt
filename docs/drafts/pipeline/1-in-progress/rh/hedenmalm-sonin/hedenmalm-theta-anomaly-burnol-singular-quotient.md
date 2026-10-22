# Hedenmalm theta anomaly--Burnol singular quotient

- **ID:** `hedenmalm-theta-anomaly-burnol-singular-quotient`
- **Stage:** 1-in-progress
- **Label:** `P-G111`
- **Type:** `[THEOREM (LEAN)] [ROUTE-P POSITIVE SURVIVOR] [SINGULAR QUOTIENT]`
- **Parents:** `P-G107`, `P-G110`, `HedenmalmThetaIntervalTransform.lean`,
  `BurnolPrimeDilationCoPoissonQuotient.lean`, `HedenmalmTwoPrimeNormalFrame.lean`

## Frozen conjecture

The singular quotient forced by P-G107 is not an abstract rigging choice. Complete the removable
prime interval multiplier by the literal Gamma/co-Poisson divided cell

```text
qhat_n(z) = i n^(-1/2)
  GammaCell(log n, 1-dirichletExponent(z), 1/2).
```

Prove off the removable point

```text
qhat_n(z) = shiftMultiplier(n,z),
Fourier(integerAnomaly_n)(z) = qhat_n(z) XiC(z).
```

After canonical centering, prove prime `2` and `3` completed quotient values never vanish
simultaneously on an actual Xi divisor copy. Thus both raw anomaly conormals vanish there, while
their source-defined divisor quotient is nonzero.

## Complete paper proof `[PROVED HERE]`

Since `1-dirichletExponent(z)-1/2=-i z`, Gamma divided-difference law gives

```text
GammaCell = (exp(-i z log n)-1)/(-i z)
          = -i (1-exp(-i z log n))/z.
```

Multiplication by `i n^(-1/2)` gives exact interval multiplier. At `z=0`, factorial completion
supplies missing value `i n^(-1/2) log n`. Centering multiplies by the zero-free phase
`-i exp(i z log(n)/2)`, hence preserves zero set. Existing irrationality of `log 2/log 3` proves
the two centered multipliers have no common nonzero zero; `XiC(0) != 0` excludes origin from Xi
divisor.

## Scientific delta

P-G107 proved regular conormal blindness and demanded singular rigging. P-G111 identifies exact
source-canonical singular quotient: division by Xi on translated theta anomaly equals Burnol's
entire co-Poisson interval cell. Prime `2/3` frame is faithful on every Xi multiplicity copy. This
removes quotient-existence and reporter-nonvanishing obstacles; it does not yet orient quotient
energy.

## External novelty audit

Targeted search checked Burnol's co-Poisson/Sonine papers and Hedenmalm's 2026 spectral theta
paper. Burnol connects co-Poisson, Mellin transforms, Sonine spaces, and zeta-zero evaluators;
Hedenmalm constructs theta-source differential pencils. No located source states the exact
normalized identity between Hedenmalm's integer-translation anomaly multiplier and Burnol's
entire Gamma/co-Poisson divided cell, nor the faithful prime-2/3 singular quotient separation at
each Xi multiplicity copy. Novelty claim is limited to that exact weld and formal theorem.

## Falsifiers

- Gamma cell differs from interval multiplier off `z=0`.
- Completion fails to recover removable value.
- Prime-2/3 completed quotient frame vanishes at any Xi copy.
- Result depends on an assumed zero location rather than only `XiC(z)=0` and `XiC(0) != 0`.

## Gates

- [x] prior anomaly/co-Poisson/two-prime corpus collision audit
- [x] conjecture frozen with exact normalization
- [x] completed Gamma/co-Poisson multiplier formalized
- [x] raw and centered anomaly quotient factorization formalized
- [x] faithful prime-2/3 Xi quotient frame formalized
- [x] raw-conormal-zero / quotient-energy-positive separation formalized
- [x] direct `lake env lean` passes
- [x] exact module `lake build` passes (`12931` jobs)
- [x] module wired into `RHTower.lean`
- [x] external novelty audit completed
- [ ] lint, axiom, and full umbrella audits pass

## Lean status

Umbrella-wired module
`formal/GaloisForLFunctions/RHTower/HedenmalmThetaAnomalyBurnolSingularQuotient.lean` contains the
complete result. Direct `lake env lean` and exact module build pass.

## Log

- 2026-08-13 — P-G111 frozen after P-G110 ruled out every local symmetric rank-two correction.
- 2026-08-13 — Exact Burnol completion, raw/centered factorization, faithful two-prime Xi quotient
  frame, and positive quotient energy formalized; exact build and external novelty audit passed.
