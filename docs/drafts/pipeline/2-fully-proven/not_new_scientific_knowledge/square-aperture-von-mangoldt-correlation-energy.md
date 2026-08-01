# Square-aperture von Mangoldt correlation energy

- **ID:** `square-aperture-von-mangoldt-correlation-energy`
- **Stage:** `2-fully-proven`
- **Type:** `THEOREM (paper) / EXACT RH EQUIVALENCE`
- **Scientific status:** `[PAPER-PROVED] [BRIDGE] [CIRCULAR AS SOURCE PRODUCER] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Route:** Route I, coefficient-nonlocal square-aperture pivot

## Definitions

Put

```text
c = 2(1-1/sqrt(2)),
b(k) = Lambda(k)/sqrt(k),
chi_m(k) = 1_{m^2/2 < k <= m^2}.
```

For `M>=1`, define the square-window overlap and first-moment kernels

```text
K_M(k,l) = sum_{1<=m<=M} chi_m(k)chi_m(l),
J_M(k)   = sum_{1<=m<=M} m chi_m(k).
```

Only `k,l<=M^2` contribute. Define the centered correlation energy

```text
C_M = sum_{k,l<=M^2} b(k)b(l)K_M(k,l)
      - 2c sum_{k<=M^2} b(k)J_M(k)
      + c^2 sum_{m<=M} m^2.
```

## Exact finite identity

For every natural `M`,

```text
C_M = sum_{1<=m<=M} (W(m^2)-cm)^2,                 (1)
```

where

```text
W(n)=sum_{n/2<k<=n} Lambda(k)/sqrt(k).
```

In particular `C_M>=0`, although its displayed correlation formula contains cancellation between
three terms of much larger individual scale.

### Proof

For `m<=M`, extend the window sum by zero to the fixed carrier `0<=k<=M^2`:

```text
W(m^2)=sum_{k<=M^2} b(k)chi_m(k).
```

Finite Fubini gives

```text
sum_m W(m^2)^2
 = sum_{k,l<=M^2} b(k)b(l) sum_m chi_m(k)chi_m(l)
 = sum_{k,l<=M^2} b(k)b(l)K_M(k,l),

sum_m mW(m^2)
 = sum_{k<=M^2} b(k) sum_m m chi_m(k)
 = sum_{k<=M^2} b(k)J_M(k).
```

Expanding `sum_m (W(m^2)-cm)^2` proves `(1)`.

## RH implication

Let `E(n)=(W(n)-c sqrt(n))_+`. On square apertures,

```text
E(m^2)=(W(m^2)-cm)_+,
E(m^2)^2 <= (W(m^2)-cm)^2.                         (2)
```

Assume the source-pure correlation estimate

```text
for every delta>0, C_M = O_delta(M^(1+delta)).      (3)
```

Equations `(1)` and `(2)` imply

```text
sum_{m<=M} E(m^2)^2 = O_delta(M^(1+delta))
```

for every `delta>0`. The nonnegative Dirichlet series with coefficients `E(m^2)^2` therefore has
absolute-convergence abscissa at most `1`. Hence, for every `epsilon>0`,

```text
sum_m E(m^2)^2/m^(1+epsilon) < infinity.
```

The already-proved square-sampled positive-excess `L^2` gate now gives RH.

## Reverse implication from RH

This correlation estimate is not an independent source conjecture. It follows from RH by the
classical von Koch--Schoenfeld prime-number-theorem error bound. Schoenfeld's Theorem 10, equation
`(6.2)`, proves under RH that, for `x>73.2`,

```text
|psi(x)-x| < sqrt(x) log(x)^2/(8 pi).                    (4)
```

Write `R(x)=psi(x)-x`. The exact Abel identity already formalized for Route I is

```text
W(n)-c sqrt(n)
  = R(n)/sqrt(n) - R(n/2)/sqrt(n/2)
    + (1/2) integral_[n/2,n] R(t)t^(-3/2) dt.            (5)
```

For `n>146.4`, `(4)` bounds each endpoint term in absolute value by
`log(n)^2/(8 pi)`. For the integral term,

```text
(1/2) integral_[n/2,n] |R(t)|t^(-3/2) dt
 <= (1/(16 pi)) integral_[n/2,n] log(t)^2/t dt
 <= (log 2)/(16 pi) log(n)^2.                            (6)
```

Thus `|W(n)-c sqrt(n)|=O(log(n)^2)`. At `n=m^2`, squaring and summing gives

```text
C_M = O(M log(M)^4) = O_delta(M^(1+delta))               (7)
```

for every `delta>0`. Combined with the formalized forward implication, this proves on paper

```text
RH  iff  SquarePrimeWindowCorrelationEnergySubpower.     (8)
```

Primary source: L. Schoenfeld, *Sharper Bounds for the Chebyshev Functions theta(x) and psi(x).
II*, Mathematics of Computation 30 (1976), Theorem 10,
<https://doi.org/10.1090/S0025-5718-1976-0457374-X>.

## Hard-core classification

Estimate `(3)` is an exact RH equivalent, not a new Route-I source producer. It asks for
near-linear variance after centering a discontinuous dyadic von-Mangoldt window at square
apertures. Expanding and bounding the positive pair term separately loses the cancellation and
leaves cubic-scale main mass. Current unconditional pointwise PNT errors miss `(3)` by a power;
RH supplies it immediately through `(4)`--`(7)`.

This pivot does not map to:

- Route E: no Möbius or squarefree convolution appears;
- Routes B/C1: no rectangular/Haar positivity premise appears;
- retired Route C2: no completed Xi response or horizontal-modulus coordinate appears;
- the adjacent BV boundary route: its scale-zero boundary contraction is not this square-lattice
  two-point correlation estimate.

It is a source-pure prime-pair variance problem. Classical Selberg-integral mean square is a parent
analogy, but a continuous dyadic `L^2` bound does not by itself control this sparse square trace.

## Literature boundary

Brent--Platt--Trudgian, *The mean square of the error term in the prime number theorem*,
<https://arxiv.org/abs/2008.06140>, proves the dyadic continuous error mean square `O(X^2)` under
RH and unconditional lower/oscillation results. It does not supply a restriction theorem from the
continuous measure to unit neighborhoods of square arguments. Bellotti's current zero-density/PNT
error work likewise remains pointwise far above the critical square-trace scale. No primary source
publishing this exact square-window kernel was located. The finite Fubini identity and its RH
consequence are routine applications of finite rearrangement and Schoenfeld's theorem; neither is
claimed as publication-level novelty. The independent-source interpretation of `(3)` is rejected
as circular.

## Gates

- [x] exact finite kernel and carrier fixed
- [x] complete finite-Fubini proof
- [x] exact correlation-growth implication to RH
- [x] RH-to-correlation reverse implication from Schoenfeld plus exact Abel summation
- [x] exact paper equivalence and circularity classification
- [x] anti-theatre and route-collision audit
- [x] exact identity and forward implication formalized unconditionally in Lean
- [ ] reverse implication formalized in Lean (requires a formal von Koch--Schoenfeld theorem)
