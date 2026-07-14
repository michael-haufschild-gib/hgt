# Prime--archimedean Bernstein exponential phase selection

- **ID:** `prime-arch-bernstein-exponential-phase-selection`
- **Stage:** 3-formalized
- **Type:** THEOREM / SOURCE--DIVISOR SELECTION
- **Scientific status:** `[THEOREM] [PAPER PROVED] [LEAN FORMALIZED]`

## Target

Let

```text
a(n,i) = momentFunctional
  (radiusNormalizedMoment primeArchEndpointHausdorffRadius normalizedPrimeArchMoment)
  (bernsteinPolynomial R n i)
```

and let

```text
TV(n) = sum_{0 <= i <= n} |a(n,i)|.
```

The source-only phase law is

```text
RH
  iff for every epsilon > 0, eventually TV(n) <= exp(epsilon * n).
```

Equivalently, using the exact order-unit identity

```text
TV(N+1) = s(0) + 2 * eta(N),
```

RH is equivalent to subexponential growth of the total Bernstein negative mass.  This is strictly
weaker in syntax than `eta(N) -> 0`: nonzero and unbounded negative mass is permitted, provided its
exponential rate vanishes.

The false-RH phase must therefore be positive:

```text
not RH -> exists epsilon > 0,
  infinitely many n satisfy exp(epsilon * n) < TV(n).
```

## Existing exact source identity

For `|w| <= 1`, define

```text
P_n(w) = sum_i a(n,i) w^i.
```

The formal source--divisor pencil identity already gives

```text
P_n(w)
 = sum_q lambda_q * (1 - lambda_q / R + (lambda_q / R) * w)^n,

|P_n(w)| <= TV(n),
```

where `lambda_q` is the multiplicity-exact reciprocal-square Xi coordinate and `R` is the endpoint
Hausdorff radius.

## Exponential-separation mechanism

Assume an off-line zero exists and choose its nonreal normalized coordinate `u_0 = lambda_0 / R`.
There is `w` on the unit circle such that

```text
alpha_0 = 1 - u_0 + u_0 * w,
|alpha_0| = |1-u_0| + |u_0| > 1.
```

Choose `1 < r < |alpha_0|`.  Absolute summability of `lambda_q` makes the set of bases

```text
alpha_q = 1 - lambda_q / R + (lambda_q / R) * w
```

with `|alpha_q| >= r` finite.  On the maximal-radius packet, equal bases have equal nonzero
reciprocal-square coordinate, so their multiplicity weights add and cannot cancel.  After
normalization by the maximal radius, the distinct surviving bases lie on the unit circle.  The
exact Cesaro mean-square identity for a finite exponential pencil gives a positive limiting square
mean, while the absolutely summable lower-radius tail tends to zero.  Therefore the full normalized
pencil cannot tend to zero.

Since `|P_n(w)| <= TV(n)`, subexponential total variation would force every such normalized pencil
to tend to zero, a contradiction.  Thus subexponential source total variation forces every
reciprocal-square coordinate to be real and hence forces RH.

## Formal theorem surface

- `FiniteExponentialPencilMeanSquare.lean` proves the exact finite Cesaro mean-square identity,
  collision-fiber aggregation, and the dominant-finset nondecay theorem for an absolutely summable
  exponential family.
- `PrimeArchBernsteinExponentialPhase.lean` proves the strict unit-circle ellipse witness, the
  multiplicity-exact off-line exponential witness, and
  `riemannHypothesis_iff_primeArchEndpointBernsteinTotalVariation_subexponential`.
- `PrimeArchBernsteinNegativeMassAbscissa.lean` converts total variation to the exact scalar
  Bernstein negative mass and identifies the condition with the critical prime--polar abscissa.
- `PrimeArchCofinalSourceTemperatureMaster.lean` incorporates both subexponential endpoints into
  the source--temperature equivalence chain.

## Gates

- [x] exact Bernstein total-variation identity
- [x] exact prime--Gamma/Xi pencil identity
- [x] unit-disk total-variation bound
- [x] numerical pre-certification on symmetric synthetic off-line packets
- [x] summable exponential-family dominant-packet nondecay theorem
- [x] off-line reciprocal-square exponential witness
- [x] source subexponential phase law
- [x] Lean proof and axiom audit
- [x] manuscript integration
