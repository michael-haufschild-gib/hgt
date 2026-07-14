# Prime--archimedean Bernstein exponential phase selection

- **ID:** `prime-arch-bernstein-exponential-phase-selection`
- **Stage:** 1-in-progress
- **Type:** THEOREM / SOURCE--DIVISOR SELECTION
- **Scientific status:** `[CONJECTURE] [PAPER PROOF IN DEVELOPMENT] [LEAN OPEN]`

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

Prove the source-only phase law

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

with `|alpha_q| >= r` finite.  Apply the finite shift polynomial that kills every distinct such
base except `alpha_0`.  Equal bases have equal nonzero reciprocal-square coordinate, so their
multiplicity weights add and cannot cancel.  The filtered pencil is therefore

```text
c_0 * alpha_0^n + O(r^n),  c_0 != 0.
```

Any subexponential bound on `TV(n)` passes to every fixed finite shift filter of `P_n(w)`, which
contradicts `|alpha_0| > r > 1`.  Thus subexponential source total variation forces every
reciprocal-square coordinate to be real and hence forces RH.

## Formalization plan

1. Prove the generic summable exponential-family filtering lemma.
2. Prove the unit-circle strict-ellipse lemma
   `u not real -> exists |w|=1, 1 < |1-u+u*w|`.
3. Prove equality of pencil bases implies equality of reciprocal-square coordinates when `w != 1`.
4. Group the finite exceptional bases and prove their coefficients are nonzero multiplicity sums.
5. Transfer subexponential Bernstein total variation through the pencil bound and the finite shift
   filter.
6. Close the RH equivalence and add it to the source--temperature master theorem.

## Gates

- [x] exact Bernstein total-variation identity
- [x] exact prime--Gamma/Xi pencil identity
- [x] unit-disk total-variation bound
- [x] numerical pre-certification on symmetric synthetic off-line packets
- [ ] summable exponential-family filtering lemma
- [ ] off-line reciprocal-square exponential witness
- [ ] source subexponential phase law
- [ ] Lean proof and axiom audit
- [ ] manuscript integration
