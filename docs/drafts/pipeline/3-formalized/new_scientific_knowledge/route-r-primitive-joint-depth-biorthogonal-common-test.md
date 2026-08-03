# Route R primitive joint-depth biorthogonal common-test landing

- **ID:** `route-r-primitive-joint-depth-biorthogonal-common-test`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **RH used:** no
- **Xi zero used:** no
- **Computation used:** no
- **Parent:** `singular-infinite-source-pointed-common-test-factorization.md`

## Frontier statement

Route R requires primitive promotion to occur before any divisor or
prime-power scalarization. The earlier positive common-test source used the
single symmetric amplitude

```text
sqrt(Lambda(n)/n).
```

That realizes the correct scalar kernel, but it takes the geometric mean
before pairing and therefore does not exhibit the promoted source and the
reciprocal-promotion descent leg separately.

For `pe=(p,e)`, put `n=p^(e+1)`. For complex right-half-plane parameters
`w,v`, define the two retained-label coefficients

```text
L_w(pe) = [log(p)/sqrt(n)] n^(-w),
R_v(pe) = [1/sqrt(n)]       n^(-v).
```

The first coefficient is the literal primitive-promoted Gamma boundary
amplitude. The second is the reciprocal-promotion co-source. Prime and
valuation-depth labels remain present on both legs until their Hilbert
pairing.

## Theorem

If `Re(w)>0` and `Re(v)>0`, then `L_w` and `R_v` belong to
`ell^2(Primes x Nat)`, and

```text
<R_v,L_w>
  = sum_(p prime) sum_(e>=0)
      log(p) p^(-(e+1)(1+w+conj(v)))
  = LSeries Lambda (1+w+conj(v)).
```

Consequently

```text
<R_v,L_w> / (w+conj(v))
  = eulerPrimitiveCommonTestKernel(w,v).
```

This is unconditional and two-variable. It constructs the exact
source-to-common-test landing on the joint prime/depth carrier rather than
recovering only a scalar real-displacement trace.

## Proof

For every prime-depth coordinate, the squared norms are

```text
|L_w(pe)|^2
  = [log(p)^2/n] exp(-2 Re(w) log(n)),

|R_v(pe)|^2
  = [1/n] exp(-2 Re(v) log(n)).
```

These are exactly the previously proved promoted-boundary and
reciprocal-promotion square families at displacements `2 Re(w)` and
`2 Re(v)`. Their positive-displacement summability gives the two Hilbert
vectors.

At zero displacement, primitive promotion cancels only across the two legs:

```text
[log(p)/sqrt(n)] [1/sqrt(n)] = log(p)/n = Lambda(n)/n.
```

For prime powers this is the square of the resolved von Mangoldt depth-one
amplitude. Complex conjugation on the right leg changes `n^(-v)` to
`n^(-conj(v))`; therefore each coordinate product equals the Dirichlet term

```text
LSeries.term Lambda (1+w+conj(v)) n.
```

Since `Re(1+w+conj(v))>1`, the von Mangoldt L-series is absolutely summable.
Unique factorization makes `(p,e) |-> p^(e+1)` injective. The von Mangoldt
support is contained in prime powers, so the prime-power reindexing theorem
identifies the joint-depth sum with the full L-series. Multiplication by the
common Hardy Cauchy factor `1/(w+conj(v))` yields the stated common-test
kernel.

## Anti-theatre audit

This is not RH, a zero detector, or a renamed scalar Euler identity. New
frontier content is the simultaneous construction of both nonidentical
Hilbert legs on the complete prime/depth carrier and proof that their
two-variable pairing is the pre-existing Route-R common-test kernel.
Primitive promotion is visible and remains attached to source incidence
until the final pairing.

The theorem removes one precise ambiguity from Route R: common-test landing
does not require taking the geometric mean before source pairing. It does not
supply the unresolved source-derived Ward sign. Remaining producer must add
the Gamma/Green reflection differential and prove that its arithmetic
boundary contribution annihilates the nonright divisor complement before
the four-unit Ward consumer.

## Lean certificate

```text
formal/GaloisForLFunctions/RHTower/
  EulerPrimitiveJointDepthBiorthogonalCommonTest.lean
```

Capstones:

- `xiGammaEulerPrimitiveCommonTestSourceLp`;
- `xiGammaEulerPrimitiveCommonTestCoSourceLp`;
- `xiGammaEulerPrimitiveCommonTestSourceCoeff_mul_star_coSourceCoeff_eq_term`;
- `inner_xiGammaEulerPrimitiveCommonTestCoSource_source_eq`;
- `xiGammaEulerPrimitiveJointDepthCommonTestPairing_eq`.

## Exact surviving frontier

Construct the Gamma/Green-reflected differential on this biorthogonal
joint-depth common-test source and prove its boundary form equals the
four-unit Ward form with source-derived positive orientation. Existing
positive-cone, finite signed-orbit, and absolutely summable signed-orbit
rigidity theorems force that differential to be divisor-coupled before
frequency separation or singular beyond absolute orbit summability.
