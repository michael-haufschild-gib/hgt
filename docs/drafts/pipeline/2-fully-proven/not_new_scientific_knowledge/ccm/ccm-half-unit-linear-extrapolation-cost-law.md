# Linear extrapolation across the CCM half-unit seam costs a square-root power

- **ID:** `ccm-half-unit-linear-extrapolation-cost-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / NO-GO WITH POSITIVE DUAL, `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** the invariant half-unit weighted-domain seam, positive-shift Euler--Möbius
  contractivity, and the rectangular subpower lower RH gate

## Statement

Let `h>0`, let `omega_1,...,omega_r>=0`, and let `a_1,...,a_r` be complex coefficients.  If the
linear extrapolator reproduces the half-unit exponential atom exactly,

```text
sum_j a_j exp(-omega_j h)=exp(h/2),                       (1)
```

then

```text
sum_j |a_j| >= exp(h/2).                                  (2)
```

More generally, if the relative reproduction error is at most `eta<1`,

```text
|sum_j a_j exp(-omega_j h)-exp(h/2)|
  <= eta exp(h/2),                                        (3)
```

then

```text
sum_j |a_j| >= (1-eta)exp(h/2).                           (4)
```

At aperture `n=exp(h)`, every scalar linear continuation from safe nonnegative shifts through the
missing half-unit therefore has condition number at least `n^(1/2)`.  This remains true when the
number of shifts and their locations depend arbitrarily on `h`.  In particular, cofinal-order
Richardson, finite-difference, polynomial, rational-linear, or quadrature extrapolation cannot turn
separate positive-shift absolute bounds into the `n^o(1)` lower loss required by the rectangular
subpower RH gate.

## Proof

Since every `omega_j>=0` and `h>0`,

```text
|exp(-omega_j h)|<=1.                                    (5)
```

Under exact reproduction, the triangle inequality gives

```text
exp(h/2)
 =|sum_j a_j exp(-omega_j h)|
 <=sum_j |a_j| exp(-omega_j h)
 <=sum_j |a_j|,
```

which is `(2)`.  Under `(3)`, the reverse triangle inequality gives

```text
|sum_j a_j exp(-omega_j h)|
 >=exp(h/2)-eta exp(h/2)
 =(1-eta)exp(h/2).
```

Combining this with the last two inequalities above proves `(4)`. `QED`

## Why growing interpolation order does not help

For each fixed finite aperture the shifted Euler source is analytic in the shift, so it is tempting
to sample many safe positive shifts and let the interpolation order grow with `h`.  The obstruction
is not Taylor remainder.  The atom which the half-unit conjugation must create already forces the
operator norm lower bound `(4)`.  Additional nodes can redistribute the coefficient mass but cannot
reduce it.

Consequently an estimate obtained by bounding the sampled shifted values separately loses at least
the full square-root factor.  The rectangular endpoint tolerates `exp(o(h))`, but `(4)` costs
`exp(h/2)` before any source error is estimated.

## Positive dual

The no-go leaves a strict positive specification.  A successful half-unit transfer must evade at
least one premise of the scalar estimate:

```text
safe shifted channels
  -> retain their coupled prime--polar / floor--Mobius covariance
  -> perform a non-diagonal or nonlinear source cancellation
  -> scalarize only after the half-unit atom has cancelled
  -> leave an exp(o(h)) one-sided boundary loss.           (6)
```

Thus cofinal order is still allowed, but only inside a source-coupled covariance, determinant,
relative trace, or compressed graph.  It cannot be used as a scalar extrapolation of separately
bounded shifted values.  This is the quantitative positive counterpart of the fixed-order
transport wall and the critical Möbius mass-escape theorem.

## Boundary

The theorem does not exclude a source-specific identity in which large interpolation coefficients
cancel against correlated prime and archimedean channels before norms are taken.  It excludes only
linear scalar continuation controlled by the sum of separate absolute-value estimates.  That
distinction is exactly where the surviving RH mechanism must live.

## Lean decision

The proof is the finite triangle inequality plus `exp(-omega*h)<=1`.  Formalizing only this generic
norm estimate would add a wrapper without representing the shifted Euler source or its half-unit
conjugation.  No Lean file is added until the source-coupled extrapolator itself is defined.

## Gates

- [x] arbitrary node count and node placement included
- [x] exact and approximate reproduction costs proved
- [x] square-root aperture cost identified
- [x] positive non-diagonal source obligation extracted
- [ ] construct the source-coupled cancellation which evades scalar extrapolation
- [ ] prove its remaining boundary loss is subpower
- [ ] RH
