# Xi horizontal multiplicity-one universality law

Status: paper proof complete; exact `lake env lean` audit passed.

## Lean sources

- `two_le_xiHorizontalMultiplicity_of_offLine`
- `xiHorizontalSingletonZero_re_eq_half`
- `xiHorizontalSingletonZero_order_eq_one`
- `xi_zero_re_mem_open_unit`
- `xi_zero_re_eq_half_of_RH`

## Survivor

Every exact-height Xi-zero fiber has total analytic multiplicity one if and only if RH holds and
every Xi zero has analytic order one. Thus one intrinsic horizontal counting law simultaneously
detects location and simplicity: reflection doubles every off-line fiber, while RH collapses each
height fiber to its unique critical-line point.

The source module proved only the local forward implications for a single horizontal-singleton
zero. The converse requires the global critical-line theorem plus exact identification of every
same-height strip point.

The formalization also exposes the stronger identity
`xiHorizontalMultiplicity ρ.im = (analyticOrderAt xi ρ).toNat` for every Xi zero under RH; the
multiplicity-one equivalence is its global order-one specialization.

## Proof skeleton

For the forward direction, place each Xi zero in its finite strip-height fiber, apply the two local
singleton conclusions, and discharge RH via the zero-free right-half-plane criterion. Conversely,
RH puts every member of a fixed-height fiber at real part `1/2`; equal real and imaginary parts
make it the original zero. The fiber sum therefore has one term, whose order is one.

## Novelty audit

Pending post-formalization literature search.
