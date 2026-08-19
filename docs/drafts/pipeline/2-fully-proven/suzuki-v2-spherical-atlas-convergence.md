# Suzuki v2 pole-free and spherical-atlas convergence

**Status:** `[PAPER-PROVED]` `[BRIDGE]`  
**Source corrected:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
arXiv:2606.09096v2, Corollary 1.6.

## Exact correction

Write

`T(z) = XiC(z) / (XiC(z) + i XiC'(z))`.

A **finite chart** is an open set `Omega0` on which `T` is holomorphic.  It is not defined by
the nonvanishing of the displayed denominator: at a multiple zero of `XiC`, numerator and
denominator can vanish simultaneously while their quotient has a removable zero.  The RH-bearing
finite chart must be preconnected, contain `0`, and contain the full centered-Xi divisor.

Pole-free convergence means locally uniform convergence of the entire Suzuki characteristics
`W_n` to `T` on this finite chart, with all sufficiently late zeros of `W_n` real.

A **spherical atlas convergence** consists additionally of an open infinity chart `OmegaInf` such
that:

1. `Omega0 union OmegaInf = C`;
2. `1/T` is holomorphic on `OmegaInf`;
3. `1/W_n -> 1/T` locally uniformly on `OmegaInf`;
4. on every compact subset of `OmegaInf`, `W_n` is eventually zero-free.

Condition 4 is essential.  With totalized inversion, `1/0=0`; reciprocal convergence without
zero-freeness would confuse convergence to zero with escape to the point at infinity.

This is the two-affine-chart definition of compact convergence into the Riemann sphere.  At finite
points it is ordinary compact-open convergence.  At poles it is ordinary compact-open convergence
after applying the reciprocal coordinate.

## Theorem

Spherical-atlas convergence implies the corrected pole-free convergence wall, and hence RH.

## Proof

Discard the infinity-chart data and retain `Omega0` and `W_n`.  By definition, `Omega0` is open and
preconnected, contains `0` and every zero of `XiC`, and `T` is holomorphic there.  The finite-chart
clause gives locally uniform convergence `W_n -> T` on `Omega0`; the approximants are eventually
entire and all their zeros are real.

At `0`, `T(0)=1`, so the limit is not identically zero.  Let `z` be any centered-Xi zero.  Because
`z` lies in `Omega0`, the quotient is holomorphic there and `T(z)=0`.  Local Hurwitz zero transfer
places `z` in the closure of the real axis.  The real axis is closed, hence `Im z=0`.  Therefore
every centered-Xi zero is real, which is equivalent to RH.

The reciprocal convergence and compact zero-freeness clauses do not enter this implication; they
are required to make the global spherical formulation faithful at genuine poles rather than an
arbitrary strengthening of the finite-chart premise.

## Hostile audit

- Replacing `Omega0` by `{z | XiC(z)+i XiC'(z) != 0}` is invalid: it can delete multiple Xi zeros.
- Reciprocal convergence without eventual zero-freeness is invalid because inversion is totalized.
- The theorem does not construct `W_n`, the phase `theta(a)`, or the gauge `phi(a,z)`.
- The exact open producer remains source-faithful convergence of the actual Suzuki characteristics
  in either corrected topology.  This card proves only that both corrected formulations are
  coherent and RH-bearing.
