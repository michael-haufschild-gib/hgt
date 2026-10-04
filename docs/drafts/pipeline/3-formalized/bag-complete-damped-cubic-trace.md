# BAG complete damped arithmetic cubic trace

- **ID:** BAG-C28.56x
- **Stage:** 3-formalized, for the exact prime-valuation trace below.
- **Lean:** `RHTower/ChiRamanujanCompleteCubicTrace.lean`;
  namespace `RHTower.BAGTrace`.
- **Continuation:** `../1-in-progress/bag-rational-product-trace-euler-cancellation.md`.

## Exact result

Let sigma>1, z_p=p^(-sigma), and define the prime coefficient c_p(i) to be
1 for i>=0, -z_p/(1-z_p) for i=-1, and 0 below -1. The negative coefficient
is proved equal to -1/(p^sigma-1), matching the local normalized damped
Ramanujan denominator factor.

For each finite prime set P, sum

    prod_(p in P) c_p(i_p)c_p(j_p)c_p(i_p+j_p) z_p^(i_p+j_p)

over ALL integer valuation pairs. As P tends through all finite prime sets:

1. The signed sum tends to zeta(sigma)^2.
2. The sum with either zero valuation vector excluded tends to
   1-zeta(sigma)^2. Both axes are literally masked in `offAxesTrace`;
   `offAxesTrace_eq` proves the subtraction identity.
3. The full absolute sum tends to
   zeta(sigma)^2 prod_p(1+4*p^(-sigma)), a convergent Euler product.

Public capstones: `complete_signed_trace_zeta`,
`complete_offAxes_trace_zeta`, `complete_absolute_trace_limit`.

## Proof

The complete local sum has a positive quadrant, two positive corners, and
two negative strips. Geometric HasSum identities evaluate the signed local
mass as (1-z)^(-2) and its absolute mass as (1+4z)/(1-z)^2. A finite-product
HasSum theorem retains all valuation assignments. The ordinary absolutely
convergent Euler product gives the global signed limit, and summability of
4*p^(-sigma) gives the exact absolute limit. Each axis has the same square
coefficient sum as the full signed trace; deleting their union restores the
common origin once. Conversion to mathlib's riemannZeta is proved.

## Audit and scope

Direct production audit with `lake --old env lean` exits0 without diagnostics.
All27 public theorem axiom queries exit0 and report only propext,
Classical.choice and Quot.sound. Umbrella import wired; no umbrella/full build.
Logs: `/tmp/bag-rational-trace-final-01a0.log` and
`/tmp/bag-rational-trace-axioms-01a0.log`.

Index regeneration passes. Repository lint reports18 unrelated unreachable
modules, with no error for this leaf, proof debt, or generated-file freshness.
Temporary Lean probes removed; audit/search logs retained.

This evaluates the complete directed prime-coordinate resonance trace.
A single unordered positive-rational double-tsum reindexing is not a theorem
of this leaf. More importantly, the arithmetic frequency axes have NOT been
identified with the literal physical prime diagonals. The full weighted
critical boundary, finite-height near-resonances, coupled damping/band limit,
and moving V/W amplitudes remain open. Growing moments, moving cofactors,
positive common-height self-return and RH are not proved.
