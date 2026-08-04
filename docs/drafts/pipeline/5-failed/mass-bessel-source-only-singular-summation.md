# Mass-Bessel source-only singular summation

**Stage:** Failed / retired  
**Date frozen:** 2026-08-04  
**Label:** `[CIRCULAR]`  
**Parent:** `mass-bessel-finite-radiation-jet-renormalization.md`

## 1. Exact claim, frozen before attack

The infinite-jet obstruction suggested an ontological reversal: regard the
completed prime source as a singular radiation germ modulo its entire
deep-time jet, rather than as a function obtained from finite apertures.

The conjecture was:

> There exists a canonical source-only summation functional on the
> infinite-radiation-jet quotient.  It agrees with the mass-Bessel von Mangoldt
> sum on positive real time and selects a representative bounded on every
> fixed vertical line `t=\sigma+iu`.

If true, the source-to-trace seam would be a singular quotient construction,
not a regular limit, and the selected bounded representative would discharge
the exact open core.

## 2. Hostile attack: uniqueness before regularization

For `a>1/2`, the actual prime series

\[
 P_a(t)=\sum_{n\ge1}\frac{\Lambda(n)}{\sqrt n}B_a(t,\log n)
\]

converges absolutely and locally uniformly on `\Re t>0`; the strip width `a`
beats the prime weight `n^{-1/2}`.  Hence it already defines a unique
holomorphic function on that half-plane.

Let `S_a(t)` be any proposed analytic summation representative which agrees
with the source sum for positive real `t`.  The positive real axis has an
accumulation point inside `\Re t>0`.  The identity theorem forces

\[
 S_a(t)=P_a(t)\qquad(\Re t>0).
\]

Therefore a singular quotient cannot choose another analytic representative
with better vertical growth.  It must return the existing `P_a`.

If boundedness is included in the definition of admissible summation, then

\[
 \text{a bounded source-only summation exists}
 \quad\Longleftrightarrow\quad
 P_a(\sigma+iu)=O_{a,\sigma}(1),
\]

after the same explicit auxiliary terms.  This is exactly the open core, not
an independent source law.

## 3. Verdict

`[CIRCULAR]`.  Infinite-jet language correctly classifies why regular finite
completion fails, but summation cannot alter the already unique holomorphic
source function.  The missing theorem is cancellation inside `P_a`, not
existence of a preferred representative.

The quotient is useful only if it supplies an independently provable identity
whose unique representative is then forced to be bounded.  Selector existence
alone is a renamed boundedness premise.

## 4. Strongest positive survivor

**Source-completion uniqueness.**  Any analytic source completion agreeing
with the positive-real-time mass-Bessel sum agrees with it on the entire right
half-plane.  Thus all honest source-only routes share exactly the same vertical
growth; regularization choice cannot improve the exponent.

This is `[REDISCOVERED] [BRIDGE]`, not new scientific knowledge.  Its abstract
Lean content already exists in mathlib as
`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`.  The route-specific
application still needs formal local-uniform convergence and holomorphy of the
mass-Bessel source series; those are part of the explicit-formula seam, not a
proof of the open bound.

## 5. Stronger replacement constraint

Based on what killed the summation conjecture, the next conjecture must satisfy:

1. it states an identity or invariant of the **existing** holomorphic `P_a`;
2. it is derived from non-self-dual arithmetic source structure, not from a
   bounded-selector axiom;
3. it acts at cofinal/infinite-jet level, since every finite jet fails;
4. it distinguishes output cancellation from bounded bulk dynamics;
5. it cannot be invariant under arbitrary finite symmetric zero surgery.

The natural primitive left by the failures is the two-ended radiation-corona
class of the unique source function.  Mass deformation should be tested first:
if mass is corona-trivial, tuning `a` cannot supply the missing source law.

## 6. Lean status

The abstract uniqueness theorem is `[CORPUS]`.  No mass-Bessel specialization
is claimed `[LEAN-PROVED]`; Bessel-series holomorphy remains unformalized.
