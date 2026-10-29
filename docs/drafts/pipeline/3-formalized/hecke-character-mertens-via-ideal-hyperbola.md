# Hecke character Mertens bounds from the ideal hyperbola identity

- **ID:** hecke-character-mertens-via-ideal-hyperbola
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke programme](../1-in-progress/hecke-l-functions-and-class-field-theory-2026-10-28.md)
- **Statement:** The actual prime-power sum `Mpsi(N)=sum_(N(p)^k<=N) psi(p)^k log N(p)/N(p)^k` is bounded for every nontrivial ray class character. For the trivial character it is `log N+O(1)`. The same statements hold for sums over prime ideals alone.

## Completed inputs

1. [All-character nonvanishing](real-hecke-characters-nonvanishing-by-positive-occupations.md):
   `heckeLCont_one_ne_zero` supplies the actual nonzero value at one.
   Final source audit and five transitive axiom audits pass.
2. [Harmonic estimates](hecke-harmonic-sums-have-power-saving-tails.md):
   with `delta=1/(2[K:Q])>0`, the actual harmonic sums satisfy
   `|L(1,psi)-Spsi(N)|<=C*(N+1)^(-delta)`, and logarithmic harmonic sums
   `Tpsi(N)` are bounded. Final source audit and both axiom audits pass;
   the required olean exists.
3. [Weighted ideal hyperbola](hecke-harmonic-sums-satisfy-the-ideal-hyperbola-identity.md):
   `Tpsi(N)=sum_(N(p)^k<=N) psi(p)^k log N(p)/N(p)^k * Spsi(floor(N/N(p)^k))`.
   Weighted ideal multiplication and exact norm grouping justify the
   identity. Final source audit and three axiom audits pass.
4. [Weighted prime powers](prime-power-weights-have-power-bounds.md):
   `exists_sum_primePowersLe_log_rpow_le` gives
   `sum log N(p)*(N(p)^k)^(-sigma)=O(N^(1-sigma))`, for `0<sigma<1`.
   Its scratch, final source audit, and transitive axiom audit pass.
   This reuses `ArtinMertens.sum_log_mul_rpow_neg_le` and the existing
   integer power-sum bound, without duplicating Abel comparison.
5. `ArtinMertens.exists_abs_primeMertens_sub_log_le` already proves the
   untwisted number-field formula `primeMertens=log N+O(1)`. Its full
   source was inspected and its transitive axiom audit passes.

All transitive audits above report only `propext`, `Classical.choice`,
and `Quot.sound`. Both complete Mertens conclusions below, including
their prime-ideal versions, now also pass Lean and seven transitive
axiom audits with exactly those axioms.

## Nontrivial-character proof

Replace the harmonic sum in the exact hyperbola identity by its L-value.
For `q=N(p)^k`, the inequality `N/q < floor(N/q)+1` and the negative
power weight give an error at most

`C*N^(-delta)*sum_(q<=N) log N(p)*q^(delta-1)`.

Since `0<delta<1`, the weighted prime-power bound makes this uniformly
bounded. Thus `Tpsi(N)-L(1,psi)*Mpsi(N)=O(1)`. The logarithmic sum is
bounded and the actual L-value is nonzero, so `Mpsi(N)=O(1)`.

The harmonic estimates come from twisting at `sigma0=1-delta`, strictly
between the ray-class counting exponent and one. Bounded shifted partial
sums and decreasing-weight Abel summation give the tail. The logarithmic
weight `log n/n^delta` eventually decreases and gives the second estimate.
No sharp exponent or stronger prime-distribution assertion is assumed.

## Trivial-character proof

`heckeValue_one_prime` identifies the difference from the existing full
prime-ideal Mertens sum as exactly the mass of primes dividing `m.fin`.
These primes lie in the finite set of nonzero prime ideals of norm at
most `N(m.fin)`. Each geometric prime-power row is bounded by
`2*log N(p)`, using `HTGeometry.geom_sum_range_le` and `N(p)>=2`.
The deleted mass is nonnegative and uniformly bounded. Subtracting it
from `primeMertens=log N+O(1)` proves the trivial Hecke formula.

This avoids repeating the already proved ideal-count/logarithmic
hyperbola argument. Convergence to an exact Mertens constant is stronger
than boundedness and is not inferred here.

## Removing higher prime powers

The inspected source
`ArtinMertens/TheDegreeOnePrimesCarryTheMertensSum.lean` already bounds
`primeMertens-degreeOneMertens` uniformly. Grouping by norm identifies
this remainder with the full non-prime-norm mass. Every term with
exponent greater than one has non-prime norm, and each twisted term's
norm is bounded by its untwisted mass. Consequently the difference
between Hecke prime-power and prime-ideal sums is uniformly bounded.
The combined scratch contains the exact integral-prime reindexing,
this difference bound, and both prime-ideal Mertens conclusions.

## Declarations and audit

Final module:
`GaloisForLFunctions/HeckeLFunctions/HeckeCharactersSatisfyMertensBounds.lean`.

Seven main transitive axiom audits pass with exactly
`[propext, Classical.choice, Quot.sound]`:

- `exists_norm_heckeMertens_hyperbola_error_le`
- `exists_norm_heckePrimePowerMertensSum_le`
- `heckePrimePowerMertensSum_one_eq`
- `exists_norm_heckePrimePowerMertensSum_one_sub_log_le`
- `norm_heckePrimePowerMertensSum_sub_prime_le`
- `exists_norm_heckePrimeMertensSum_le`
- `exists_norm_heckePrimeMertensSum_one_sub_log_le`

The final direct source audit
`lake --old env lean GaloisForLFunctions/HeckeLFunctions/HeckeCharactersSatisfyMertensBounds.lean`
passes without warnings. The module is wired into the Hecke umbrella.
No umbrella was compiled. No Mertens olean is generated until a written
consumer requires it.

HL6 is complete. The primitive completed functional equation remains on
[its arithmetic card](hecke-primitive-gauss-sums-and-arithmetic-dual-character.md).
Class field theory follows the completed Hecke programme.
