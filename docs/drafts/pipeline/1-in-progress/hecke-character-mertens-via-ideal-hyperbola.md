# Hecke character Mertens bounds from the actual ideal hyperbola identity

- **ID:** hecke-character-mertens-via-ideal-hyperbola
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [Hecke programme](hecke-l-functions-and-class-field-theory-2026-10-28.md)
- **Statement:** For every nontrivial ray class character, the actual prime-power Mertens sum `sum_(N(p)^k<=x) psi(p)^k log N(p)/N(p)^k` is bounded. For the trivial character the corresponding sum is `log x+O(1)`.

## Existing inputs

- `HeckeLFunctionsContinuePastTheLineReOne` supplies actual coefficient
  partial sums `O(x^alpha)` for nontrivial characters and
  `heckeDensity*x+O(x^alpha)` for the trivial character, where
  `alpha=1-1/[K:Q]` and `0<=alpha<1`.
- Global continuation and all-character nonvanishing are proved. In particular
  `heckeLCont_one_ne_zero` supplies the actual nonzero value needed below;
  its transitive axiom audit reports only the standard Lean axioms.
- `ArtinMertens/TheIdealVonMangoldtIdentity.lean` proves the actual
  prime-power divisor identity and the multiplication bijection for
  bounded ideals. Its source has been inspected. The needed weighted
  sum identity must be derived from this bijection, not from a cardinality
  equality alone.
- `ArtinMertens/ThePrimeIdealsSatisfyChebyshevBounds.lean` and
  `TheSoftMertensTheoremForPrimeIdeals.lean` give `sum_(N(p)^k<=x) log N(p)=O(x)`.
- `RenormalizedArithmeticPotentialTheory/MertensTheoremForCharacters.lean`
  proves the rational-character model by harmonic tails, a logarithmic
  sum, the hyperbola identity, and `L(1,chi)!=0`. The source is inspected;
  its bounded character partial sums must be replaced by the actual Hecke
  power saving, not assumed for number-field characters.

## Nontrivial-character proof

Put `sigma0=(alpha+1)/2` and `delta=1-sigma0>0`. The existing
`exists_norm_sum_term_le` bounds the partial sums of
`a(n)=LSeries.term(heckeCoeff,sigma0,n)` by a constant `M`.
Shifted partial sums are bounded by `2M`; the existing decreasing-weight
Abel bound applied to `(N+j)^(-delta)` bounds every finite harmonic tail
by `2M*N^(-delta)`. Passing to the already proved series limit gives

`Spsi(y)=sum_(N(I)<=y) psi(I)/N(I) = L(1,psi)+O((y+1)^(-delta))`.

This weaker exponent suffices; no sharp tail estimate is needed.
The analogous logarithmic sum
`Tpsi(x)=sum_(N(I)<=x) psi(I)*log N(I)/N(I)` is bounded, since
the same power saving makes its Abel integral converge.
Multiplicativity and the actual ideal von Mangoldt identity give exactly

`Tpsi(x)=sum_(N(p)^k<=x) psi(p)^k*log N(p)/N(p)^k*Spsi(floor(x/N(p)^k))`.

Replace the harmonic sum by its nonzero L-value. Its total error is bounded
by a constant times

`x^(-delta) * sum_(N(p)^k<=x) log N(p)*(N(p)^k)^(delta-1)`.

Partial summation of the proved prime-power Chebyshev bound makes the
last sum `O(x^delta)`. Thus `L(1,psi)*Mpsi(x)=O(1)`, and division by the
actual nonzero value proves boundedness.

## Trivial character

A later corpus query located the already formalized
`ArtinMertens/TheMertensTheoremForPrimeIdealsHasABoundedError.lean`,
whose complete source has now been inspected. Its
`exists_abs_primeMertens_sub_log_le` proves `log x+O(1)` for all prime
ideals. The trivial Hecke case follows by deleting the finitely many
primes dividing the finite modulus; each deleted geometric prime-power
sum is bounded by `log N(p)/(N(p)-1)`. There is no need to repeat the
ideal-count/logarithmic hyperbola proof.

## Remaining obligations

1. Completed: actual nonvanishing at one, including quadratic characters.
2. Completed: actual power-saving harmonic tail and bounded logarithmic
   sum, both with standard transitive axiom audits. Final module
   `HeckeHarmonicSumsHavePowerSavingTails.lean` passes its direct source
   audit; [proof](../3-formalized/hecke-harmonic-sums-have-power-saving-tails.md).
3. Completed scratch: weighted ideal multiplication and actual hyperbola
   identity, all three transitive axiom audits standard-only. Final direct
   source audit passes; [proof](../3-formalized/hecke-harmonic-sums-satisfy-the-ideal-hyperbola-identity.md).
4. Prove the power-weighted Chebyshev estimate with its actual exponent.
5. Assemble the nontrivial and trivial Mertens statements and audit them.

No Mertens result on this card is yet claimed. Convergence to an exact
Mertens constant is a stronger statement than boundedness and is not
being inferred from these bounds.

## Written arithmetic consumers

`/tmp/HeckeWeightedIdealHyperbolaScratch.lean` contains the weighted
multiplication bijection, weighted ideal von Mangoldt identity, exact
norm grouping, actual harmonic hyperbola formula, and prime-power weight
bound. It passes without warnings and is finalized as
`HeckeHarmonicSumsSatisfyTheIdealHyperbolaIdentity.lean`; its final direct
source audit passes. Its required consumer olean is not built yet.

`/tmp/HeckeWeightedChebyshevScratch.lean` now reuses
`ArtinMertens.sum_log_mul_rpow_neg_le` from the same bounded-error
module. No new grouping or Abel-comparison proof is needed.
`RHTower.Sieve.sum_rpow_neg_le_of_lt_one` gives
`sum log N(p)*(N(p)^k)^(-sigma)=O(x^(1-sigma))`, for `0<sigma<1`.
Both source proofs have been inspected. This scratch is under its first
complete check. An earlier check was stopped immediately because it
briefly overlapped the previous final audit; no conclusion came from it.

`/tmp/HeckeNontrivialMertensScratch.lean` is the complete written consumer.
It substitutes the harmonic approximation into the exact hyperbola sum,
uses the weighted prime-power bound, and divides by the proved actual
nonzero `heckeLCont(1,psi)`. It remains uncompiled pending the two arithmetic
modules. Its imports also justify building the now-finalized nonvanishing
module's olean, which is not built yet.

`/tmp/HeckeTrivialMertensScratch.lean` is the complete written trivial
consumer. `heckeValue_one_prime` identifies the deleted mass exactly.
The bad primes lie in the finite set of nonzero prime ideals of norm at
most `N(m.fin)`. Each geometric prime-power row contributes at most
`2*log N(p)`, using `HTGeometry.geom_sum_range_le`. The existing full
prime-ideal Mertens theorem then gives `log N+O(1)`. This scratch remains
uncompiled. No additional counting or logarithmic-error proof is needed.
