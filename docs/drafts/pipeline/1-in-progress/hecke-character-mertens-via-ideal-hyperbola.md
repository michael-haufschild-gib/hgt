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

Use the unweighted ideal hyperbola identity with the actual count
`rho*x+O(x^alpha)`. Partial summation gives the logarithmic ideal sum
`rho*x*log x+O(x)`. The total hyperbola remainder is `O(x)` by the same
weighted Chebyshev estimate. Dividing by `rho*x`, with `rho>0`, gives
the claimed `log x+O(1)` prime-power Mertens formula.

## Remaining obligations

1. Completed: actual nonvanishing at one, including quadratic characters.
2. Reuse or prove the power-saving harmonic tail estimate and bounded
   logarithmic sum for the actual Hecke coefficients.
3. Prove the weighted ideal multiplication and hyperbola identities.
4. Prove the power-weighted Chebyshev estimate with its actual exponent.
5. Assemble the nontrivial and trivial Mertens statements and audit them.

No Mertens result on this card is yet claimed. Convergence to an exact
Mertens constant is a stronger statement than boundedness and is not
being inferred from these bounds.
