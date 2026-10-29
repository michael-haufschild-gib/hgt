# Cyclotomic coercivity with an exact positive remainder

- **ID:** completed-arithmetic-forms-cyclotomic-coercivity
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** The full divisor-conductor Gram controls the interior coefficient square mass
  and its total-mass square with universal factor one quarter, with an exact positive remainder.

## Statement

For an integer `Q ≥ 1` and real coefficients `a_i`, `1 ≤ i < Q`, put

`A = Σ_i a_i`, `P(z) = Σ_i a_i Σ_(r<i) z^r`,

`E_Q(a) = Σ_(m|Q,m≠1) Σ_(i,j) a_i a_j G_m(i,j)`,

`R_Q(a) = Σ_(m|Q,m≠1) Σ_(z primitive m) |(1+z)P(z)|²`.

Then

`4 E_Q(a) = Q (A² + Σ_i a_i²) + R_Q(a)`.

Consequently `Q (A² + Σ_i a_i²) ≤ 4 E_Q(a)`. The interior form is strictly positive
on every nonzero coefficient vector. Boundary prefix lengths `0` and `Q` are null directions.

## Proof

The geometric identity gives `(1-z)P(z) = A - Σ_i a_i z^i`. Its coefficient vector
on one period is `b_0=A`, `b_i=-a_i`, so it has zero sum. Discrete Parseval on all
`Q`th roots gives

`Σ_(z^Q=1) |(1-z)P(z)|² = Q (A² + Σ_i a_i²)`.

The constant root contributes zero. Partition the remaining roots by their primitive orders
dividing `Q`. Every root has unit norm, hence

`|(1-z)P(z)|² + |(1+z)P(z)|² = 4 |P(z)|²`.

Summing and applying the exact primitive-prefix Gram identity proves the decomposition.
Every summand of `R_Q` is nonnegative. If the interior energy vanishes, the inequality forces
each `a_i=0`; conversely the zero vector has zero energy. The existing divisor completion
`Σ_m G_m(i,j)=Q min(i,j)-ij` vanishes whenever either index is `0` or `Q`.

## Accumulation consequence

For `T=Q-1`, set `a_j=c_j/j`. The kernel identity

`Q min(j,k)-jk = Q jk (1/max(j,k)-1/Q)`

identifies the actual cumulative covariance with `E_Q(a)/Q`. It therefore has the lower bound

`(1/4) [Σ_(1≤j≤T) (c_j/j)² + (Σ_(1≤j≤T) c_j/j)²]`.

Application to the actual Euler-deletion increments retains every unequal-pair term.
This is a coercivity estimate; it does not supply the upper bound required by the current criterion.

## Uniform truncation of the actual error energy

For every `1≤X<M` and `T≥0`, the literal full Euler-deletion energy satisfies

`0 ≤ fullErrorEnergy(X,M)-cumulativeEnergy(c,T) ≤ (M+1)²/(T+1)`.

The source bound `|modular(X,M,n)|≤M` gives `|1-modular(X,M,n)|≤M+1` at every coordinate.
The omitted carrier weights telescope:

`Σ_(n>T) 1/(n(n+1))=1/(T+1)`.

Termwise comparison proves the upper tail bound; nonnegativity proves the lower bound.
The estimate holds simultaneously in both cutoffs and the coordinate horizon.

## Dependencies

- `primitivePrefixGram_quadratic_eq`.
- `sum_nontrivial_divisors_primitivePrefixGram`.
- `sum_nthRootsFinset_norm_sq`.
- The partition of roots of unity by primitive order.

## Lean declarations

- `CompletedArithmeticForms.divisorGramEnergy_completion`.
- `CompletedArithmeticForms.divisorGramEnergy_coercive`.
- `CompletedArithmeticForms.divisorGramEnergy_eq_zero_iff`.
- `CompletedArithmeticForms.cumulativeEnergy_completion`.
- `CompletedArithmeticForms.errorIncrement_mass_le_fullErrorEnergy`.
- `CompletedArithmeticForms.fullErrorEnergy_truncation_bounds`.

Modules: `GaloisForLFunctions/CompletedArithmeticForms/CyclotomicCoercivity.lean` and
`GaloisForLFunctions/CompletedArithmeticForms/DivisorCovariance.lean`.
Both pass `lake --old env lean` without output files. The transitive axiom sets contain
only `propext`, `Classical.choice`, and `Quot.sound`.
