# Positive origin degree does not descend through Poisson boundaries

- **ID:** positive-origin-degree-does-not-descend-through-poisson-boundaries
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Q-II source effectivity and linear degree.
- **Statement:** Origin evaluation is a complex-linear degree, strictly positive on every nonzero actual Meyer source sharp square, but cannot factor through genuine Poisson cohomology.

## Proof

For a strong logarithmic source `g`, its sharp involution gives

`(g * g^sharp)(0) = integral exp(t) |g(t)|²`.

Actual convolution integrability supplies integrability of this nonnegative real
integrand. If its integral vanishes, continuity makes it vanish everywhere; positivity
of the exponential then forces `g=0`. Every nonzero source therefore has positive
origin square degree, without a zero-location assumption.

Take the actual Xi-cap boundary `g`. Its Mellin transform at `1` is `xi(1)=1/2`,
so `g` is nonzero. The Poisson range is a convolution ideal, hence `g*g^sharp`
is still a genuine boundary. Its origin degree is strictly positive. A linear degree
on the quotient would send this same boundary to zero, a contradiction.

## Insight

Strict source positivity and quotient descent are distinct obligations. The elementary
positive origin degree cannot replace the descended ordinary trace degree in the
intersection theory. This is an exact obstruction with a positive survivor: a faithful
positive degree on actual sources and an explicit positive boundary witness.

## Lean verification

Module: `formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/OriginDegreeDoesNotDescendThroughPoissonBoundaries.lean`.

- `meyerOriginDegree_sharp_square`
- `meyerOriginDegree_sharp_square_eq_zero_iff`
- `meyerOriginDegree_sharp_square_pos`
- `exists_meyer_boundary_positive_originDegree`
- `meyerOriginDegree_not_cohomology_degree`

Direct `lake --old env lean` file check passed. Each listed declaration has only
`propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. Module wired
into its umbrella; umbrella not compiled. External novelty unverified.
