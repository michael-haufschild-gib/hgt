# Friable auxiliaries and homogeneous prime-log forms

- **ID:** friable-dirichlet-auxiliary
- **Stage:** 3-formalized
- **Type:** THEOREM / reduction
- **Statement:** A fixed-order derivative of a friable Dirichlet polynomial at `s=1` is a homogeneous form in prime logarithms. Its rational coefficient map is surjective once the auxiliary degree is at least the derivative order.

## Native object

For a finite prime family `p₁,…,p_k`, write `n_m=∏_i p_i^(m_i)` and

`F(s)=Σ_(|m|≤d) λ_m n_m^(−s)`.

The prime-exponent parametrization identifies bounded exponent vectors with
smooth integers. Its coefficient families form the friable polynomial space
`𝒜_(S,d)`. Growing the prime set at fixed degree grows this space.

## Exact derivative and coefficient map

For derivative order `T`, termwise differentiation gives

`F^(T)(1)=(-1)^T Σ_m λ_m (Σ_i m_i log p_i)^T/n_m`.

Multinomial expansion gives

`F^(T)(1)=(-1)^T Σ_(|a|=T) C_a ∏_i(log p_i)^(a_i)`,

`C_a=(T!/∏_i a_i!) Σ_m λ_m ∏_i m_i^(a_i)/n_m`.

Thus integer auxiliary coefficients give rational `C_a`. Over rational
coefficient vectors `λ`, the map `λ↦C` is surjective for `d≥T`.

To prove surjectivity, a relation among its rows can be multiplied by the
nonzero denominator `n_m`. It becomes a degree-at-most-`T` polynomial
vanishing on the lattice simplex `{m≥0:|m|≤d}`. The simplex interpolation
theorem forces every coefficient to vanish. Finite-dimensional duality
then gives surjectivity. The nonzero multinomial factors preserve it.

Integer `λ` do not map onto all rational vectors. Clearing denominators in
a rational solution realizes a nonzero integer multiple of the target form.
For fixed prime set and degrees, a fixed rational right inverse controls
this denominator clearing. Uniform height bounds as these parameters grow
require additional estimates.

## Homogeneous scope

The coefficient-surjectivity theorem concerns forms of one fixed total
degree. It does not identify them with arbitrary polynomial relations
mixing degrees. In particular, `friable_no_soft_spot` states that the
coefficient map has full range; it does not assert that every truncation
has an open transcendence obstruction.

For two distinct primes `p,q`, every fixed-degree family

`(log p)^j (log q)^(T−j)`, `0≤j≤T`,

is linearly independent even over the algebraic numbers. Divide a relation
by `(log q)^T`; it becomes a polynomial relation in `log p/log q`.
Gelfond–Schneider makes this ratio transcendental, also over the algebraic
numbers by transitivity of algebraicity. The exact statement is formalized
in [AHA-LOG2](../aha-two-prime-homogeneous-log-rigidity.md).

Consequently the two-prime homogeneous quadratic case is not the open
algebraic-independence problem for `log 2,log 3`. Qualitative homogeneous
nonvanishing at every separate degree does not exclude mixed-degree
relations. For larger prime sets, higher homogeneous relations need their
own analysis; coefficient surjectivity alone decides none of them.

## Quantitative boundary

The auxiliary race additionally needs lower bounds for the magnitude of a
nonzero collected log form in terms of coefficient height and the growing
prime and degree parameters. Neither coefficient surjectivity nor the
qualitative two-prime theorem supplies those bounds. This card proves no
uniform quantitative C-bound and no algebraic independence of all prime
logarithms.

The zero estimate is a different input: a nonzero `K`-term Dirichlet
polynomial has some nonzero derivative of order below `K`, by Vandermonde
independence. This does not guarantee that its chosen order-`T` collected
form is nonzero. Constants depending on the largest prime become
polynomial in the prime-set size along the canonical first-primes
exhaustion using PNT; that scope does not cover arbitrary prime sets.

## Lean anchors

| Content | Declarations |
|---|---|
| Friable coefficient space | `friableSpace`, `mem_friableSpace_iff` in `RHTower/FriableEdgeCoefficients.lean` |
| Smooth-integer parametrization | `boundedExponentVectorEquivSmooth` |
| Derivative identity | `iteratedDeriv_friableExponentDirichletExp_at_one` in `RHTower/FriableAuxiliary.lean` |
| Word expansion | `primeLogDot_pow_wordExpansion` |
| Collected homogeneous form | `primeLogDot_pow_collected`, `iteratedDeriv_friableExponentDirichletExp_at_one_collected`, `iteratedDeriv_at_one_collected_of_mem_friableSpace` |
| Rational coefficient surjectivity | `friableRow_linearIndependent`, `friableCoefficientMap_surjective`, `friableCoefficientMap_weighted_surjective`, `friable_no_soft_spot` in `RHTower/FriableCoefficientSurjectivity.lean` |
| Simplex interpolation | `eq_zero_of_eval_natCast_eq_zero_on_simplex`, `coeff_eq_zero_of_monomialSum_vanishes_on_simplex` in `HTGeometry/SimplexTestSet.lean` |
| Zero estimate | `diagonalDirichlet_has_nonzero_iteratedDeriv_lt_card` in `RHTower/ZeroEstimateUniformity.lean` |
| Height and Vandermonde controls | `logPrime_height_bound`, `prod_inv_primeLogHeight_le_abs_det_vandermonde` |
| Monomial count bound | `card_boundedDegreeMonomials_le` |
| Canonical prime-exhaustion bounds | `eventually_nth_prime_le_two_mul`, `eventually_nth_prime_le_sq` |

These are the existing formalized identities and bounds. The quantitative
race endpoint remains separate from them.
