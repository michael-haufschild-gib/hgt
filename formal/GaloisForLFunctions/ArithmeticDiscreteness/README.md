# Arithmetic discreteness (Route Ω)

Route Ω of `docs/reports/review-0511/obstacles-summary.md` §2.4: purity from (i) a pure member,
(ii) continuity of the zeros along a deformation, (iii) a discrete structure on near-coincidences
forcing collide-or-repel. Card: `docs/drafts/pipeline/1-in-progress/ado-arithmetic-discreteness-route-omega.md`.

## What discreteness does

| Statement | Module | Theorem |
|---|---|---|
| Distinct roots of every monic `f ∈ ℤ[X]` (roots in `|z| ≤ R`) are `≥ (2R)^{−((n−1)²+n−2)}` apart; no separability | `DistinctRootsOfIntegerPolynomialsRepel` | `one_le_norm_sub_mul_pow_of_ne`, `collide_or_repel_of_monic` |
| The exponent must grow with the degree: Mignotte polynomials `x^{2m} − 2(ax−1)²` have roots `< 2a^{−(m+1)}` apart | `TheRepulsionScaleIsSharp` | `mignotte_close_roots`, `mignotte_monic` |
| Both Frobenius collisions collide or repel; impurity of an integral trace configuration is quantized; near purity is purity | `ImpurityIsQuantized` | `frobenius_collide_or_repel`, `impurity_is_quantized`, `isPureTrace_of_near` |
| Integrality does not produce purity: impure integral configurations exist in every degree | `ImpurityIsQuantized` | `exists_impure_integral` |
| Power sums bounded at `N` consecutive orders past `M₀` certify integral purity; real configurations are never certified at finitely many orders; impure integral configurations have a zero at depth `> log(1+κ)/log q` | `FinitelyManyOrdersCertifyIntegralPurity` | `isPureTrace_of_bounded_powerSums`, `eventually_isPureTrace_of_bounded_powerSums`, `not_certified_at_finitely_many_orders`, `exists_deep_eigenvalue_of_not_pure` |

## Paths

| Statement | Module | Theorem |
|---|---|---|
| Continuous families with integer coefficients on a preconnected set are constant | `UniformRepulsionCarriesReality` | `eq_of_continuousOn_intCoeff` |
| Uniform repulsion along a continuous real family carries reality from `P 0` to every `P t`, with no integrality; loss of reality forces vanishing separation | `UniformRepulsionCarriesReality` | `splits_of_uniform_repulsion`, `exists_near_collision_of_not_splits` |

## Euler products: Diophantine discreteness

| Statement | Module | Theorem |
|---|---|---|
| Zeros of `∏_{p∈S}(1 − p^{−s})` (Euler columns) of height `≤ T` collide or repel at scale `c T^{−C}` (effective Baker bound) | `EulerColumnsCollideOrRepelAtPolynomialScale` | `eulerCarrier_collide_or_repel` |
| Two columns have distinct zeros `≤ 2π/((n+1) log p')` apart at height `≤ 2πn/log p` | `EulerColumnsCollideOrRepelAtPolynomialScale` | `eulerColumns_near_coincidence` |
| One prime (`P(p^{−s})`, `P ∈ ℤ[X]` monic): uniform repulsion; two primes: none | `TheRankOfTheFrequencyModuleDecidesRepulsion` | `onePrime_uniform_repulsion`, `twoPrime_no_uniform_repulsion` |

## Reading

Integrality quantizes impurity and amplifies approximate purity; it never produces purity, and it
cannot act along a continuous path. Over `ℤ` the frequency module `⊕ ℤ log p` has infinite rank, so
near-coincidences occur at every scale; their separation is a height-dependent transcendence
statement (effective Baker for Euler carriers).
