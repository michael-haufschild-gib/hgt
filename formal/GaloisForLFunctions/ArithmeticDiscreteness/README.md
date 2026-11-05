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

| The certificate length must grow: `X − (⌊2√q⌋+1)` is impure but its power sums stay `≤ 2e·q^{ν/2}` for all `9ν⁴ ≤ q` | `TheCertificateLengthGrowsWithQ` | `quarter_power_mimic` |

## Paths

| Statement | Module | Theorem |
|---|---|---|
| Continuous families with integer coefficients on a preconnected set are constant | `UniformRepulsionCarriesReality` | `eq_of_continuousOn_intCoeff` |
| Uniform repulsion along a continuous real family carries reality from `P 0` to every `P t`, with no integrality; loss of reality forces vanishing separation | `UniformRepulsionCarriesReality` | `splits_of_uniform_repulsion`, `exists_near_collision_of_not_splits` |

## Euler products: Diophantine discreteness

| Statement | Module | Theorem |
|---|---|---|
| The prime Kronecker flow `t ↦ (p^{−it}, p'^{−it})` approaches every torsion point at most polynomially: distance `≥ c(2+|t|)^{−C}` for `|t| ≥ 1` (chord bound + effective Baker) | `ThePrimeFlowIsDiophantineAtTorsionPoints` | `exists_chord_lower`, `primeFlow_diophantine_at_torsion` |
| Zeros of `∏_{p∈S}(1 − p^{−s})` (Euler columns) of height `≤ T` collide or repel at scale `c T^{−C}` (effective Baker bound) | `EulerColumnsCollideOrRepelAtPolynomialScale` | `eulerCarrier_collide_or_repel` |
| Two columns have distinct zeros `≤ 2π/((n+1) log p')` apart at height `≤ 2πn/log p` | `EulerColumnsCollideOrRepelAtPolynomialScale` | `eulerColumns_near_coincidence` |
| One prime (`P(p^{−s})`, `P ∈ ℤ[X]` monic): uniform repulsion; the two-prime Euler product: none | `TheRankOfTheFrequencyModuleDecidesRepulsion` | `onePrime_uniform_repulsion`, `twoPrime_no_uniform_repulsion` |
| Integral pure degree-two factors `1 − a_p p^{−s} + p^{−2s}` (`a_p ∈ ℤ`, `|a_p| ≤ 2`): Satake parameters are 12th roots of unity, zeros lie on refined columns, collide or repel at polynomial scale | `IntegralPureEulerFactorsRepelAtPolynomialScale` | `pow_twelve_eq_one_of_satake`, `degTwoCarrier_collide_or_repel` |
| With real pure data `a = 2cos θ` the polynomial law fails: a Liouville angle gives zeros `≤ e^{−|k|}`-close at height `≍ |k|` | `RealSatakeAnglesDefeatPolynomialRepulsion` | `exists_liouville_angle`, `real_pure_carrier_not_polynomial_repulsion` |
| Any finite-prime carrier `D(s) = G((p_i^{−s}))` with zeros in a strip and no tangency `G = H = 0` of its Bohr lift on `K[a,b] = {|x_i| = p_i^{−σ}, σ ∈ [a,b]}` repels uniformly | `ConsistentTangenciesAreTheOnlySourceOfNearCoincidences` | `exists_tangency_gap`, `uniform_repulsion_of_no_consistent_tangency` |
| Converse: an isolated consistent tangency of order `m ≥ 2` gives, at arbitrarily large height and in every disc radius `δ`, zeros of total multiplicity `m` — a multiple zero or two distinct zeros within `2δ` (Kronecker + local Rouché) | `ConsistentTangenciesForceNearCoincidences` | `exists_zeros_near_tangency`, `exists_collision_or_close_pair` |
| Integral pure Euler carriers `∏ F_i(p_i^{−s})` of every degree (`F_i ∈ ℤ[X]` monic, roots of modulus one): roots are torsion (Kronecker), zeros on refined columns, polynomial collide-or-repel | `IntegralPureEulerCarriersOfEveryDegreeRepel` | `exists_pow_eq_one_of_pure`, `pureCarrier_collide_or_repel` |
| For almost every Satake angle `θ = 2πx` the real pure carrier collides or repels at scale `C/T²` (Borel–Cantelli for `kξ − j ∓ x`, `ξ = log 3/log 2`); the Liouville failure is a null set | `GenericSatakeAnglesRepelAtPolynomialScale` | `ae_inhomogeneous_gap`, `ae_realPureCarrier_repulsion` |
| The non-product carrier `(1 − 2^{−s})² − (1 − 3^{−s})³` (cusp of the Bohr lift at `(1,1)`) has near-coincidences at every scale | `ACuspOfTheBohrLiftForcesNearCoincidences` | `cuspCarrier_collision_or_close_pair`, `zeroMult_cuspCarrier` |
| With log coefficients a two-prime affine carrier `−(log 3 − log 2) + log 3·2^{−s} − log 2·3^{−s}` has a smooth consistent tangency at `(1,1)` and near-coincidences at every scale; with integer coefficients a torsion tangency must be singular | `ASmoothTangencyNeedsTranscendentalCoefficients` | `logTrinomial_collision_or_close_pair`, `zeroMult_logTrinomial` |
| For algebraic carriers every tangency at an algebraic point (torsion points, `σ ∈ ℚ` with root-of-unity phases) is a singular point of the lift: the tangency form `Σ log p_i·x_i∂_iG(x)` is transcendental otherwise (corpus Baker) | `AlgebraicTangenciesAreSingular` | `algebraic_tangency_is_singular`, `pderiv_eval_eq_zero_of_algebraic_tangency` |
| Near its cusp the cusp carrier collides or repels at polynomial scale: two zeros within `1/16` whose midpoint `c` has `|1−2^{−c}|, |1−3^{−c}| ≤ r₀`, `|Im c| ≥ 1` satisfy `|s₁−s₂|² ≥ κ(2+|Im c|)^{−K}` | `TheCuspRepelsAtPolynomialScale` | `cusp_algebra`, `flow_coordinate_le`, `cusp_local_repulsion` |
| `(1, 1)` is the only consistent tangency of the cusp carrier on its Bohr lift | `TheCuspIsTheOnlyConsistentTangency` | `neg_log_one_sub_cube_le`, `minus_root_inconsistent`, `cusp_consistent_tangency_eq` |
| Global polynomial collide-or-repel law: distinct zeros of the cusp carrier with `|Im s| ≥ 2` satisfy `|s′−s| ≥ c(2+|Im s|)^{−C}`; in general, zeros off any neighbourhood of the tangency set are uniformly separated | `TheCuspCarrierRepelsAtPolynomialScale` | `cuspCarrier_zero_re`, `repulsion_off_tangency_set`, `norm_cpow_neg_sub_le`, `cuspCarrier_collide_or_repel` |
| The non-Euler two-prime carrier `1 + 2^{−s} + 3^{−s}` repels uniformly (`≥ min(1/4, (log 3 − log 2)/224)`): its Bohr tangency is inconsistent with the moduli | `EulerProductsCreateTheNearCoincidences` | `trinomial_uniform_repulsion`, `trinomial_tangency_gap` |

## Zeta: the dictionary of B54

| Statement | Module | Theorem |
|---|---|---|
| Two zeros of a holomorphic `f` within `R/4` flatten `f'`: `‖f'(a)‖‖b−a‖ ≤ (8M/R²)‖b−a‖²` | `ANearCoincidenceFlattensZeta` | `norm_deriv_mul_le_of_two_zeros` |
| For `ζ`: a second zero within `1/8` forces `‖ζ'(ρ)‖ ≤ 160e²(|γ|+2)(|γ|+5)‖ρ'−ρ‖`; a lower bound `‖ζ'(ρ)‖ ≥ c` separates `ρ` from every other zero by `min(1/8, c/(160e²(|γ|+2)(|γ|+5)))` | `ANearCoincidenceFlattensZeta` | `norm_deriv_riemannZeta_mul_le_of_near_zero`, `separation_of_norm_deriv_riemannZeta_ge` |

| An off-line zero `½ + δ + iγ` and its partner flatten `ζ` at the centre: `|ζ(½+iγ)| ≤ 480e²(|γ|+2)(|γ|+5)δ²` for `|δ| ≤ 1/16`; a lower bound for `|ζ(½+iγ)|` is a depth gap | `TheDepthOfAnFEPairIsReadOnTheLine` | `norm_le_of_two_symmetric_zeros`, `norm_zeta_center_le_of_offline_zero`, `depth_ge_of_norm_zeta_center_ge` |
| The pair makes `|ζ(½+it)| ≤ 1280e²(|γ|+2)(|γ|+5)η²` on all of `|t−γ| ≤ η` (`0 < |β−½| ≤ η ≤ 1/16`); a sublevel set of measure `< 2η` there is a depth gap; and `|β−½| ≥ min(1/16, |ζ'(ρ)|/(320e²(|γ|+2)(|γ|+5)))` | `TheDepthOfAnFEPairIsReadOnTheLine` | `norm_zeta_line_le_of_offline_zero`, `depth_gt_of_small_value_measure`, `depth_ge_of_norm_deriv` |

| Two zeros within `1/16` make `ζ` and `ζ'` jointly small at their midpoint (`|ζ(c)| ≤ K‖h‖²`, `|ζ'(c)| ≤ K‖h‖`): B54 is the emptiness of a joint small-value set of `(ζ, ζ')` | `NearCoincidencesAreJointSmallValues` | `norm_deriv_le_of_two_symmetric_zeros`, `joint_small_values_of_close_zeros` |

| Converse: if `|F(c)| + |F'(c)|r + (64M/R³)r³ < ½|F''(c)|r²` then `F` has zeros of total multiplicity exactly two in `‖z−c‖ < r` (third-order Taylor + Rouché) | `JointSmallValuesAreNearCoincidences` | `norm_taylor_two_remainder_le`, `two_zeros_of_joint_small_values` |

## Reading

Integrality quantizes impurity and amplifies approximate purity; it never produces purity, and it
cannot act along a continuous path. Over `ℤ` the frequency module `⊕ ℤ log p` has infinite rank, so
near-coincidences can occur at every scale; they do so exactly when the Bohr lift has a tangency
consistent with the moduli `|p^{−s}| = p^{−σ}` (the Euler product over `{2, 3}`: yes; the trinomial
`1 + 2^{−s} + 3^{−s}`: no). Their separation is then a height-dependent transcendence statement
(effective Baker for Euler carriers).
