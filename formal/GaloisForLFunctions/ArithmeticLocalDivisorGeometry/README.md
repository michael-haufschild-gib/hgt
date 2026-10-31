# ArithmeticLocalDivisorGeometry (ALDG)

Namespace `GaloisForLFunctions.ArithmeticLocalDivisorGeometry`; umbrella `ArithmeticLocalDivisorGeometry.lean`;
25 modules. Polynomial algebra over `ℝ[X]`; source files use `RHTower` zero copies.

## 1. Motivation

At each real height `t` the horizontal `Ξ`-slice factors into a finite head (zero copies within radius `R`
of `½ + it`) times a tail; RHTower proves the tail heat-positive and transfers head positivity to every
heated slice coefficient. What remains is the sign of one finite real polynomial whose degree and
multiplicities change with `t`. ALDG is the exact theory of that polynomial: which local divisors lie in
the coefficient cone, what multipliers and how much heat repair them, where the sharp obstructions sit,
and what the actual `Ξ` head satisfies unconditionally.

## 2. Objects

Variable `Y = x²` (squared horizontal displacement). Spectral copy `z = γ + iδ`; `u = γ − t`.

| Object | Lean | Meaning |
|---|---|---|
| Pair factor | `pairFactor u δ` | `Y² + 2(u²−δ²)Y + (u²+δ²)²` = conjugate pair `(Y+(u±iδ)²)` |
| Coefficient cone | `CoeffNonneg` (HTGeometry) | all coefficients `≥ 0` |
| Binomial / geometric repair | `binomialRepair α n`, `geometricRepair u δ n` | `(Y+1)^n(Y²−2αY+1)`; pair × `(Y+u²+δ²)^n` |
| Flat polynomial, reflection witnesses | `flatPolynomial`, `coefficientReflectionWitness`, `sparseReflectionWitness` | `Σ_{j≤n}Y^j`; `flat(2D) − bY^D`; `Y^{2D}−Y^D+1` |
| Polynomial heat | `forwardPolyHeat s` (HTGeometry) | `exp(s∂²)` on polynomials; semigroup |
| Masked pair | `centralMaskedPair a m` | `Y^{2m}(Y²−a)²`: adverse pair at its ordinate behind a central zero |
| Masked index / threshold | `maskedHeatIndex m t k`, `maskedPairHeatThreshold m` | quadratic sign index; first admissible heat (depth 1) |
| Hermite edge | `hermiteEdge n` | largest zero of `He_{n+1}` (probabilists') |
| Hermite extremizer | `hermiteExtremizer m`, `scaledHermiteExtremizer r m` | `He_{2m+4} − He_{2m+4}(edge(2m+2))`; monic dilation |
| Local divisor | `localDivisorPolynomial t S`, `horizontalDivisorPolynomial t S` | `Π_crit(Y+(γ−t)²)·Π_up pairFactor`; composed with `x²` |
| Disc factors | `DiscFactor r` | monic real factor, complex roots in `|ρ| ≤ r` |
| Heat-coefficient polynomial | `heatCoefficientPolynomial p j` | coefficient `j` of `heat_s p` as polynomial in `s` |
| Gaussian moments | `gaussMoment s m` | `(2m)! s^m/m!` |

## 3. Language

- **Cone**: coefficient nonnegativity of `P(Y)`; distinct from real-axis positivity `P(x²) ≥ 0`.
- **Repair**: a multiplier or heat time moving a polynomial into the cone. A model multiplier is not a
  divisor factor of `Ξ` until a source theorem identifies it.
- **Reflector**: multiplier `q` with `p·q ∈ cone ⇔ p ∈ cone` for all `p`.
- **Heat time vs Gaussian parameter**: polynomial heat `s` ↔ Gaussian variance parameter `λ = 2s`.
- **First heat time / contact**: least admissible `s`; the coefficients vanishing there.
- **Edge**: outermost critical point of `He_{n+2}`; the sharp root barrier unit.
- **Head**: radius-`R` copy set `xiSliceGaussianRadiusHead t R`; `N(t,R)` its cardinality.

## 4. Mechanisms

**Exact local algebra**
1. Pair cone is the 45° cone `δ² ≤ u²`; one real factor `Y+c` enlarges it to exactly `δ² ≤ 3u²`
   (`c = u²+δ²`); boundary `pairFactor·(Y+4u²) = Y³+64u⁶`.
2. Multiplicity cost: rescaling the pair to `Y²−2αY+1`, `α = (δ²−u²)/(u²+δ²)`, `n` real factors repair iff
   `α(m+1) ≤ m` (`n=2m`) / `α(m+2) ≤ m+1` (`n=2m+1`) — the middle coefficient decides; in geometric form
   `δ² ≤ (2m+1)u²` / `δ² ≤ (2m+3)u²`. Linear opening; never reaches `u = 0`.
3. At its own ordinate (`u = 0`) an off-line pair has the positive root `δ²`; no multiplier repairs it.
4. Central monomials `Y^a`, positive scalars, positive rescaling reflect the cone. These are the only
   universal reflectors: any other nonzero cone multiplier hides a defect in a strictly positive polynomial
   of degree `≤ 2 deg q` (flat-polynomial witness), sharp via `(1+Y^D)(Y^{2D}−Y^D+1) = 1+Y^{3D}`.

**Heat**
5. `forwardPolyHeat` is a semigroup (commutator with `X`), preserves the cone, coefficients continuous in
   `s` ⇒ admissible times form a closed ray `[τ, ∞)`. Dilation: `heat_s(p(rY)) = (heat_{sr²}p)(rY)`.
6. Masked pair: every even heated coefficient equals a positive weight × `maskedHeatIndex`, a quadratic in
   the integer index (completed square). `1/(8m+10) ≤ τ_m ≤ 1/(8m+5)`; in this bracket the integer
   minimizer is `⌊m/2⌋`, strictly, and crosses zero once ⇒ exact radical formula, a single contact
   coefficient of degree `m+2+(m mod 2)`, `8m·τ_m → 1`, depth scales exactly (`a·τ_m`).
7. Hermite normalization: `heat_{−1/2}(Y^n) = He_n`, so `heat_{−1/2}q = Σ q_j He_j`. Beyond `edge n` all
   `He_j` (`j ≤ n+1`) are positive ⇒ for `q` in the cone, inverse heat is increasing past the edge.
8. Sonin function `nHe_n² + He_n'²` has derivative `2x He_n'²` ⇒ the outermost critical value of `He_{n+2}`
   is the strict minimum on `[0,∞)`; hence the extremizer is `≥ 0` with exactly two (double) real roots and a
   strictly positive even monic cofactor.
9. Edge asymptotics without matrix models: ratio recurrence `edge = r_{j+1} + (j+1)/r_j` + AM-GM block bound,
   against `edge n < 2√(n+1)` ⇒ `edge(j)²/(j+1) → 4`.
10. Heat-coefficient polynomials: even heated coefficient `2j` is a polynomial in `s` of degree `d−j` with
    positive leading coefficient ⇒ even polynomials eventually enter the cone; a positive real root forces
    `τ > 0`.
11. Root-radius law: heated coefficient = Gaussian integral of Hasse derivatives,
    `(2l)! s^l/l!·[x^{2l}]heat_s q(x²) = ∫ g_s u^{2l} H_l(u²)`; three-region pointwise bound from
    coefficient domination (`y ≥ r`) and absolute bounds (`|y|+r`); moment ratio `μ_N/μ_l ≥ (2sN/e)^{N−l}`.

**Source**
12. The canonical finite `Ξ` head equals a positive real scalar × `localDivisorPolynomial(z²)`, no division
    by `Ξ(t)`, valid at central zeros; even Taylor coefficients = scalar × divisor coefficients; odd vanish.
13. Head factors are `DiscFactor(R²)`; degree = `N(t,R)` with multiplicity; Riemann–von Mangoldt windows
    `(t−R/2, t+R/2]` make `N(t,R) → ∞`.

## 5. Pillar theorems (all unconditional)

| Theorem | Lean |
|---|---|
| One-factor repair region `δ² ≤ 3u²` | `exists_linear_repair_iff`, `pairFactor_boundary_repair` |
| Exact multiplicity cost | `coeffNonneg_binomialRepair_even_iff`/`_odd_iff`, `coeffNonneg_geometricRepair_even_iff`/`_odd_iff` |
| Own-ordinate pair is unrepairable | `coeffNonneg_pairFactor_at_center_mul_iff` |
| Universal reflectors = positive monomials; degree `2 deg q` sharp | `universal_coefficient_reflector_iff`, `exists_positive_reflection_counterexample`, `sparseReflectionWitness_natDegree` |
| Masked-pair classification `(s ≥ 0 ∧ cone) ⇔ max(a,0)τ_m ≤ s` | `centralMaskedPair_heat_cone_classification` |
| Masked threshold: formula, unique contact, `8mτ_m → 1`, strictly decreasing | `maskedPairHeatThreshold_eq`, `centralMaskedPair_heat_even_contact_iff`, `tendsto_maskedPairHeatThreshold`, `maskedPairHeatThreshold_strictAnti` |
| Gaussian moment cone = heat cone, threshold `2b²τ_m` | `maskedPairMoments_nonneg_iff_threshold` |
| Sharp stationary/root barrier `x ≤ √λ·edge n` | `stationary_le_sqrt_mul_hermiteEdge`, `nonnegative_root_le_sqrt_mul_hermiteEdge` |
| Boundary rigidity: equality ⇒ scaled extremizer | `scaled_nonnegative_edge_root_rigidity`, `nonnegative_boundary_eq_scaledHermiteExtremizer` |
| Extremizer heat set exactly `[r²/2, ∞)`; double roots, positive cofactor | `coeffNonneg_heat_scaledHermiteExtremizer_iff`, `scaledHermiteExtremizer_positive_cofactor` |
| `edge(j)²/(j+1) → 4` | `tendsto_hermiteEdge_sq_div_degree` |
| Optimal fixed-depth heat `a/(2 edge(2m+2)²)` attained; constant 4 sharp | `isLeast_fixed_depth_heat`, `hermite_degree_constant_optimal` |
| Central masking costs asymptotically factor 2 | `tendsto_central_to_optimal_heat_ratio` |
| First heat time exists for even `p ≥ 0` with positive root | `exists_first_heat_time_of_even_nonnegative_root` |
| Exact source factorization of the `Ξ` head | `xiFiniteHead_eq_localDivisorPolynomial`, `xiFiniteHead_even_taylor`, `localDivisorPolynomial_split_coeff` |
| Source barrier `(Im z)² ≤ λ·edge(2N−2)²` at own ordinate | `radiusHead_depth_sq_le_hermite_edge` |
| Root-radius law `32r ≤ sN` ⇒ cone, any configuration | `coeffNonneg_forwardPolyHeat_expand_of_discFactors` |
| Actual head: `32R² ≤ s·N(t,R)` ⇒ cone at every height | `coeffNonneg_heat_localDivisorPolynomial_radiusHead`, `coeffNonneg_heat_sliceTruncPoly_radiusHead` |
| Large-height head and slice positivity from counting | `exists_radiusHead_heat_coeffNonneg`, `exists_xiSliceHeatTransfer_nonneg_of_head_counting` |

## 6. Tools

**Developed**
- Cone toolkit: shift/scalar/rescale reflections, `eval_pos_of_coeffNonneg`, flat-polynomial witnesses.
- Heat toolkit: semigroup `forwardPolyHeat_comp`, `coeffNonneg_forwardPolyHeat_mono`, `isClosed_forwardPolyHeat_cone`,
  `forwardPolyHeat_comp_dilation`, `heatCoefficientPolynomial`, `evenHeatMonomialCoeff`.
- Hermite toolkit: `hermiteEdge` (monotone, `< 2√(n+1)`, asymptotic), Sonin `hermiteSonin`, `inverseHeat_hermite_expansion`,
  extremizers with exact factorization.
- Disc-factor calculus: `CoeffDom`, `CoeffAbsLe` (multiplicative), Hasse-derivative bounds, `pointwise_lower`,
  `moment_numerics`, `heatCoeff_mul_eq_integral`.
- Source bridge: `localDivisorPolynomial` with `_monic`, `_degree`, `_union`, `_split`, own-ordinate root,
  `sliceTruncPoly_eq_C_mul_localDivisorPolynomial`.
- Counting: `exists_le_card_radiusHead`, `card_radiusHead_neg`, `routeKSmoothRVMCount_sub_ge`.

**To build**
- Configuration-sensitive head repair: heat bound in terms of local depth `δ`, not radius `R`.
- A source sign certificate for heated head coefficients at detector scale (depth²/log t).
- Exact cone criteria for mixed blocks (several pairs at different `u`, plus central zeros), beyond the
  single-pair and masked-pair families.
- Edge asymptotics with explicit error terms (only the limit `4` is formalized).

## 7. Open questions

1. Can the actual `Ξ` head be repaired at heat `≍ δ²/log t` (`δ` = local depth) at every large height? Counting
   gives `≍ R²/N(t,R) ≍ R/log t`; the scale gap is configuration information.
2. Which arithmetic input bounds the number of zero copies within `O(δ)` of `½ + it` (the masked/cluster
   mechanism shows this count controls the heat rate)?
3. Classify heat thresholds and contact orders for general local divisors: is generic first contact of
   positive order, as for both model families?
4. Do mixed blocks admit a closed-form threshold analogous to `maskedPairHeatThreshold_eq`?
5. Is there a reflector theory relative to restricted classes (e.g., divisors of `Ξ` heads) that escapes the
   positive-monomial rigidity?
6. Finite-height ranges: effective `R₀`, `T` in `exists_radiusHead_heat_coeffNonneg`.

## 8. Traps

| Trap | Fact |
|---|---|
| Axis positivity ⇒ cone | False: `pairFactor` is `≥ 0` on the axis but in the cone only for `δ² ≤ u²` |
| Cancel a positive factor from a cone statement | Only positive monomials reflect; witnesses of degree `≤ 2 deg q` |
| More real factors eventually repair everything | Repair region `δ² ≤ (2m+1)u²` never contains `u = 0` |
| Fixed-order coefficient checks | The obstruction sits at the middle index `⌊m/2⌋`, which moves with multiplicity |
| Contact at first heat time is order zero | Masked pair: contact at degree `m+2+(m mod 2)`; extremizer: all middle coefficients vanish, constant positive |
| Heat time = Gaussian parameter | `λ = 2s`; constants double at the Hermite/RHTower interface |
| Counting repair resolves depth | Root-radius law is configuration-blind; heat `R²/N` covers depth up to `R`, not `δ` |
| Normalized vs unnormalized head | `sliceTruncPoly` needs `Ξ(t) ≠ 0`; `localDivisorPolynomial` does not |
| Barrier degree index | Degree `n+2` uses `hermiteEdge n` (largest zero of `He_{n+1}`) |
| Masked pair as a model of `Ξ` | `MaskedPairHermite` identifies the model moment cone only; actual receiver needs a signed cofactor estimate |

## 9. Context

| Direction | Programmes (import counts) |
|---|---|
| Uses | HTGeometry 10 (`PolynomialHeatProduct`, `PolynomialHeatFactorBounds`, `PolynomialHeatNonrealCount`, `HermiteRealRoots`, `HermitePerturbationRealRoots`), RHTower 7 (finite head, zero copies, RVM remainder, masked-pair moments, head/tail transfer, Gaussian average) |
| Used by | RHTower/Heat 2, MainTheorems |

| Neighbour | Interface |
|---|---|
| `RHTower` finite-head reduction | `xiSliceHeatTransfer_nonneg_of_finiteHead_poly` turns ALDG head positivity into slice positivity |
| `RHTower/Heat/HeatRepairFromLocalDepthAndCount` | consumes the head degree law: depth-`δ` + count `64R² ≤ λN(t,R)`, `R² ≥ 2δ²` ⇒ slice positivity |
| `RHTower/Heat/AClusterHidesAnOffLineZeroFromHeat` | consumes the root-radius law: a central cluster of multiplicity `m` hides a depth-`δ` pair at heat `64δ² ≤ λ(m+2)` |
| `RHTower/Heat` detection (`re_xiSliceHeatTransfer_neg_of_slice_zero_quadratic`) | an off-line zero of depth `δ` forces a negative coefficient at heat `κ/log t`, `κ ≤ δ²/200` — the receiver ALDG repair must beat |
| `HTGeometry` | polynomial heat, Hermite real-root theory; ALDG supplies sharp edge, Sonin, extremizers |
| ArithmeticOrientationTheory / ArithmeticOrientationGeometry | spectral-support and collision counts; ALDG keeps multiplicity and exact local factors |
| SquareRootThreshold | depth/width visibility thresholds; ALDG gives the heat-side depth barrier |

## 10. Big picture

ALDG localizes the RH heat question to one finite polynomial per height and answers every purely
polynomial question about it sharply: exact repair regions, exact heat thresholds, the sharp Hermite
barrier with its extremizers, and a configuration-free degree law. The outcome is a clean separation.
Everything that depends only on degree and root radius is now unconditional, and through zero counting it
already yields heat positivity of every finite head and every heated slice coefficient at large height.

What it cannot do is reach the detection scale. The barrier and the cluster model show the true local heat
rate is depth² divided by local count; a polynomial argument that ignores where the zeros are can only see
radius, and an adverse pair masked by enough central multiplicity is invisible to heat at the same order.
The remaining RH content is therefore a statement about how many zeros of `ξ` can crowd near a point and how
deep they can sit — arithmetic input on local clustering, not further polynomial positivity.
