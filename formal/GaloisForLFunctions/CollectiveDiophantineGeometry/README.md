# Collective Diophantine Geometry of the Prime Logarithms

## Motivation

The prime orbit
\[
 t\longmapsto (t\log p\bmod 2\pi)_{p\le y}
\]
links simultaneous Diophantine approximation to large values of prime Dirichlet
polynomials. Individual linear forms control the precision of a return. The
problem here is to control how many prime coordinates can return together at
fixed precision while the number of coordinates grows.

The intended application is a sign-free route to the two-sided crude bound for
the cubic-spline trace at prime degrees. That bound decides RH. A bound for
returns alone does not: translating the zeta function horizontally preserves
its prime frequencies. The passage to zeros must use the functional equation
centred at one half and the actual arithmetic coefficients.

## Objects and language

- **Phase error:** distance from `t log p` to `2πℤ`, in radians.
- **Return:** simultaneous phase control on a specified set of primes. A first
  return must exclude the neighbourhood of `t = 0`.
- **Breadth:** weighted mass fraction of returning coordinates. The
  logarithmic profile uses `w(p)=log p`, total `θ(y)`; the critical-column
  profile uses `w(p)=p^(−1/2)`. The weight and required fraction are parameters,
  and changing them requires a proved transfer.
- **Depth:** phase precision of a return at a given height.
- **Bohr set:** heights satisfying a specified family of phase constraints.
- **Approximate relation:** an integer vector with small scalar product with
  the prime logarithms. Exact homogeneous integer relations are trivial by
  unique factorization. Geometry of numbers must therefore use the integer
  lattice with an approximation body, or an equivalent augmented lattice.
- **Rank profile:** rational rank of the integer vectors in a coefficient box
  whose scalar products with the prime logarithms are small. This records
  simultaneous small forms, beyond the smallest individual form.
- **Dual polynomial:** a Dirichlet polynomial supported on integers composed
  of the selected primes; exponent vectors encode its frequencies.
- **Freezing:** replacement of orbit phases by a fixed torus point, with an
  explicit error controlled by the auxiliary's coefficients and degree.

## Questions and success criteria

For a chosen weight `w`, let `R_w(y,δ,κ)` be the infimum of heights `t≥1`
at which primes with phase error at most `δ` carry at least `1−κ` of the
total weight below `y`. The all-prime return is the case `κ=0`. The breadth
target is `log R_w(y,δ,κ)≥y^c` for some fixed `c>0`, at constant precision
and a specified admissible mass fraction, for every sufficiently large `y`.
The admissible range of `(δ,κ)` is part of the question.

1. Count returns up to height `T` with errors uniform in the number of primes,
   including families of size comparable to powers of `log y`.
2. Control successive minima of the augmented approximation lattice as both
   prime cutoff and coefficient height grow.
3. Determine which mass fractions and height ranges admit uniform exclusion
   of heavy returns; relate these bounds quantitatively to large values of
   the prime polynomial.
4. Pass beyond the bounded-height obstruction, first to a return bound with
   `log R ≥ (log y)²`, then to `log R ≥ y^c` for some fixed positive `c`.
5. Convert breadth estimates and functional-equation information into a
   two-sided crude bound at prime degrees, using absolute convergence and
   sign-free elimination.

These are research targets, not theorem assumptions. The programme is complete
only when its counting tools and these implications are proved, including
the final arithmetic bound. A new module must improve an unbounded regime,
resolve a genuine obstruction with a substantive positive survivor, or supply
a missing mechanism with quantitative content. Finite certification, renamed
criteria, and unsupported interfaces do not meet that standard.

## Mechanisms and foundational pillars

The decision theorem is [two-sided gap iteration](TwoSidedGapIteration.lean).
For any degree set with gaps `O(x^θ)`, `θ<1`, and every `σ≥0`,

`zetaZeroWidth ≤ σ ↔ ∃ K, ∀ d∈D, |2 Re S(log d)| ≤ K d^σ`.

At current width `a`, interpolation from the degree set costs
`O(exp((a+θ−1)u))`. The absolute-convergence rate theorem then improves the
width to `max(σ,a+θ−1)`. Iterating from the unconditional width `1/2` reaches
`σ`. The analytic mechanism is a Laplace transform and residue comparison
on a horizontal strip; no one-sided Landau criterion enters. The prime
specialization at `σ=0` is RH. This proves a receiver, not its arithmetic
input.

| Pillar | Declaration | Scope |
|---|---|---|
| Absolute interpolation step | `twoSided_width_step` | width `a` becomes `max(σ,a+θ−1)` |
| Exact sampling exponent | `zeroWidth_iff_twoSided_powGaps` | every degree set with power-saving gaps |
| Prime-degree decision | `riemannHypothesis_iff_twoSided_primes` | bounded absolute trace iff RH |

Two existing return tools fix the baseline. TTPO's
`le_of_isDeltaReturn_pair` gives an explicit power lower bound in inverse
precision for two primes. TAPO's `firstReturn_le_pow` gives
`R≤Q^|P|` when `2π²≤ηQ²`, in cosine-defect precision `η`.
These statements concern different precision conventions and opposite
directions of inequality; neither supplies the missing breadth law.

Further interfaces are bounded-height rounding obstructions, reciprocity
of returns with zero clusters, exact Adams operations on torsion, and
Turán–Vandermonde elimination. Their quantitative costs must be retained
when used.

The proposed new mechanism is collective arithmetic control: combine many
relations or count smooth-number frequencies with an error that survives
growing dimension. A successful estimate must distinguish actual prime
logarithms from rounded commensurable systems. Phase counting and two-sided
absolute estimates are admissible; spectral positivity, Landau's theorem,
and an assumed zero-free region are not producers here.

### From heavy returns to absolute large values

For a nonnegative weighted column `P(t)=Σ a_i exp(itℓ_i)` of total weight
`S`, a large modulus aligns phases around an arbitrary common angle.
Returning that angle to zero needs only one-dimensional approximation.
[AbsoluteValuesForceHeavyReturns.lean](AbsoluteValuesForceHeavyReturns.lean)
proves, for every integer `Q≥1`,

`min_{1≤m≤Q} D(mt) ≤ 2Q²(S−|P(t)|)+4π²S/Q²`,

where `D(u)=Σ a_i(1−cos(uℓ_i))`. Thus prescribed cosine precision
`η>0` and missing-mass allowance `κ>0` give explicit constants

`Q=ceil(sqrt(8π²/(κη)))+1`, `c=κη/(4Q²)>0`.

Every height with `|P(t)|>(1−c)S` has a multiple `mt`, `1≤m≤Q`,
returning a subset of mass greater than `(1−κ)S`. For heights in `[A,B]`,
`A≥0`, the absolute-large-value measure is at most
`H_Q vol(R∩[A,QB])`, where `H_Q=Σ_{m≤Q}1/m` and `R` is the
heavy-return set. Constants are independent of dimension, cutoff, and
weights. The prime specialization uses the actual polynomial
`Σ_{p≤y}log p·p^(−it)` and total mass `θ(y)`.

This transfers an arithmetic return exclusion or count to complex modulus
control. It supplies neither the arithmetic estimate nor the final trace
bound. Cosine precision is `1−cos(phase)≤η`; conversion to radian precision
must be explicit.

### Rank bounds and counts for near relations

[CollectiveRankDepth.lean](CollectiveRankDepth.lean) controls independent
families of integer forms in `k` distinct prime logarithms `log p_j`, `p_j≤y`.
For `1≤r≤k` independent coefficient rows with `|ν_ij|≤H`, `H≥1`, put
`d=k−r`. Some row satisfies

`|Σ_j ν_ij log p_j| ≥ Δ(r,d,y,H)>0`.

For `d≥1`, the explicit floor is

`Δ=exp(−B_{d+1}(y)(log((d+1)r!H^r)+2))/(r!H^(r−1))`,

where `B_{d+1}(y)` is the proved explicit Baker exponent for `d+1`
prime logarithms at most `y`. At full rank, the stronger elementary floor
is `Δ(r,0,y,H)=log 2/(r!H^(r−1))`.

Cramer's rule on a nonzero maximal minor retains one pivot logarithm and
the `d` complementary logarithms. Its integer coefficient height is at
most `(d+1)r!H^r`; the adjugate costs `r!H^(r−1)`. Thus penultimate rank
uses only **two logarithms**, independently of the number of coordinates.
Full rank needs only integrality of the determinant.

For integer `H` and `ε≤Δ`, all near relations
`|ν_j|≤H`, `|Σν_j log p_j|<ε` span at most `r−1` rational dimensions
and number at most `(2H+1)^(r−1)`. A basis selected from these relations
cannot have rank `r`; an injective coordinate projection then gives the count.
The parameters retain their dependence on dimension, height, and cutoff.

This is an elementary collective consequence of the existing scalar Baker
bound. The cardinal exponent alone is also available by scalar coordinate
slicing: fixing all but `s` coordinates leaves an `s`-logarithm difference
of height at most `2sH`. Below half its scalar floor, that projection is
injective. For one omitted prime, the threshold is `log 2/2`, independent
of coefficient height. For `r≥2,H≥1`, the scalar threshold is at least the
rank threshold. The additional collective information is the dimension of
the rational span of **all** near relations, not this cardinal exponent.
The stronger first-minimum bound remains open; finite-time counts from the
collective profile are given below.

### Collective integral auxiliaries

[CollectiveAuxiliaryConstruction.lean](CollectiveAuxiliaryConstruction.lean)
separates the number `k` of prime frequencies from the `d=k−r` free
directions of a rank-`r` family of integer forms. A maximal absolute pivot
minor gives normalized projected coordinates bounded by `(r+1)q`,
independently of the matrix's coefficient height. The frequency defect is
exactly an adjugate-weighted combination of the original forms.

The integer jet system has `XS^(d+1)` equations and `(N+1)q^k` unknowns.
Explicit parameters use `h=floor(d/r)+1`; the polynomial controlling the
extrapolation length has degree `h(k+1)+k≤3k+2` when `r≥d`.
`exists_collective_auxiliary` constructs a nonzero integer coefficient
vector of bounded height, proves exact initial jet vanishing, and retains
a nonzero true value before the full prime-frequency interpolation length.
The proof uses integer Siegel, Fel'dman's common divisor, and unique
factorization followed by confluent interpolation.

### Simultaneous logarithm bounds

[CollectiveExtrapolation.lean](CollectiveExtrapolation.lean) and
[CollectiveLogarithmBound.lean](CollectiveLogarithmBound.lean) close the
analytic argument. For a rank-`r` integer matrix in `k` distinct prime
logarithms, coefficient height `H≥1`, and `W=ceil(Σ log p_j)+1`, some row
satisfies

`|Σ_j M_ij log p_j| ≥ exp(−(C′+1)(log(r!H^r)+2))/(r·r!H^(r−1))`.

Here `C′=collectiveLambdaExponent(P)` is an explicit expression in the
collective parameters, independent of `H`. The stronger normalized bound is

`Σ_i |(B⁻¹M log p)_i| ≥ exp(−(C′+1)(log|det B|+2))`.

The analytic family differentiates only in the free directions. Its
frequency defect is at most `q` times the normalized-form sum. Growth and
error bounds use the enlarged analytic box `Q=kq`, while integer Siegel
and terminal interpolation keep the original `q`. Hermite–Schwarz doubles
the zero interval at each stage; the common divisor turns small companion
values into exact zeros. The explicit thresholds force enough zeros to
contradict prime-frequency interpolation.

The parameter degree `h(k+1)+k` remains at most `3k+2` when `r≥k−r`.
The full formulas and proof are in
[the simultaneous-bound theorem](../../../docs/drafts/pipeline/3-formalized/cdg-simultaneous-logarithm-bounds.md).
This supplies collective small-form control at every coefficient height.
It supplies the arithmetic input to finite-time counting below. The
height-times-phase-error loss remains for constant-precision return
exclusion. The full-rank determinant
floor and scalar reductions remain useful additional bounds.

### Reciprocal-rank approximation profile

[ReciprocalRankBounds.lean](ReciprocalRankBounds.lean) gives a common bound
for the full simultaneous exponent. With `h=floor((k−r)/r)+1`, put

`U=10⁴(W+1)(k+1)²`, `C=U^(100h(k+1))`,
`Δ_r(H)=exp(−C(log(r!H^r)+2))/(r·r!H^(r−1))`.

Every rank-`r` integer coefficient matrix of height `H≥1` has a form of
size at least `Δ_r(H)`. For integral `H`, all vectors in the height-`H`
box whose forms have size below `ε≤Δ_r(H)` span at most `r−1` rational
dimensions and number at most `(2H+1)^(r−1)`.

The exponent degree `e=100h(k+1)` satisfies `re≤100k(k+1)`.
At rank at least half the dimension, `e≤200(k+1)`; strictly above half
rank, `e=100(k+1)`. The proof bounds the exponential step factor directly
from its binary-logarithm formula, retaining the reciprocal-rank gain
through all analytic parameters. Taking the maximum of this floor and
the scalar-elimination floor preserves both arithmetic regimes.

This controls the whole approximation body uniformly in coefficient
height and dimension. The time-window count below uses the common rational
span to bound close smooth-number pairs.
The complete proof is [CDG-EXP](../../../docs/drafts/pipeline/3-formalized/cdg-rank-sensitive-exponent.md).

### Bounded elimination onto coordinate intersections

[BoundedCoordinateElimination.lean](BoundedCoordinateElimination.lean) controls
the cost of localizing a small-form span to any coordinate set. If a finite
family `S⊂ℤ^k` has coefficient height at most `H≥1` and values below `ε>0`
under a real linear form `L`, then every intersection

`span_ℚ(S) ∩ ℚ^J`

has a rational basis of integer rows supported on `J`, with coefficient
height at most `k!H^k` and values below `k!H^(k−1)ε`.
The exact basis theorem is `exists_bounded_coordinate_basis`.

A pivot minor of order `q` gives the sharper bounds
`(q+1)!H^(q+1)` and `(q+1)!H^q ε`. Cramer's rule kills all excluded
coordinates. On the coordinate intersection, elimination is multiplication
by its nonzero pivot determinant; its image therefore spans the whole
intersection. Selecting a basis loses no surviving rank.

This supplies height control for applying the simultaneous logarithm bound
to coordinate intersections.

### Hereditary rank and weighted separation

[HereditaryRankBounds.lean](HereditaryRankBounds.lean) controls every
coordinate intersection with one threshold. For `k≥1`, put

`H′=k!H^k`, `K=k!H^(k−1)`, `δ=Δ_k(H′)/K`,

where `Δ_k` uses the full-dimension exponent `U^(100(k+1))` above.
If `V` is the rational span of the height-`H` integer forms of size below
`δ`, then every coordinate set satisfies

`2 dim(V∩ℚ^J) ≤ |J|`.

Indeed, bounded elimination gives a basis of the intersection at height
`H′` and value below `Kδ`. If its rank exceeds half its support size,
the restricted simultaneous bound has root degree one. Monotonicity in
dimension, logarithmic mass and factorials makes its floor at least `Kδ`,
a contradiction.

[WeightedCoordinateSeparation.lean](WeightedCoordinateSeparation.lean)
converts this hereditary bound into weighted selection. For every
nonnegative weight `w`, a coordinate set `J` carries at least half the
total weight, and every nonzero integer form supported on `J` of height
at most `H` has absolute value at least `δ`.

Choose a coordinate basis of `V` with minimum total weight. Its normalized
rows satisfy Hall's condition on the unchosen coordinates: hereditary rank
bounds the support of every row subset. Matching each pivot to a nonzero
unchosen coordinate and exchanging basis columns shows that the complement
carries at least half the weight. Injectivity of the chosen projection
gives `V∩ℚ^J=0` on that complement.

These are formal coefficient-body tools. Their linear exponent degree
improves the scalar Fel'dman estimate used earlier in this corpus, not the
published scalar benchmark below. They do not establish a new
constant-precision breadth bound.

### Finite-time return counts

[FiniteTimeReturnCounts.lean](FiniteTimeReturnCounts.lean) bounds the measure
of actual prime-torus returns. Let `N≥2`, `H=N−1`, and `Δ=Δ_r(H)`.
For every target phase vector and every interval of length `T≥0`,

`vol{returns at precision 1/(2N)} ≤ (5π/2)·4^k·max(T/2,Δ⁻¹)/N^(k−r+1)`.

This holds in both chord and radian precision. At `T≥2/Δ`, the relative
measure is at most `(5π/4)·4^k/N^(k−r+1)`. The observation threshold has
the exact polynomial form

`2/Δ_r(H)=B H^E`, `B=2r·r!·exp(C(log(r!)+2))`, `E=rC+r−1`,

where `C=U^(100h(k+1))` is the collective exponent above. At proportional
rank, its degree in the common base is linear in dimension.

All close frequency differences in the smooth exponent box lie in one
rational subspace of dimension at most `r−1`. An injective coordinate
projection gives at most `N^(r−1)` partners for each exponent vector.
The Fejér window inequality retains only these close pairs; the product
of coordinate geometric sums detects the return set. There is no separate
far-frequency error requiring an additional power of `N` in the horizon.

The quantitative gain concerns shrinking precision and partial-dimensional
density. At fixed Fourier height, elementary separation is stronger in the
growing-dimension regime. First-return exclusion, constant-precision breadth,
and the prime-degree trace producer remain open.
Proof and exact declarations:
[CDG-COUNT](../../../docs/drafts/pipeline/3-formalized/cdg-finite-time-rank-counts.md).

## Fixed-height mass calibration

[FixedHeightPrimeMass.lean](FixedHeightPrimeMass.lean) proves an exact law
for all geometric prime windows:

`Σ_{j≥0}(θ(xq^j)−θ(rxq^j))/x → (1−r)/(1−q)` for `0<q<r<1`.

At `x_N=exp(2πN+δ)`, take the primes in the disjoint windows
`(exp(−2δ)x_N exp(−2πj), x_N exp(−2πj)]`. Every selected prime returns at
height `1` with radian error at most `δ`. For `0<δ<1`, their logarithmic
mass fraction tends to

`M(δ) = (1−exp(−2δ))/(1−exp(−2π))`.

Thus any required fraction strictly below `M(δ)` admits height-one returns
at arbitrarily large cutoffs. In particular, more than half the logarithmic
prime mass can return with error `1/2` radian. A uniform growing lower bound
for `R_log(y,δ,κ)` therefore requires `1−κ≥M(δ)`; this necessary condition
is not sufficient.

The proof uses the prime number theorem, a summable geometric majorant,
and an exact identification with finite sets of actual primes. It is the
logarithmic-weight form of the classical nonuniform phase-distribution
phenomenon reviewed by
[Hutson, *On the distribution of log(p)*, Theorem 2.1](https://www.ijpam.eu/contents/2003-7-4/6/6.pdf).
Its role here is to calibrate the conjecture, not to claim a new breadth
estimate. TTPO's precise `MainConjecture` uses `p^(−1/2)` weights and
existentially chooses a sufficiently small missing-mass allowance; this
result does not refute that statement or transfer between the two weights.

## Tools to develop

**Return tubes and relation bodies.** Put `ℓ_p=log p/(2π)`. The integer
windings of returns up to height `T` lie in the tube
`{tℓ+e : |t|≤T, ‖e‖∞≤δ}`. Its support function is
`T|m·ℓ|+δ‖m‖₁`. Thus both the small scalar product and the total coefficient
height matter in dual approximation. Successive-minimum estimates must
control these bodies as the prime set grows; exact linear independence
alone provides no quantitative estimate.

**Smooth-number duality.** Integer exponent vectors index rational ratios
of smooth integers. Their logarithmic separation controls Fourier errors.
The required tool must retain the distribution of many such ratios rather
than replacing every denominator by its worst lower bound.

**Integer auxiliaries at sign returns.** For an integer Laurent polynomial
`F` and a sign vector `ε`, a nonzero value `F(ε)` has absolute value at least
one. Freezing near `ε` pays the coefficient mass weighted by total degree,
`Σν |cν|‖ν‖₁`. To use growing-degree auxiliaries at constant precision, one
must control their actual error collectively; discarding cancellation
recovers the bounded-height obstruction.

**Uniform zero estimates and elimination.** Zero estimates must retain
their dependence on the number of logarithms, degree and observation
height. Turán elimination on thick sets then tests whether the resulting
bound controls the infinite trace, rather than only a finite exceptional
layer. The functional equation must enter any passage from frequency
geometry to the zeros of the actual zeta function.

## Traps and calibration

- “First positive return” has infimum zero. State a nontrivial height range.
- “Every heavy subset” is ambiguous without a specified mass fraction;
  prime mass concentrates near the upper cutoff. Test fixed-height windows
  before asserting an exponential lower bound.
- Qualitative equidistribution at fixed dimension gives no uniform growing
  dimension estimate.
- Dirichlet approximation supplies an upper bound for an available return,
  never a lower bound for the first return. An exponential pigeonhole scale
  cannot be used as evidence that earlier returns are impossible.
- The absence of exact relations does not bound approximate relations.
- Bounded-height information survives rounding and cannot by itself cross
  the known polynomial return barrier.
- An identity with zeros, a conditional implication, or a reformulation of RH
  is not an unconditional producer of the required estimate.

## Place in the corpus

**TranscendenceTheoryOfThePrimeOrbit** controls depth, rounding and return
reciprocity. **PrimeTorusTheory** and **TailArithmeticOfThePrimeOrbit** supply
orbit and Euler-tail questions. **ArithmeticLefschetzStepanovTheory** supplies
torsion auxiliaries and their exactness limits. **EulerFETransportTheory**
addresses the functional-equation information needed to distinguish zeta
from frequency-identical shifts. **ArithmeticCastelnuovoSeveri** and
**ArithmeticOrientationGeometry** supply the prime-degree trace receivers.

This programme owns collective phase geometry and its quantitative tools.
Its Lean namespace and sibling umbrella are `CollectiveDiophantineGeometry`.

## External calibration

Effective local Kronecker approximation is an established subject.
[Korolev and Rezvyakova, *On simultaneous approximations to the logarithms of primes*](https://www.mathnet.ru/eng/cheb1257)
give an explicit interval length ensuring approximation to every target.
An existence bound of this kind is not an exclusion of early returns.
Growing-dimension estimates here must state both their error and their
height range before being compared with the breadth target.

Simultaneous lower bounds are also established transcendence theory.
[Gaudron, Theorem 1.1, published version](https://lmbp.uca.fr/~gaudron/art12.pdf)
has dimension factor `(10k)^(58k²/r)` for `r` independent forms in `k`
independent logarithms. At proportional rank this can improve substantially
on the scalar Baker reduction above. That theorem is not formalized or
assumed here. A collective contribution must be compared with this benchmark,
while retaining the sharper elementary bounds near full rank. Neither
comparison supplies the missing constant-precision return exclusion.

Scalar estimates also require calibration against
[Matveev, Corollary 2.3](https://www.mathnet.ru/php/getFT.phtml?jrnid=im&option_lang=eng&paperid=314&what=fullteng).
For distinct primes, that result gives every nonzero height-`H` form a
floor `exp(−C_M(1+log H))`, with
`C_M=(e/2)30^(k+3)k^(9/2)∏ log p_j`.
Thus scalar bounds already have linear dimension degree in a common base
dominating the prime logarithms. Keeping only half the weight at the much
smaller hereditary floor is not an improvement over this published result.
This benchmark is not imported as a Lean assumption. Arithmetic progress
beyond it must exploit the distribution of small forms or smooth ratios,
rather than only their worst individual separation.
