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
Return-height counts and a stronger first-minimum bound remain open.

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

This is a collective auxiliary construction. Analytic extrapolation for
these jets is still required to obtain a simultaneous logarithm lower
bound; no breadth estimate or Gaudron bound is assumed.

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
