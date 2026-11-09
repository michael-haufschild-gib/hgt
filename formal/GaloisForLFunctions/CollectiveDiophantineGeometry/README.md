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
