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
- **Breadth:** logarithmic prime mass of the returning coordinates, measured
  against `θ(y) = Σ_{p≤y} log p`. The required mass fraction is a parameter.
- **Depth:** phase precision of a return at a given height.
- **Bohr set:** heights satisfying a specified family of phase constraints.
- **Approximate relation:** an integer vector with small scalar product with
  the prime logarithms. Exact homogeneous integer relations are trivial by
  unique factorization. Geometry of numbers must therefore use an augmented
  approximation lattice, not a nonzero lattice of exact relations.
- **Dual polynomial:** a Dirichlet polynomial supported on integers composed
  of the selected primes; exponent vectors encode its frequencies.
- **Freezing:** replacement of orbit phases by a fixed torus point, with an
  explicit error controlled by the auxiliary's coefficients and degree.

## Questions and success criteria

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

The existing corpus supplies leads: the two-prime transcendence depth law,
Dirichlet recurrence, bounded-height rounding obstructions, reciprocity of
returns with zero clusters, exact Adams operations on torsion, and
Turán–Vandermonde elimination. Their precise statements and dependencies must
be checked before importing them as pillars of this programme.

The proposed new mechanism is collective arithmetic control: combine many
relations or count smooth-number frequencies with an error that survives
growing dimension. A successful estimate must distinguish actual prime
logarithms from rounded commensurable systems. Phase counting and two-sided
absolute estimates are admissible; spectral positivity, Landau's theorem,
and an assumed zero-free region are not producers here.

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
