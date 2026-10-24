# Scale-Signed Incidence Criticality

Scale-Signed Incidence Criticality asks **what a proposed argument can know
from the data it reads**. A proof may use coefficient magnitudes, moments,
positivity at a bounded aperture or zeros below a finite height. Which other
sources share those observations, and how different can their target values be?

The programme turns this question into an exact resolution calculus. Its
purpose is both diagnostic and constructive: exhibit the information lost by
a method, then identify an observation that repairs the loss and price the
precision it requires.

## Objects and language

A **reading** is a map $r:D\to O$ from a specified class of data to observations.
Its **shadow** at $d$ is the fibre

$$
\operatorname{shadow}_r(d)=\{e:r(e)=r(d)\}.
$$

For an invariant $I$, a reading certifies $I\le\beta$ at $d$ precisely when
every member of that shadow satisfies the bound. When the values are bounded,
the best possible upper bound is the **resolution limit**

$$
U_r(d)=\sup\{I(e):r(e)=r(d)\}.
$$

The corresponding infimum is the **resolution floor**. Their interval contains
all unresolved values; its endpoints and interior need not be attained.
A reading **resolves** a property when the property is constant on its fibres.
A finer reading shrinks fibres; a joint reading intersects them.

A **collapse** is a change of data invisible to the reading. If it changes the
verdict, no post-processing of that reading can resolve the verdict. Arithmetic
examples include parity flips, node deletion, bounded-aperture truncation and
insertion of zeros beyond a finite observation height.

The abstract fibre argument is elementary. The research lies in constructing
arithmetic witnesses, proving that a method really factors through the reading,
and computing sharp limits and stable repairs on the specified data class.

## Foundational mechanisms

**Collapse and refinement.** An invisible verdict-changing collapse excludes
every method depending only on the same reading. Refinement and composition
laws carry that obstruction to whole classes of arguments. See
[TheResolutionLimitOfAReading](TheResolutionLimitOfAReading.lean).

**Aperture blindness.** Lattice configurations of arbitrary depth can share
bounded-aperture positivity. More sign observations inside the same hiding
range need not improve the width bound. Unbounded information or a different
observable is required; a finite certificate is not an approximation to the
cofinal sign criterion in the sense a proof would need.

**Magnitude repairs.** In the explicit lattice and isolated-pair models, two
band energies can recover depth and scale; a third can remove unknown on-line
mass. Doubling ratios also recover information lost by the sign. These are
quantitative inverse laws with precision costs. “Magnitude-only” is therefore
not a universal synonym for blindness: one must name the magnitude reading.

**Cofinal rate information.** A growth rate is a tail invariant. Cofinal
sampling theorems hold for the stated convex profile class and separately for
the actual lattice family; bounded-range readings leave the rate unresolved.
Extending this principle to arbitrary profiles requires tail regularity that
prevents escape between samples. See
[TheRateIsACofinalInvariant](TheRateIsACofinalInvariant.lean).

**Arithmetic instances.** Complete-period or absolute-value observations can
identify parity-related sources with different receiver behaviour. In the
pronic Gram problem, adding single-modulus residue statistics makes a coarse
bilinear reading more informative. A local zero-count bound can likewise
shrink a width/energy resolution interval. Abstract compatible rate data must
not be mistaken for an actually realizable analytic divisor.

## Research questions

- Which admissible classes of readings admit an exhaustive classification of
  repairs to blindness, with quantitative precision costs?
- What tail conditions make sparse cofinal observations determine a rate for
  larger classes of profiles?
- Can a scale-matched reading of the actual prime source be measured at the
  precision demanded by the depth-inversion law?
- What is the exact resolution of the enriched actual-row Gram reading at
  the receiver endpoint, including all transfer constants?

There is no unrestricted “three ways to escape” theorem for arbitrary maps:
a map can encode the target itself. The known aperture, magnitude and
mass/dilution repairs are concrete mechanisms. Passing their information test
also does not produce the arithmetic measurement they need.

## Place in the wider research

[Square-Root Threshold](../SquareRootThreshold/README.md) supplies the visibility
models. [Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) supplies blind
nodes and phase-sensitive observations.
[Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md)
and [Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) supply
finite arithmetic readings and their receiver costs.
[Arithmetic Orientation Theory](../ArithmeticOrientationTheory/README.md)
extends this language to flips, source invariants and calibrated repair tools.

To use the programme, specify $D,r,I$ first, then give either an indistinguishable
pair or an inversion theorem. The
[programme umbrella](../ScaleSignedIncidenceCriticality.lean) maps the instances.
