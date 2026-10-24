# Arithmetic Castelnuovo–Severi Theory

Arithmetic Castelnuovo–Severi theory asks which ingredients of Weil's geometric
proof over finite fields can supply the sign of the explicit formula over
$\mathbb Z$. Its central object is the **scaling surface**: a vector space of
cycles with an intersection pairing, not a constructed scheme.

The intersection identities are available. The missing geometric input is an
independent arithmetic supply of effective cycles or sections strong enough
for Riemann–Roch and Hodge index. Defining effectivity by the desired sign only
repackages the problem.

## Objects and language

A **polar surface** has a symmetric intersection pairing and fibre classes
$H,V$ satisfying $H^2=V^2=0$ and $H\cdot V=1$. Its Castelnuovo–Severi defect is

$$
\delta(x,y)=(x\cdot H)(y\cdot V)+(x\cdot V)(y\cdot H)-x\cdot y.
$$

The **Hodge index property** is $\delta(x,x)\ge0$ for every cycle. On the
scaling surface, cycles consist of the pole plane together with Weil tests,
and the defect on tests is the Weil form. Hodge index is therefore equivalent
to RH.

**Hecke cycles** are scaled translates of tests. Their intersections give the
prime-comb Lefschetz numbers, while the archimedean term supplies adjunction.
Over a finite field, Frobenius graphs play these roles. The analogy gives
exact formulas; it does not import the ambient geometry that proves their sign.

**Effectivity** specifies which cycles have sections. Riemann–Roch supplies
effective cycles in classes of positive square, and ampleness supplies enough
positive-degree classes. **Degree** is pairing with the fibre classes;
**aperture** bounds test support. They are different parameters.

The **Hodge defect** counts negative squares of the Weil form. A spectrally
generic test has transform nonzero at every zero and can generate an orbit
that sees the full defect.

## Foundational pillars

**The geometric forcing theorem.** Riemann–Roch supply together with the stated
ample and nonnegative-degree conditions forces Hodge index. Conversely, the
abstract effectivity structure exists when Hodge index holds. On the scaling
surface this is an exact RH criterion. The research problem is a source-defined
construction meeting the conditions, not the abstract equivalence itself.

**Finite-field calibration.** Frobenius-span Hodge index is equivalent to
unitarity of the normalized eigenvalues. Its defect counts distinct eigenvalues
outside the unit circle. Fake curve data can satisfy Lefschetz, adjunction,
functional equations and integral nonnegative point counts while failing this
sign. These examples identify precisely what the span identities leave unpaid.

**The index law.** For the zeta scaling surface, the Hodge defect is the number
of distinct zeros right of the critical line. The entire defect is already
visible on the Hecke orbit of one generic test. Prime towers provide smaller
readings, with resonance and accumulation restrictions; two-prime completeness
and the classified single-tower cases are existing tools.

**Local geometry and sections.** Disjoint nonnegative tests have Bézout
positivity, and specified low-frequency-blind or finite-model subsurfaces admit
stronger geometric certificates. Section-count and sampling laws measure what
finite degree can force. They do not supply Riemann–Roch on every arithmetic
class merely because the local intersections are positive.

<a id="311-the-all-parity-critical-deficit-identity"></a>

**The attained Sobolev degree floor.** For real compact $C^2$ tests supported
in $[-A,A]$, the all-parity critical-deficit identity retains a nonnegative
horizon-resolvent term. It gives the exact endpoint law: for $\sigma\ge0$,

$$
\Delta\le\sigma
\quad\Longleftrightarrow\quad
\exists C\ \forall A,F:\quad
\Re\mathcal W(F,F)\ge-Ce^{2\sigma A}
 (\|F\|_2^2+\|F'\|_2^2),
$$

where $\Delta$ is zero width. The least exponent is attained for both odd and
all-parity tests. Unconditionally, Vinogradov–Korobov input gives the stronger
subpower factor $e^{-\kappa A^\alpha}$ relative to $e^A$, for each
$0<\alpha<3/5$. This still has exponential rate $1/2$ in width units. See
[AllParityCriticalDeficitAndEndpointSobolevLaws](AllParityCriticalDeficitAndEndpointSobolevLaws.lean).

**Rank–trace certificates.** Finite evaluation Grams also give quantitative
critical-line proportions. Their coalescence blind spot explains the two-thirds
limit of the specified subthreshold method. Improving it requires extra
spectral information or a signed prime-pair estimate, pursued by
[Trans-Threshold Pair Correlation](../TransThresholdPairCorrelation/README.md).

## Research questions

- What source-defined sections satisfy Riemann–Roch and ampleness without
  building the Weil sign into their definition?
- Which source energy pays the defect through an independent arithmetic
  inequality and leads to a usable section cone?
- Can one lower the Sobolev floor exponent below $1/2$, or establish the
  unrestricted $L^2$ width law in the clustering regime?
- Which arithmetic input improves the rank–trace certificate beyond its
  Gram-only information limit?

Neither positive point counts nor a nonnegative count of defects gives an
upper bound forcing the defect to vanish. Similarly, the attained Sobolev
endpoint does not remove its derivative cost. These distinctions determine
what a proposed geometric construction must actually prove.

## Place in the wider research

[Arithmetic Orientation Geometry](../ArithmeticOrientationGeometry/README.md)
studies scaling correspondences and individual cycle orbits.
[Arithmetic Orientation Theory](../ArithmeticOrientationTheory/README.md)
connects their invariants to source readings and section counts.
[Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md) and
[Square-Root Threshold](../SquareRootThreshold/README.md) study the same defect
through ground energy and visibility.
[Arithmetic Local Divisor Geometry](../ArithmeticLocalDivisorGeometry/README.md)
retains multiplicities and local factor transitions beyond the global index.

Start with the polar surface and finite-field calibration, then the exact
forcing conditions. The [programme umbrella](../ArithmeticCastelnuovoSeveri.lean)
maps the section, index, tower and floor theorems.
