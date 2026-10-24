# Square-Root Threshold

Square-Root Threshold is a theory of **zero visibility**. At a given height,
what support length and arithmetic information let a test distinguish an
off-line zero configuration from one on the critical line? The programme
constructs detectors, prices their resolution and identifies what bounded
observations can miss.

Its organizing chain is **aperture → accessible lags → spectral information →
zero-width bounds**. The explicit formula turns the same chain into a demand
on prime sums. A detector explains what an estimate would exclude; it does
not supply that estimate.

## The threshold and its objects

A test supported in $[-a,a]$ has **aperture** $a$. Its autocorrelation reaches
lags at most $2a$, so the prime side reads prime powers up to $X=e^{2a}$.
Its spectral resolution is of order $1/a$.

Near height $T$, the mean zero spacing is of order $1/\log T$. The model
configuration

$$
\left\{\tfrac12\pm\delta+\frac{2\pi i k}{L}:k\in\mathbb Z\right\}
$$

has an exact hiding threshold: for $\delta>0$, its Weil form is positive on
all tests of aperture $a\le L/2$, despite the off-line depth. Beyond that
threshold it has a negative witness. At $L\approx\log T$, the test length is
$e^a\approx\sqrt T$ and the prime length is $X\approx T$. This is the
**square-root threshold**, also the diagonal scale of Dirichlet mean values.

A **configuration** is a locally finite zero multiset with the required
reflection symmetries and summability. Its **depths** are
$|\Re\rho-1/2|$; its **width** is their supremum $\Delta$. A probe **sees** a
zero when its transform is nonzero there. A **generic probe** sees every zero
relevant to its criterion. No attained deepest zero is assumed unless stated.

A **lag reading** is the Weil pairing of a source with its translate.
Two-bump tests turn its value into a two-point minor of the form. For lattice
and periodic configurations, the full family becomes an explicit Toeplitz
matrix problem.

## Foundational mechanisms

**Exact models of hiding.** Lattices and periodic depth profiles give sharp
aperture thresholds, not merely examples of poor estimates. They show why
finite-window positivity cannot bound arbitrary zero depth. They also give
explicit witnesses once the observation crosses the threshold.

**Lag detection.** Off-line contributions grow exponentially under translation.
Two-bump and difference-bump tests expose this growth through the signed Weil
pairing. For the actual divisor, generic probes give complete eventual-lag
criteria. Record estimates handle a supremum of depths that is not attained;
local mass and clustering determine the quantitative cost of visibility.

**Smooth detectors at finite cost.** Every actual off-line zero $\rho$ has a
smooth compact negative Weil witness at some aperture

$$
0<a\le C\frac{(4+|\Im\rho|)^2}{|\Re\rho-1/2|^2},
$$

with one constant independent of the zero. Smoothness is therefore not a
missing prerequisite. The stronger problem is a better aperture–height–depth
tradeoff. See
[SmoothWeilDetectorPolynomialAperture](SmoothWeilDetectorPolynomialAperture.lean).

**The width dictionary.** An aperture-independent constant in a floor of the
form $\mu(A)\ge-Ce^{2\sigma A}$ bounds zero width by $\sigma$, with the precise
domain and norm retained. Converse statements depend on normalization.
All-parity Sobolev floor rates attain $\Delta$ unconditionally in
[Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md);
the unrestricted $L^2$ converse has additional sampling or clustering issues.

**Arithmetic localization.** The explicit formula turns a translated probe
into a prime-window functional with Gamma and polar terms intact. It is here
that visibility becomes a source problem: bound a signed prime sum at the lag
and height required by the detector. Size-only Dirichlet estimates meet the
$X\approx T$ diagonal before they resolve the general configuration.

## Research questions

- Which signed prime estimate reaches beyond $X=T$ with the height phases and
  complete polar compensation retained?
- What is the optimal aperture needed to detect a zero of prescribed depth
  and height, including clustered configurations?
- Can the unrestricted $L^2$ width law be proved without a local sampling
  hypothesis, or can the relevant clustering alternative be excluded?
- Which observations control the unbounded zero tail, rather than only the
  zeros below a chosen finite height?

A single prime-logarithm grid can miss resonant or accumulating configurations.
A dense set of two-prime rational lags uses integer exponents of both signs
and supports a continuity argument; two sparse prime-power sequences do not.
Finite-dimensional positivity, eventual positivity at one fixed resolution,
and positivity at every growing resolution must also remain distinct.

## Place in the wider research

[Arithmetic Positivity Theory](../arithmetic-positivity-theory/README.md)
builds source families that must reach these detectors.
[Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md)
studies the same visibility through its ground-energy path.
[Scale-Signed Incidence Criticality](../ScaleSignedIncidenceCriticality/README.md)
formalizes what a reading can determine.
[Trans-Threshold Pair Correlation](../TransThresholdPairCorrelation/README.md)
pursues the close-prime-pair estimate beyond the Dirichlet diagonal, while
[Arithmetic Local Divisor Geometry](../ArithmeticLocalDivisorGeometry/README.md)
uses detector costs to connect local zero geometry to source certificates.

Start with the lattice threshold and two-bump mechanism. The
[programme umbrella](../SquareRootThreshold.lean) maps the quantitative
visibility, configuration and width results.
