# EWU structural scalarization

Status: FORMALIZED. Capstone, dependencies, oleans, direct Lean audits, axiom audit, and umbrella wiring complete.

Goal: remove a structural obstruction in EWU beyond the completed critical one-pole and exact even-polar energy-fibre recovery results.

Constraints: unconditional source theorems, no new axioms or RH premise; no web, numerical computations, or literature novelty audit. Corpus search and Lean source are authoritative.

Conjecture log:

1. Recover an arbitrary spectral density with even rows. FALSE as stated: every even row has even real-line spectral density, whereas a general complex source need not. Survivor: only symmetrized densities can be targets.
2. Scalarize every finite positive smooth even-polar mixture exactly: its entire autocorrelation transform is the spectral square of one smooth compact even-polar source. PROVED: divisor splitting, controlled growth, contour shifting, and Fourier inversion produce the actual source. For merely C² inputs, modulus control initially gives Sobolev regularity, not automatically C²; that upgrade remains unproved.
3. An arbitrary even Hermitian factor should retain the source type. FALSE: multiplying a factor by exp(i z²) preserves its Hermitian square and evenness but can destroy exponential type. Survivor: construct a particular canonical factor with subquadratic growth before propagating the axis information.

Completed mechanism: inspect corpus factorization and source-division results; construct the selected divisor; remove the origin multiplicity obstruction; control the chosen factor; recover a compact smooth source; identify its whole autocorrelation.

## Paper proof: smooth exact scalarization

For a finite positive mixture of smooth compact even complex sources, form
P(z) = sum c_j F_j(z) conjugate(F_j(conjugate(z))). Then P is even, entire,
Schwarz-real and nonnegative on both coordinate axes. The imaginary-axis
nonnegativity uses evenness, and is essential; arbitrary real-line spectral
densities do not have this property.

1. At every nonzero point of either axis, nonnegativity along that axis forces
even zero order. At zero the order is divisible by four: even entire square
descent writes P(z)=D(z²). Positivity on both axes makes D nonnegative on the
entire real line, so D has even origin order. Composition doubles that order.
Remove z^(4k); the remaining P has positive value at zero.
2. Split the divisor: retain all copies in quadrants I and III, none in II and
IV, and half the copies on each axis. The retained divisor is invariant under
z -> -z. Its sum with its conjugate is exactly the original divisor.
3. Jensen and logarithmic buckets give summability of inverse p-th powers for
every p > 1. The genus-one product Q of the retained copies is entire and even.
Its conjugate product has the complementary divisor. Their product has the
same divisor as P. The existing even fixed-divisor rigidity, with subquadratic
proximity, makes the quotient constant. Normalize Q by sqrt(P(0)). Thus
P(z)=Q(z) conjugate(Q(conjugate(z))). Restore the factor z^(2k).
4. For 1 < p < 2, each genus-one factor has log norm at most
2 min(|z/a|, |z/a|²) <= 2 |z/a|^p. Therefore Q has growth exp(C |z|^p).
On both axes |Q|²=P. On the real axis Q has arbitrarily rapid polynomial decay;
on the imaginary axis it has a finite exponential-type bound. Apply quadrant
Phragmen-Lindelof to Q(z)(z+i)^n exp(i(T+n)z), then use evenness for the lower
half-plane. The case n=2 yields the global strip estimate
|Q(x+iy)| <= C exp(A|y|)/(1+x²), sufficient for literal compact support.
5. The inverse Fourier integral of Q is smooth (all frequency moments are
integrable), even, and compactly supported: shifting the contour to imaginary
height ±s and letting s tend to infinity makes it zero when |x|>A. Fourier
inversion identifies its entire transform with Q.
6. Consequently its autocorrelation equals the original mixture pointwise,
by Fourier inversion. All raw integer atoms, all pole values, and the complete
archimedean functional agree exactly. If the original rows are pole-free,
P(i/2)=0 and |Q(i/2)|²=0, so the scalar source is pole-free as well.

This is an actual source construction. Its conclusion is equality of the
smooth even-polar autocorrelation cone with its finite positive hull. No
positivity of the Weil functional is assumed or concluded. The C² extension
is deliberately not claimed before regularity is paid.

Formalization tasks: divisor split and growth; axis-zero multiplicities;
Fourier compact-support recovery; exact EWU source scalarization; leaf builds,
direct audits, axiom checks, umbrella wiring and cleanup.

No external novelty claim is made. Existing research Markdown is not used as evidence.

## Formal proof progress

The divisor selection, origin removal, exact Hermitian product, subquadratic
growth, quadrant propagation, and smooth compact inverse are now checked by
Lean. The origin argument is stronger than the original paper sketch: square
descent turns positivity on both axes into positivity on the entire real line,
so the descended origin order is even and the original origin order is `4k`.

The final application is `EvenSectorSmoothSourceScalarization.lean`:
`exists_smoothPolar_exact_autocorrelation` takes only a finite NNReal-weighted
family of actual smooth even-polar tests. It returns an actual smooth even-polar
test with the whole autocorrelation equal to the mixture. Its targeted olean
build, direct `lake env lean` audit, dependency audits, and axiom audit passed.
No RH or Weil-positivity conclusion is claimed.

New modules: `EvenHermitianCanonicalFactor`, `EvenHermitianAxisMultiplicity`,
`CanonicalProductSubquadraticType`, `EvenHermitianSpectralFactor`,
`EvenEntireAxisType`, `EvenEntireCompactSource`,
`EvenSectorHermitianScalarization`, `EvenSectorSmoothSourceScalarization`.

Search coverage: whole-corpus indexed source inventory complete; inverse-Fourier
deep query hit its time budget and reported partial semantic coverage. Candidate
applicability was checked against Lean source and kernel elaboration. No search
hit was treated as an established theorem without inspecting its statement.

Next conjecture after scalarization: extend exact energy-fibre recovery to one
smooth even-polar source by proving smooth exact-trace recovery. This is not
claimed here. Blind-fibre positivity also remains open.

## Exact delivered theorem and frontier change

```lean
theorem exists_smoothPolar_exact_autocorrelation
    (c : SmoothEvenPolarTestFn →₀ ℝ≥0) :
    ∃ f : SmoothEvenPolarTestFn,
      EF.weilTest f.1.1.1 f.1.1.1 =
        polarMixtureProfile (smoothPolarCoefficients c)
```

The only input is a finite nonnegative-weighted family of actual smooth compact
even pole-free sources. The conclusion supplies another actual source. There
is no spectral-factor premise, positivity receiver, RH assumption, tolerance,
or limiting approximation. The entire autocorrelation profile is identical,
so the single source preserves all arithmetic samples and archimedean energy.
This removes the finite-mixture/rank obstruction within the smooth even-polar
cone. It does not establish positivity on the blind fibre.

## Audit record

- All eight listed modules have current oleans and successful direct
  `lake env lean <module>.lean` checks.
- Final targeted build:
  `lake --old build GaloisForLFunctions.RHTower.EvenSectorSmoothSourceScalarization`.
  No full or umbrella build was run.
- All eight modules are imported by their theorem-area umbrellas.
- A `/tmp` Lean audit checked all 317 Mathlib constants resolved from the eight
  module reference indexes, including `have := @Name` declarations with explicit
  universe levels. No unresolved names remain.
- `/tmp` `#print axioms` checks for both source scalarization theorems,
  `exists_even_entire_factor_subquadratic`, and `exists_smooth_compact_source`
  report only `propext`, `Classical.choice`, and `Quot.sound`.
- No new axioms, `sorry`, `admit`, `opaque`, `unsafe`, computational experiments,
  or heartbeat/recursion-limit increases. Changed-file whitespace check passed.
- Global `scripts/formal_tools.py lint` ran. Its only errors were six unrelated
  CHMD modules unreachable from the umbrella: `CHMDArchimedeanDomain`,
  `CHMDBoundedPrimeGenerator`, `CHMDPrimeDomain`, `CHMDPrimeOperatorDomain`,
  `CHMDPrimeRowBound`, and `CHMDThetaHarmonicIdentity`. Those modules were left
  untouched. Existing large-file warnings remain.

The earlier requested `CHMDStage22PrimeWaveGrowthLawAndTwoPointSumCriterion`
is wired and has its olean. This EWU change does not modify that theorem.
