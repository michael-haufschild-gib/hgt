# Current Formal Frontier Toward Proving or Disproving the Riemann Hypothesis

## Formal research map of HTGeometry, HilbertMetric, and RHTower

## Abstract

This paper states where the project stands now. It maps every independent route toward a
proof or disproof of the Riemann hypothesis represented in `HTGeometry`, `HilbertMetric`,
and `RHTower`, together with its proved chain, endpoint, first open premise, obstruction,
and strongest surviving theorem.

The central fact is negative but precise: the formal corpus contains no unconditional
theorem of `RiemannHypothesis` and no unconditional theorem of
`¬RiemannHypothesis`. It contains a large connected atlas of exact RH equivalents,
conditional reducers, disproof certificates, and source-independent infrastructure. After
quotienting that atlas by shared unresolved premises, the live proof frontier consists of a
smaller set of genuinely different source routes. The nearest are: the literal CCM
first-clock tail/Bohr route; fixed-width rectangular Weil lower floors; all-node
Xi-Weil form positivity; theta-cusp center-mixed positivity; critical Möbius cancellation;
all-prime Sonin closure;
Suzuki full-frequency Hermite–Biehler/Ward realization; Xi Taylor core-current control;
and a new Julia compound-Poisson coherent-energy route. Operator, Deninger, Gamma–Jacobi,
Connes/prolate, and source-domain Hedenmalm routes remain structurally meaningful but
farther upstream.

The map uses exact Lean declaration types as authority. **RH equivalent** means a complete
target, not progress toward its source proof. **Open core** means first unproved premise
after proved connectors are removed. **Dead mechanism** kills only stated construction;
its strongest positive survivor remains part of frontier.

## 1. Current conclusion

Project has solved most connector problems and has not solved source-acquisition problem.
Nearest routes require one global source theorem: first-clock lower control, fixed-width
Weil floor, completed Hedenmalm positivity, critical Möbius cancellation, quantitative
Sonin closure, Suzuki full-frequency source realization, Xi-current control, or Julia
coherent-energy budget. No route supplies that theorem today.

## 2. What the foundational tower actually proves

`RHTower/RiemannTower.lean` supplies the logical skeleton:

```text
RH
↔ Xi has no zero in Re(s) > 1/2
↔ a coherent dyadic Kummer root tower exists
↔ every right-half zero multiplicity is divisible by every power of two
↔ analytic 2^k-roots exist on the right half-plane for every k.
```

`RHCharacterizations.rh_tfae` packages fifteen equivalent coordinates: right-half
nonvanishing, tower existence, all ladders, empty off-line height locus, top valuation
profile, zero census jumps, empty boxes, zero-free descent, trivial deck charge, line
holography, window certificates, and zero local modulus slopes.

These declarations are exact and valuable. They are not source producers. A proof route
must establish one coordinate from information that does not already contain Xi zero
location. The same rule applies to the hundreds of later `↔ RiemannHypothesis`
theorems.

## 3. Complete quotient of live proof routes

This section quotients thousands of declarations by their first unresolved premise. Two
criteria belong to the same route when their proved chains return to the same missing
source law.

### Route A — literal CCM first clock

**Endpoint.**

- `CCMFirstClockPublishedSourceEventuallyBoundedBelow`;
- `CCMFirstClockScaledSourceAsymptoticallyBohrAlmostPeriodic`.

Both are Lean-proved equivalent to RH.

**Proved chain.**

```text
literal published first-clock source
→ exact prime creases and von Mangoldt atom recovery
→ rational divisor moments / complete source-divisor tomography
→ Landau exclusion of a right-half divisor
→ RH.
```

The Bohr form adds:

```text
continuous asymptotic Bohr model
→ bounded source tail
→ eventual lower floor
→ RH.
```

HTGeometry proves summable-spectrum screw almost periodicity, exact Bohr coefficients,
uniqueness, recurrence, full tail closure, and Torelli recovery once an asymptotic model
exists. RHTower proves complete single-clock source/divisor tomography.

**Open core.** Prove directly from the literal source either:

```text
∃ C ≥ 0, A ≥ π/2, ∀ L ≥ A, -C ≤ B₁(L),
```

or a continuous Bohr-almost-periodic asymptote for the scaled source.

**Obstacle.** A zero-frequency top layer, accumulating spectrum, or failure of uniform
remainder separation can evade the existing AP-vanishing theorem. Torelli recovery occurs
after model existence and therefore cannot supply it.

**Assessment.** Nearest single-source route and cleanest current endpoint.

### Route B — fixed-width rectangular Weil floor

**Endpoint.** For one fixed width `L > 0`, the rectangular logarithmic Weil samples are
eventually bounded below. Lean proves this equivalent to RH.

**Proved chain.**

```text
¬RH
→ rightmost right-half Xi divisor
→ dominant rectangular Dirichlet coefficient
→ Landau singularity and shifted-zeta/Xi order contradiction
→ rectangular samples cofinally diverge to -∞.
```

Equivalent charts include multiplicative screw curvature, negative-channel abscissae,
cumulative negative mass, holomorphic continuation, and adjacent critical-Mellin block
imbalance.

**Open core.** Prove one fixed-width lower floor from prime–Gamma or theta source without
invoking global Weil positivity.

**Obstacle.** Finite-cutoff positivity has a tail budget. Recent finite Guinand–Weil
theorems quantify certification but do not produce the required cutoff-free floor.

### Route C1 — complete Xi-Weil/Hedenmalm-form positivity

**Endpoint.**

- `riemannHypothesis_iff_xiWeilPolarization_nonneg`;
- `HedenmalmXiPositiveFormWall`.

**Proved chain.**

```text
nonnegative completed form on every admissible test
→ every Xi spectral point real
→ RH.
```

**Open core.** Construct the complete positive form from literal source on its full test
class. This premise is not source-level equivalent to the theta Fourier-current premise
below; no theorem converts one missing sign law to the other without traversing RH.

### Route C2 — theta-cusp center-mixed Fourier current

**Endpoint.** `thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis`.

**Unconditional progress.**

- actual positive center-mixed theta density;
- exterior-aperture positivity;
- central frequency band through `|b| ≤ 218/25`;
- global ordered three-point PSD;
- nondegenerate two-node positivity;
- several order-three chambers;
- fourth reflection-jet Hankel positivity;
- exact incomplete-Gamma shell coordinates;
- higher-shell value quadrants and horizontal derivative directions;
- absolute far-shell convergence;
- exact coupled-cone integral normal form.

**Open core.** Prove the actual Fourier-current sign in the remaining interior
high-frequency region
`0 < a < 1/2`, `|b| > 218/25`.

**Exact unresolved data.**

1. signed ground-shell cancellation without total-variation loss;
2. transverse derivative components;
3. cofinal reflected product-fibre compensation after every finite endpoint order
   cancels.

**Obstacle.** Pointwise cone-kernel positivity is false. Every fixed finite shell prefix
has the wrong cusp asymptotic; only the infinite completion cancels it. Generic positivity,
log-concavity, and fixed local derivative order cannot close the route.

### Route D — prime–archimedean Hankel sign and reconstruction

**Endpoint.**

- `PrimeArchSourceTraceHankelIntNonnegative`;
- `PrimeArchSourceMomentHankelExactReconstructionPhase`.

The degree-tail and exact reconstruction formulations are RH equivalent.

**Proved chain.**

```text
all-polynomial prime–Gamma source Hankel nonnegativity
→ complete countable Weil source cone
→ RH.
```

HilbertMetric proves existential unisolvent reconstruction for independent features and an
equivalence at arbitrary prescribed nodes. It does not construct reconstruction on the
fixed prime–archimedean source packet or establish its all-degree sign.

**Open core.** Prove fixed-node source PSD plus exact recovery, or positivity on one
cofinal degree family, from literal prime–Gamma structure.

**Obstacle.** Low theta moments do not weaken the target. Lean proves any infinite exact
degree set already reconstructs the full cone by opposite high-degree perturbations.
Zero-selected tests are circular.

### Route D2 — continued prime–arch high-frequency ceiling

**Endpoint.** `ContinuedPrimeArchPositiveFrequencyAboveImBoundedAbove 4 ↔ RH`.

**Proved chain.**

```text
verified central band through height 9/2
+ any finite upper ceiling for continued prime–arch imaginary source above frequency 4
→ global upper ceiling by reflection
→ RH.
```

If RH is false, the source exceeds every finite ceiling at admissible points above four.

**Open core.** Construct any finite uniform upper bound from literal source. Existing
central-band sign cannot propagate itself to high frequency.

### Route E — critical Möbius/Mertens cancellation

**Endpoints.**

- critical or strict-half Mertens bounds;
- half-polylog discrete Laplace decay;
- additive triangle and second-Cesàro bounds;
- `MobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded`.

**Proved chain.**

```text
critical Möbius decay or cofinally bounded off-diagonal covariance
→ Mellin continuation / strict-right L² energy
→ ζ nonvanishing in Re(s) > 1/2
→ RH.
```

The Gamma–Hankel split removes diagonal and lower-bound obligations. Only sparse upper
bounded returns are needed.

**Open core.** Prove cofinal upper bounded returns of the actual upper-signed Möbius
Gamma–Hankel covariance, or an equivalent critical Möbius cancellation estimate, from a
nonlocal all-prime law.

**Killed mechanisms.**

- fixed-order Gowers uniformity supplies only logarithmic savings;
- second fixed-prime removal has a negative lobe;
- ternary divisor insertion pays excessive mass;
- Lambert lifting collapses to the binary source or loses two powers;
- positive semiprime LCM blocks have excessive cubic mass.

**Positive survivor.** Difficulty localizes to the supercritical LCM boundary; bounded
returns suffice, not uniform all-aperture control.

### Route F — all-prime Sonin transfer

**Endpoints.** Per-test, finite-moment, cofinal-block, and valuation-cone Sonin-to-prime
coupling interfaces, each with an RH conclusion.

**Proved chain.**

```text
positive Sonin finite/block/moment values
+ source-faithful closure onto literal prime–arch Hankel values
→ prime–arch source cone
→ RH.
```

**Unconditional progress.**

- aperture refinement is strictly subadditive;
- lost-layer coupling energy is positive and divergent;
- frequency-side logarithmic shell channel is the sole surviving completion candidate;
- inverse-dilated packet physical cutoff and physical-band error vanish exactly;
- a square-root norm floor follows from the packet-energy floor under the stated mean and
  square-tail hypotheses;
- the remaining coupling-band budget is exactly three packet-frequency norms at radii
  `rb`, `ra`, and `b`;
- squared estimates on those three terms bound the budget by
  `√Bhigh + √Bra + √Bb`;
- it blows up but grows at most logarithmically;
- failure of the final floor is reduced to a quantitative rate shortfall.

**Open core.** Prove the three spectral estimates with asymptotics strong enough after
normalization to compare coupling-energy growth with the logarithmic frequency channel
and close the completed packet floor with summable excess.

**Dead mechanisms.** Scalar, bounded, fixed-operator, Burnol counterterm, position-side,
and aperture-refinement-only completions fail. Divergence without rate is insufficient.

### Route G — Suzuki Hermite–Biehler, anti-Pick, and Ward realization

**Endpoint.** `SuzukiHermiteBiehler xiHedenmalmDeBrangesE` implies RH without a
simplicity hypothesis.

**Proved finite/source chain.**

```text
finite self-adjoint extensions and interlacing
→ finite anti-Pick identity
→ signed partial fractions and residue signs
→ measure-level anti-Pick law
→ half-plane Herglotz representation and support theorem.
```

**Required continuation.**

```text
actual monotone source eigen-coefficient law
→ source-selected chord-mass gap
→ full normalized jump Pick kernel / Ward semiboundedness
→ Hermite–Biehler for the global Hedenmalm pair
→ RH.
```

**Open core.**

1. actual source coefficient law;
2. chord-mass threshold;
3. full normalized jump kernel;
4. full-frequency global carrier identification.

**Dead predecessor.** The legacy entire compact-limit target is impossible because the
actual quotient has genuine poles. The live route is meromorphic and full-frequency.

### Route G2 — relative-Volterra phase source-germ weld

This is a separate disjunctive route; it bypasses Suzuki coefficient monotonicity,
chord-mass, Pick-kernel, Ward, and Hermite–Biehler obligations.

**Unconditional algebra.** `2V = C + iH`, with `C` and `H` self-adjoint. Under explicit
hypotheses that the reflection operator is self-adjoint and conjugates `T` to its adjoint,
`C` is reflection-even and `H` reflection-odd; odd-sector claims additionally require the
reflection square to be the identity.

**Endpoint.** `riemannHypothesis_of_suzukiVolterraPhaseEulerDefect_source_germ_weld`
concludes RH from analytic response/Weyl packages, real-zero conditions, and the seed
source-germ identity.

**Open core.** Prove the actual phase Green/Christoffel–Darboux Euler-defect source-germ
weld (`hseed`) and discharge its analytic and real-zero premises from source.

**Retired transfer mechanism.** Under the stated reflection structure, sign or positivity
of the symmetric coordinate cannot simply be transferred to the complementary phase
sector. The exact difference identity is an algebraic separation, not an unconditional
universal impossibility theorem.

### Route H — Xi Taylor/theta core current

**Endpoint.** `XiCTaylorThetaTailCoreCurrentSublinearUpper`, with several equivalent
schedule and remainder formulations.

**Proved chain.**

```text
unconditional superaccurate Taylor schedule
+ sublinear oriented core-current bound
→ absence of transverse Xi zero
→ RH.
```

**Open core.** Control the actual off-diagonal Hermitian block/top-row translation current.

**Dead shortcut.** The combined finite-arithmetic remainder is invariant under admissible
Haar-depth refinement and tends to four times the unresolved current, not zero. Prefix and
top-row decay cannot dissipate it.

**Positive survivor.** Exact refinement conservation identifies the current that must be
oriented directly.

### Route I — sharp dyadic prime window

**Endpoint.** `DyadicWeightedPrimeWindowSubpowerUpper N`.

**Chain.**

```text
sharp weighted-prime main term + subpower error for all large n
→ Landau/shifted-zeta contradiction at a right transverse zero
→ RH.
```

**Open core.** Prove the sharp dyadic error from source. Monomial-tail and finite-degree
estimates cannot reach the necessary height-linear range.

### Route J — Julia compound-Poisson coherent energy

This route is distinct from older diagonal Julia attenuation.

**Proved chain.**

```text
literal compound-Poisson equilibrium source
→ exact variance 3/2
→ normalized Julia defect kernel
→ positive definiteness on the real line
→ bad-origin-correlation² ≤ coherent cross-prime energy
→ negative completed source forces a squared excursion into that energy.
```

The equilibrium kernel is now an actual characteristic function, not only an abstract
positive-definite kernel: source gives an explicit compound-Poisson law with zero atom
`1/(2√2)`, a square-biased law with density `(2/3)x²`, and an independent centered
triangular-clock realization. `CharacteristicDefectGramCapacity` packages the universal
finite-second-moment anchor-correlation bound used directly by RHTower.

**Open core.** Prove a global coherent bad-energy budget that forces vanishing or bounds
the excursion by available positive mass, including the finite-packet-to-infinite-source
limit.

**Obstacle.** Diagonal attenuation and scale-four/KMS decompositions preserve bad signs.
Only a non-diagonal cross-prime or inter-scale inequality can close the gap.

**Status.** Major literal-source advance; open global energy budget prevents RH closure.

### Route K — quadratic spectral realization

**Endpoint.** `XiQuadraticSpectralReality ↔ RH`.

**Needed chain.**

```text
source-built closed self-adjoint realization of -D(D+1)
+ every Xi zero supplies ρ(ρ-1) in its spectrum
→ real quadratic spectral parameter
→ strip and no-real-zero facts
→ RH.
```

**Open core.** Construct operator, domain, and scattering determinant from arithmetic
source without selecting the Xi divisor. The current module explicitly asserts no such
realization.

### Route L — Deninger/Hodge/cohomological realization

**Endpoint family.** Oriented Hodge, Weil-transport, dense-range, resolvent, and
divisor-spectrum inclusions, all conditionally implying RH.

**Needed chain.**

```text
literal arithmetic relevant complex
→ positive Hodge/Kähler polarization
→ one-way inclusion of every Xi divisor eigenvalue
→ spectral real-part 1/2
→ RH.
```

**Unconditional infrastructure.** Weil-height/Kummer groups, L¹/L² completions, real
scalar extension, a completed real Hilbert/Kummer inner-product package, radial flow,
Poisson realization, polar-sign correction, and Fredholm kernel reductions.

**Open core.** Meyer-complex comparison; radial Schwartz domain; nuclear topology and
closed range; nonradial acyclicity; cup/trace/flow/Hodge transport; nuclear
almost-idempotence; middle-kernel vanishing; and source-to-Xi spectrum inclusion.

### Route M — Gamma–Jacobi singular reader

**Unconditional progress.** Odd artanh heads converge to the source coordinate; adaptive
head plus residual recovers the full coefficient; singular normalization is forced;
rank-one Szegő tail transgression and adjacent residual coordinates reconstruct prime
labels; reciprocal counterreader nodes form a Blaschke-admissible boundary sequence.

**Needed chain.**

```text
joint infinite-index Krein head/tail object
→ completed Euler cyclic reader
→ positive jet-opening flux
→ fibre-pointed Berezin orientation
→ RH.
```

**Open core.** Construct the joint object, prove convergence of finite inner factors, and
identify the forced outer factor.

### Route N — Hedenmalm all-prime normal boundary

**Endpoint.** `XiCZeroHedenmalmPrimeNormalSubLogSquare`.

**Proved identity.**

```text
prime-normal energy
= vertical clock energy + radial reflected energy.
```

Sub-`(log X)^2` energy at Xi zeros forces the centered imaginary coordinate to vanish.

**Open core.** Prove a uniform source-domain sub-log-square estimate for every vector in
the closed theta Grushin domain, before specialization to a root, retaining the full Jordan
tower.

**Dead predecessor.** Strict descent of every named Xi root block into the
prime-harmonic Besicovitch domain is already RH equivalent.

### Route O — Connes restricted-Weil/prolate limit

**Endpoint.** `ConnesXiGroundStateLimitWall ↔ RH`.

**Open core.** Prove a source-locked comparison between the actual restricted-Weil ground
state and the prolate seed, including the two prolate-to-Hermite coordinate limits and
rigorous convergence of the finite spectra/determinants to Xi.

**Circularity warning.** Arbitrary real-zero entire approximants are an RH mirror:
under RH, constant Xi-based sequences witness the property.

### Route P — completed-seam Thorin/Markov representation

**Endpoint.** Compact Thorin exponent and compact Markov germ representations are RH
equivalent.

**Proved content.** Compact moment determinacy makes any witness unique; RH supplies the
canonical divisor measure.

**Open core.** Construct the literal compact positive carrier from source without using
the Xi divisor.

**Obstacle.** Uniqueness closes alternative-carrier freedom; it cannot establish
existence.

### Route Q — theta–Cassini boundary saturation

**Endpoint.** `ThetaCuspCassiniInwardBoundarySaturated ↔ RH`.

**Unconditional progress.**

- aperture-independent positive theta carrier;
- all raw latent Hankel blocks strictly positive definite;
- exact nonlinear inward response;
- unique entire continuation from the boundary germ;
- a unique power `α_* > 1` whose calibrated reciprocal pushforward matches degrees zero
  and one.

**Open core.**

1. test and then control the `α_*` carrier from degree two onward;
2. construct a fixed compact positive Markov carrier for the actual response; or
3. prove the boundary Jensen/jet saturation inequality directly.

**Dead producers.** Raw reciprocal square-gap carrier has wrong mass; calibrated
`α=1` carrier fails at degree one; one-particle infinite divisibility fails by atomic
support. A two-particle completion survives but has no transform identification.

### Divisor-fed prime-seam submass coordinate

**Endpoint.** `XiPrimeSeamPairEnergySubmass ↔ RH`.

**Unconditional progress.** The degree-one Euler functional-equation coefficient energy
is identified exactly with a horizontal prime-seam weighted norm square. Prime-pair
difference energy divided by reciprocal prime mass converges to twice this quantity, and
the energy controls `(Re(ρ)-1/2)^2 (log 2)^4` on a divisor fibre.

**Classification.** This is not yet a live source route. The predicate quantifies directly
over `XiDivisorSupport`, and its fibrewise content is exactly `Re(ρ)=1/2`; even the
first-coefficient energy remains parameterized by `ρ`.

**Potential promotion condition.** Construct a source-to-divisor-fibre all-prime/Sonin
operator that produces submass growth or zero first-coefficient energy without selecting
the Xi divisor.

**Obstacle.** Existing identities expose and coerce the quantity but do not orient it on
Xi fibres. An outer Euler modulus or prime-seam coupling remains unproduced.

### Route S — source algebraicity and dynamical mirrors

This quotient includes Arakelov power orbits, Hurwitz anchor circuits, Böttcher charges,
Kummer/Jordan conditions, valuation sectors, deck charges, and related dynamical
coordinates.

**Status.** Exact consequence atlases or fringe rigidity routes.

**Open core.** An independent source theorem must produce algebraicity, integrality,
contractivity, finite differential capture, or divisor-preserving dynamics on Xi fibres.
No such producer exists. Expected coordinates are often transcendental, so these are not
leading routes.

### Secondary criteria with no new primitive source

The following families reduce to Routes A–S or remain bare equivalences:

- Li coefficient and shifted reciprocal moment criteria;
- Salem integral exclusion;
- Hardy and Colombeau closure criteria;
- theta-infinity and arbitrary-length mollifier criteria;
- Burnol co-Poisson scalar/parity criteria;
- OPUC and phase-adapted Prouhet terminal identities;
- Hurwitz FE/Schwarz seam, current, and energy charts;
- outer Euler modulus × prime-seam coupling;
- divisor-fed Xi prime-seam submass;
- determinant-line and spectral-flow no-first-crossing charts;
- function-field `q → 1` degeneration;
- hyperbolic/adelic scattering;
- multivariate stable-section models;
- radial Jensen/Schur norm gaps;
- Böttcher, QECC, observer, and universality atlases.

They remain useful coordinates. None adds an independent source producer.

## 4. Role of HilbertMetric

HilbertMetric has no RH declaration. Its mathematical statements form a source-independent
mechanism layer, except that `FourthCurvatureMixture.lean` currently has an implementation
dependency on an HTGeometry integral inequality.

### Closed infrastructure

- finite Gaussian Fock determinant laws;
- CCR dimension/variance identities on invariant blocks;
- rank-one Gaussian metric curvature;
- symmetric-Fock lowering and phase classifications;
- Slater/Plücker and quasi-free rank/variance laws;
- finite unisolvent evaluation and prescribed reconstruction;
- exact three-point determinant/angle/Riccati criteria;
- fourth-reflection and positive-mixture transport;
- dense scalar functional rigidity;
- character-intertwiner trace obstruction.

### Direct RH handoff

```text
HilbertMetric.PrescribedEvaluationReconstruction
→ RHTower.PrimeArchHankelDeterminantCriterion
→ PrimeArchSourceMomentHankelExactReconstructionPhase
↔ RH.
```

Existence of some unisolvent nodes is closed, and reconstruction at prescribed nodes is
characterized exactly. Reconstruction and PSD for the fixed prime–arch source nodes are
not proved.

### Complete direct import handoffs

The direct surface is 3 HTGeometry consumers and 25 RHTower consumers through 30 import
statements. Only `PrimeArchHankelDeterminantCriterion` directly reaches an RH equivalence.

| Handoff class | Exact direct consumers |
|---|---|
| HTGeometry reconstruction/energy | `BipolarGramDriftAnomaly`; `ContinuousCofiniteRealHilbertReconstruction`; `PointedCollisionIncidenceLinearBridge` |
| RHTower reconstruction/freeness | `GammaShiftDirichletLSeriesArithmeticHilbertReconstruction`; `GammaShiftZetaJetArithmeticHilbertReconstruction`; `PrimeArchHankelDeterminantCriterion`; `XiJetFreeness`; `XiMobiusContinuousApertureSzegoMetric`; `XiTransverseValuationCanonicalReconstruction` |
| Hedenmalm/theta low-block geometry | `HedenmalmCenterMixedCorrelationAngle`; `HedenmalmCenterMixedFourthJetCusp`; `HedenmalmCenterMixedFourthJetCuspClosure`; `HedenmalmCenterMixedLocalThreePoint`; `HedenmalmCenterMixedRaywiseCoalescedCone`; `HedenmalmCenterMixedThreePoint`; `HedenmalmCenterMixedUniformCoalescedSquare`; `SquaredXiThreePointOrbitPositivity`; `ThetaCuspFullReflectionFourthTuran`; `ThetaCuspReflectedRiccatiAngle` |
| Gaussian curvature | `GaussianMetricHermiteStableRankFractureUniversalityLaw`; `HermiteEvenGaussianMetricCurvature`; `XiTransverseValuationGaussianCurvatureHilbertPhase`; `XiTransverseValuationGaussianCurvatureSignDuality`; `XiTransverseValuationGaussianRadicalConnector` |
| Fock/Plücker/phase | `GammaSewnFourRatePluckerConnector`; `HermiteEvenSlaterPluckerConnector`; `UniversalPhaseCoherenceEntropy` |
| Rigging no-go | `ArithmeticSchurExactNormRiggingNoGo` |

### HilbertMetric-facing downstream boundaries

**Internal HilbertMetric mathematics:**

1. affine-dimension-three Gaussian curvature boundary;
2. arbitrary-rank Gaussian curvature classification.

**RHTower literal-source cores using HilbertMetric infrastructure:**

3. all-order prime–arch Hankel reconstruction;
4. all-order Hedenmalm positivity beyond closed low blocks;
5. source-specific CCR/Fock realization with a decisive sign;
6. source filling/rank/phase estimates.

**Category and interface boundaries:**

7. a viable post-scalar rigging category;
8. sufficiency, not merely necessity, of matching characters.

## 5. Role of HTGeometry

HTGeometry supplies rigidity, faithful encodings, source decompositions, exact no-gos,
moment determinacy, Bohr recurrence/Torelli machinery, and the new Julia positive-definite
source.

### Material HT-enabled routes

- first-clock Bohr model and recurrence: Route A;
- compact moment/Thorin determinacy: Route P;
- Julia coherent-energy route: Route J;
- Euler-tail faithfulness and source tomography feeding prime/Gamma programs;
- prime KMS and orientation obstruction;
- source-specific Pick obstruction;
- moment and reporter guardrails preventing false source identifications.

### Upstream but not yet RH-connected HT programs

- Gamma differential hypertranscendence;
- reflected-digamma orientation;
- conversion of the now-proved literal-zeta Gamma-field nonrelation into divisor or
  zero-location information;
- Stanley–Reisner/boundary-wedge dimension;
- generic monodromy rigidity;
- Lindelöf exponent campaign.

These are not counted as current RH proof chains because no exact source-to-RH handoff is
present.

The literal zeta specialization is closed only for the exact Gamma-jet normal form stated
in `ZetaGammaFieldHypertranscendence.lean`: its denominator, dominant-monomial,
noncancellation, and differential-monomial hypotheses must not be erased. Controlled
digamma quotient valuations and centered coefficient algebraic independence are also now
proved, but neither has an RH handoff.

Dirichlet exponents are now identified exactly as Bohr-hull frequencies under uniform
Dirichlet approximation, closing the exponent-to-spectrum link in the Gamma-field
nonrelation chain. Vertically flat residuals are stable under differences, nonzero rational
factors, and unit translation, and no nonzero polynomial is vertically flat. Remaining
analytic assembly is evaluation/translation compatibility for rational digamma jet
polynomials. Universal-to-generic centering and coefficient-substitution injectivity are
also present; explicit algebraic independence of the centered generic coefficient family
still needs final assembly and still has no Xi-source specialization.

### Highest-value HT-specific missing inputs

1. first-clock lower floor or Bohr model;
2. completed prime–Gamma sign combining prime and archimedean terms;
3. cross-prime Julia energy budget and infinite-packet limit;
4. non-diagonal KMS/inter-scale inequality;
5. contractive or variation-diminishing Möbius inversion;
6. literal compact Thorin representation;
7. honest Xi-linked indeterminate Hamburger family;
8. completed Euler cyclic reader with infinite-index Krein packaging;
9. convergence and outer factor for finite prime-clock inner factors;
10. a theorem converting Dirichlet/Gamma nonrelation into zero-location information;
11. actual two-variable HT/SR realization;
12. literal centered-jet surjectivity;
13. Lindelöf second-spacing plus across-class cancellation.

## 6. Dead routes: exhaustive mechanism map

A route is retired only at the quantifier level proved or paper-falsified. Each entry
therefore lists the surviving positive theorem.

### 6.1 Universal finite selectors and local readers

**Dead.**

- finite rank-one selectors;
- finite seam jets and fixed local derivative order;
- finite-dimensional linear reporters;
- finite-codimension landscapes;
- finite reciprocal moments and finite polynomial degree tests;
- finite divisor prefixes;
- scalar orbit quotients and unweighted invariant `ℓ²` lifts;
- invariant-fibre “deciders” that merely restate the target.

**Reason.** Explicit no-free-lunch, blindness, completion, gauge, and tail-insertion
theorems preserve all finite observations while changing the unresolved divisor datum.

**Survivor.** Exact sharp resolution/codimension bounds, weighted orbit invariants, and
the conclusion that any viable selector must be infinite, divisor-sensitive, and
source-faithful.

### 6.2 Universal Gaussian/CCR/Fock signs

**Dead.**

- universal Gaussian bandwidth log-concavity;
- unrestricted finite full-CCR tuples;
- universal quasi-free Fano nonnegativity without filling;
- compressed-annihilator universal positive defect;
- coherent row/column compensation as a universal sign law;
- all finite annihilation-invariant-subspace sign laws;
- pairwise commutativity as an identification of defect with half the mixed-commutator
  square;
- arbitrary commuting, nilpotent, symmetric-graded tuples as a universal sign producer;
- direct Fock-square repair; cubic/triadic source-incomplete replacements.

**Lean-certified falsifiers.** Degree-five ambient-16 Gaussian positive log-curvature;
finite full-CCR nonexistence; explicit two-mode quasi-free margin `-2`.

**Paper-level retirements.** The compressed-annihilator, row/column compensation,
commuting-tuple, and universal finite invariant-subspace mechanisms are paper-level
falsifications or implications unless a separate Lean declaration is cited.

The proposed complete-Bernstein Gaussian scale law is also dead by a symbolic
equilateral-three-point paper falsifier, but no matching Lean declaration was found; its
status is PAPER-FALSIFIED, not formally certified.

**Survivor.** Rank-one strict concavity, intrinsic-dimension power concavity, invariant
block CCR, sharp filling threshold, rank/phase defect classifications, stable higher-rank
fracture, and the paper-level exact row–column decomposition. The strongest formal
quadratic survivor is the complete graph completion: annihilation invariance and the
determinant law `t^(e+m) det(tI + LᵀL)`.

### 6.3 Generic positivity, moment, and Pick arguments

**Dead.**

- “hypertranscendence implies Hankel positivity”;
- coefficient positivity or complete monotonicity alone;
- axis positivity as a substitute for a Hankel cone;
- generic positive/log-concave Schwartz shape as Fourier positivity;
- direct Pick-kernel positivity at a quadratic boundary contact;
- Schur/Nevanlinna collapse after assuming an RH-equivalent singularity statement;
- one-state universal KMS closure;
- Gamma-field asymptotic valuation stopped modulo a vertically flat residual, without
  shift-stable elimination and evaluation/translation compatibility.

**Survivor.** Exact counterexamples and boundary-contact signs identify missing literal
source structure; corrected Krein/indefinite kernels remain possible.

### 6.4 Hedenmalm/theta finite-shell mechanisms

**Dead.**

- shellwise sign as the completed sign;
- every fixed finite canonical shell prefix;
- fixed finite endpoint asymptotics;
- order-three positivity as RH closure;
- total-variation domination of the exceptional ground shell at the verified cutoff;
- automatic inward transport from boundary positivity;
- one-particle infinite divisibility of the seam carrier.

**Survivor.** Infinite-tail seam cancellation, global three-point PSD, fourth-jet
positivity, exact higher-shell quadrants, one compact ground defect, and the coupled
completed integral.

### 6.5 Sonin and Suzuki finite completion mechanisms

**Dead.**

- Sonin aperture refinement alone;
- scalar/bounded/fixed-operator/position-side Sonin completion;
- second-order Koplienko subtraction that deletes required linear terms;
- legacy Suzuki entire compact limit;
- scalar jump/Herglotz identifications with mismatched coordinates;
- finite signed-frequency repairs;
- local differential corrections;
- unrenormalized cofinal Bianchi mass;
- atomwise finite causal splice;
- raw completed-Mellin positive-domain proposals;
- transfer of symmetric Volterra positivity/sign to the complementary phase coordinate
  under the stated reflection hypotheses.

**Survivor.** Frequency-side logarithmic Sonin channel; meromorphic Suzuki anti-Pick,
Herglotz, full-frequency Ward, and projective/Plücker structures; self-adjoint relative
phase coordinate, complementary parity sector, and independent source-germ-weld route.

### 6.6 Möbius/additive cancellation shortcuts

**Dead.**

- fixed-order Gowers savings;
- two-prime positivity by repeated Euler removal;
- ternary slack insertion;
- Lambert ternary lift;
- blockwise LCM/cubical positivity;
- numerical “reciprocal-sum contradiction”.

**Survivor.** Gamma–Hankel off-diagonal bounded-return target, supercritical LCM boundary
localization, and exact positive Liu reciprocal-square gap.

### 6.7 Moving completed-source polynomial parity

**Proposed chain.**

```text
far-right positivity + right-even factorization
→ central source Hankel positivity
→ RH.
```

**Verdict.** PAPER-FALSIFIED. For `P=X`, the second completed moment is positive at the
center, negative at 10, and positive far right, forcing odd-multiplicity crossings and
contradicting even factorization.

**Lean nuance.** Lean proves center positivity and conditionally refutes the factorization
given the negative value at 10; the explicit negative estimate itself is not formalized.

**Survivor.** Four-crossing law and signed crossing structure. Do not erase crossings;
classify them.

### 6.8 Axiomatic and deformation routes

The abstract “positive generalized prime system + Riemann functional equation” lane is
circular-or-false.

**Dead.**

- moving zeros of zeta inside the positive-measure axiom class;
- continuous or nonsummable divisor deformations preserving all axioms;
- intrinsic Landau analysis of the whole source, whose pole at one dominates;
- Hamburger uniqueness as an RH shortcut;
- even/odd Weil splitting as a new lever;
- positive-definiteness tested only in the already zero-free half-plane;
- heat/homotopy flow inside the same domination class.

**Survivor.** Landau deformation rigidity and sharp pole-order budgets classify how a
positive generalized system can deviate. A from-scratch Beurling system remains a
dichotomy about the strength of the axiom class, not a proof route for zeta.

### 6.9 Source algebraicity and representation theatre

**Dead or unsupported.**

- Arakelov integrality without a source producer;
- zero-fed Deninger eigenmodels;
- divisor-preserving dynamics that read the divisor they must control;
- abstract witnesses with degenerate inhabitants;
- scalar gluing, orbit shape, ramification quotient, or connected deck charge as
  orientation;
- function-field, scattering, QECC, Böttcher, observer, and physics analogies without a
  typed arithmetic source functor.
- genuinely unbounded closable scalar-current rigging on a dense domain: every closed
  densely defined real scalar functional has full domain, and on a Banach source every
  closed or closable dense scalar functional extends boundedly and continuously;
- invertible linear intertwiners across a trace/character mismatch: one mismatched element
  excludes every invertible intertwiner.
- complete Hochster derived topology plus Stanley–Reisner differential matroid and embedded
  differential field as an orientation selector: arbitrary finite negative residue surgery
  preserves all three while changing the Herglotz chamber.

**Survivor.** Exact consequence atlases, bounded continuous scalarization, character
equality as a necessary—but not sufficient—compatibility condition, and an exact
topology–orientation product classification. Live rigging must leave the scalar closable
Hilbert category. These structures become RH routes only after a new source construction.

### 6.10 HTGeometry direct RH-adjacent failures

HTGeometry adds:

- differential-field real-zero nonidentifiability;
- Gamma-hypertranscendence/Hankel-sign independence;
- localized Selberg fixed-ratio kernel failure;
- multiplicity-only bosonic horizon;
- polarized infinite-pair orbit-lift failure;
- Sonin second-order regularization;
- capacity growth from hypertranscendence.

Their positive survivors are, respectively: divisor-sensitive gauge classification;
source-specific sign necessity; sharp flat inverse; multiplicity classification; weighted
invariants; exact residual correction; and clock-dilation norm rigidity.

Fifteen additional adjacent physics/algebra mechanisms have no exact RH endpoint:

- `actuality-factorization-interchange-law`;
- `albert-hessian-as-rank-six-event`;
- `autogenic-time-law-conjecture`;
- `clock-geometry-conservation-forces-einstein-dynamics`;
- `finite-cross-law-interference-without-containing-theory`;
- `fixed-carrier-quadratic-variation-as-gravity`;
- `gamma-digamma-mixed-jet-matroid-universality-law`;
- `higgs-tangent-universal-soldering-topology-law`;
- `noncommutative-holonomy-word-growth-differential-innovation`;
- `operational-history-reconstruction-conjecture`;
- `polarized-framed-derived-source-character-principle`;
- `projective-source-directions-are-color`;
- `ratfunc-cyclic-fixed-field-universality-law`;
- `source-reporter-counts-are-particle-indices`;
- `universal-bare-source-effectivity-reconstruction`.

They remain retired and are excluded from the active RH map until an exact source handoff
exists.

### 6.11 Named RHTower no-go modules and exact survivors

| Module family | Retired mechanism | Strongest survivor |
|---|---|---|
| `EdgeScaleNoGo` | sub-resolution edge selector | sharp phase resolution `π/ρ₀` |
| `EndpointNoGo` | fixed deck class determines endpoint sign | all four sign pairs occur |
| `JointReadingNoGo` | a joint scalar reading selects the branch | exact `C₂×C₂` orbit obstruction |
| `LandauShadowNoGo` | global orientation from the Landau shadow | parity localizes the fixed locus |
| `PinnedAffineWeldBoundaryNoGo` | raw pinned affine source selects a weld | nonzero Fitting class survives, but raw source activates everywhere |
| `PrimeDivisorAtomsNoGo` | individual prime-factor atoms detect the divisor | prime atoms are analytic units |
| `SeamArchimedeanNoGo` | seam support alone transfers archimedean orientation | exact support/sampling quotient separation |
| `ShortWindowNoGo` and `ShortWindowNoGoGeneral` | short local windows select the global phase | local/spread-cone obstruction |
| `SpurNoGo` | one-pair preservation under the spur construction | sharp geometric spur law |
| `WeldGermOrientationNoGo` | scalar or vector germ reader recovers orientation | symplectic area survives and requires at least two arithmetic directions |
| `WindowSymmetryNoGo` | a larger hidden window stabilizer supplies phase | stabilizer is exactly identity/mirror |

### 6.12 Additional structural retirements

Current corpus also retires the following mechanisms at their exact stated scope:

- polynomial surgery that leaves the Dirichlet-series class;
- scalar gluing that records orbit shape but not orientation;
- ramification data descending only to the orbit quotient;
- positive weld metrics attempting to recover Krein signature by congruence;
- conservation of connected deck charge as a zero selector;
- rational coefficient charge, which disappears although integral charge survives;
- constant sources, which collapse to scalar sums;
- positive prime-rate blocks, which are mutually congruent;
- weld/Hankel finite-block combinations required to be simultaneously positive, finite,
  and source-faithful;
- finite repaired frequency packets, whose infinite replacement demands the missing
  admissibility condition;
- zero-frequency reservoirs that are target equivalent or collapse to the `dx/x`
  boundary;
- boundary-Weyl, Stieltjes, contractivity, and finite-KMS atlases used without an
  independent source producer;
- generic Julia “coherent capacity” based only on Gram/Cauchy–Schwarz rather than the
  literal equilibrium source.

## 7. Disproof frontier

No unconditional disproof is present. The corpus nevertheless has exact witness-producing
interfaces.

### Direct witness

```text
produce a nontrivial zeta/Xi zero ρ with Re(ρ) ≠ 1/2
→ ¬RH.
```

### Equivalent finite or typed witnesses

| Certificate class | Representative exact interface | Classification |
|---|---|---|
| Completed-flux/Laguerre failure | `completedFluxTaylorCoeff_two_line_re_pos_not_RH` | typed negative certificate |
| Negative completed source jet | `not_riemannHypothesis_of_completedSourceJet_neg` | typed source certificate |
| Prime continuation nonanalyticity | `not_riemannHypothesis_iff_primeContinuationNonanalyticPhaseUniversalCertificate` | exact equivalent certificate |
| Positive Ward endpoint index | `xiEndpointWeightedWardIndex_pos_iff_not_rh` | exact equivalent certificate |
| Nonzero SEM Fitting charge | `not_riemannHypothesis_iff_exists_semHoleFittingCharge_ne_zero` | exact equivalent certificate |
| Heat-Hankel negativity | negative heat form, Turán defect, or trace determinant | finite analytic certificate |
| Shifted-reciprocal negativity | negative reciprocal Hankel quadratic | finite analytic certificate |
| Rectangular/first-clock divergence | cofinal negative rectangular floor or first-clock failure | source-asymptotic certificate |
| Bernstein/source-sector failure | persistent negative mass or sector violation | source-asymptotic certificate |
| Right-half divisor/ladder | nonempty right-half Xi copy and sharp ladder failure | divisor-fed mirror |
| Hurwitz orientation/modulus slope | positive orientation energy or nonzero slope defect | divisor-fed mirror |

Every current theorem either derives these from assumed `¬RH` or concludes `¬RH` from
an unproduced certificate. Thus the disproof open core is a concrete certified negative
witness, not a missing logical connector.

## 8. Research hypotheses that would create a leap

The following questions remain unanswered by both formal corpus and current primary
literature. They are stated at source level, before specialization to Xi zeros.

### Tier 1 — shortest RH chains

1. **First-clock lower-floor theorem.** Is the literal published first-clock source
   eventually bounded below?
2. **First-clock Bohr theorem.** Does its scaled source admit a continuous
   Bohr-almost-periodic asymptote?
3. **Fixed-width Weil theorem.** Can one fixed rectangular logarithmic family be bounded
   below from prime–Gamma source alone?
4. **Critical Möbius theorem.** Can the actual Gamma–Hankel off-diagonal covariance return
   to a bounded upper region cofinally near the critical exponent?
5. **Hedenmalm completion theorem.** Is the completed center-mixed Fourier current
   nonnegative in the interior high-frequency corner?
6. **Julia energy theorem.** Does a global coherent cross-prime budget rule out negative
   completed-source excursions?
7. **Prime–arch high-frequency ceiling.** Can literal source supply any finite uniform
   upper bound above frequency four?

### Tier 2 — source-to-operator or source-to-form construction

8. All-prime Sonin closure with the required quantitative rate.
9. Suzuki source coefficient monotonicity, chord-mass gap, and full jump Pick kernel.
10. Relative-Volterra phase Euler-defect source-germ weld.
11. Source-built all-degree prime–arch Hankel PSD/reconstruction.
12. Source-built self-adjoint quadratic-scale operator with Xi spectrum inclusion.
13. Deninger relevant-complex comparison, nuclear estimate, Hodge transport, and kernel
    vanishing.
14. Uniform source-domain Hedenmalm prime-normal sub-log-square estimate.
15. Joint infinite-index Gamma–Jacobi Krein reader and forced outer factor.
16. Restricted-Weil/prolate ground-state comparison and rigorous finite-to-Xi convergence.
17. Literal compact Thorin/Markov carrier for the completed seam.

### Tier 3 — new structure that could unlock Tier 1 or 2

18. Non-diagonal inter-scale KMS inequality neutralizing persistent bad layers.
19. Contractive or variation-diminishing Möbius inversion of Gamma occupation.
20. Source-stable OPUC terminal identity.
21. Burnol co-Poisson scalar Berezin sign or parity-block flatness.
22. Source determinant-line no-first-crossing theorem retaining negative index.
23. All-prime Calkin collinearity or two-particle Sonin subroot estimate.
24. Affine-dimension-three and arbitrary-rank Gaussian curvature classification.
25. Viable vector/operator-valued or nonclosable post-scalar rigging.
26. Actual two-variable HT/SR realization with rank-one period group.
27. A theorem converting Dirichlet/Gamma differential nonrelation into zero-location
    information.
28. Lindelöf second-spacing estimate plus across-class cancellation, followed by an exact
    typed RH handoff.

### Disproof leap

29. A rigorously certified off-line zero or any equivalent negative finite certificate.

## 9. Literature reconciliation

Current primary literature distinguishes new finite or structural advances from proof
completion.

- Connes and van Suijlekom prove real zeros for the Fourier transform of an isolated
  simple even ground state of a lower-bounded convolution operator. This validates a
  spectral mechanism but does not identify a convergent Xi ground state:
  [Quadratic Forms, Real Zeros and Echoes of the Spectral Action](https://arxiv.org/abs/2511.23257).
- Connes's survey obtains real finite approximants and explicitly leaves finite-to-infinite
  Euler-product convergence as the prospective proof step:
  [The Riemann Hypothesis: Past, Present and a Letter Through Time](https://arxiv.org/abs/2602.04022).
- Connes–Consani–Moscovici report striking finite spectral convergence; they state that a
  rigorous proof of convergence would establish RH:
  [Zeta Spectral Triples](https://arxiv.org/abs/2511.22755).
- Hedenmalm constructs the theta boundary-value eigenproblem and a formal self-adjoint
  pair. The source-positive Hilbert realization remains open:
  [Spectral interpretation of Riemann zeta zeros](https://arxiv.org/abs/2606.17494).
- Suzuki constructs finite self-adjoint extensions and conjectures the limiting
  self-adjoint operator. The infinite/full-frequency identification remains open:
  [Weil's quadratic form via the screw function](https://arxiv.org/abs/2606.09096).
- The finite Guinand–Weil dictionary gives exact finite zero sums and an explicit
  archimedean tail budget, while expressly making no RH claim:
  [A finite Guinand-Weil dictionary and archimedean tail order](https://arxiv.org/abs/2607.02828).
- Liflandsky's discrete Möbius Laplace bound implies RH, while the converse needs extra
  zero hypotheses. The critical bound remains an input:
  [Explicit formula for the discrete Laplace transform of the Möbius function](https://arxiv.org/abs/2607.09797).
- The theta-infinity paper proves zero-free consequences conditional on arbitrary-length
  mollified moment bounds; it does not prove those bounds:
  [The θ=∞ Conjecture and RH for Automorphic L-functions](https://arxiv.org/abs/2605.24363).
- The 2026 Hardy-space and Colombeau papers give closure/generalized-function criteria,
  not the missing source estimates:
  [Hardy space approximation](https://arxiv.org/abs/2606.16097) and
  [Colombeau–Beurling criterion](https://arxiv.org/abs/2606.22562).
- The Salem note is explicitly an equivalence:
  [A new equivalence by means of the Salem integral equation](https://arxiv.org/abs/2604.15396).
- Polson's revised Thorin paper establishes the probabilistic/Hadamard framework, not a
  source-constructed critical-seam carrier:
  [Riemann, Thorin, van Dantzig Pairs, Wald Couples and Hadamard Factorisation](https://arxiv.org/abs/1804.10043).

The cited primary sources close no Tier-1 or Tier-2 open core above.

## 10. Priority and research policy

### Highest expected leverage

1. first-clock lower floor / Bohr asymptote;
2. Julia global coherent-energy budget;
3. Hedenmalm completed high-frequency current;
4. Möbius Gamma–Hankel bounded returns;
5. fixed-width rectangular Weil floor;
6. any finite prime–arch high-frequency ceiling;
7. Sonin quantitative frequency-channel closure;
8. Suzuki source-selected full jump kernel or relative-Volterra source-germ weld.

These routes begin with literal source and have short, formally closed tails to RH.

### Valuable but longer-horizon construction programs

- Deninger/Hodge;
- quadratic spectral realization;
- Gamma–Jacobi reader;
- Connes/prolate convergence;
- compact Thorin/Markov carrier.

### Do not spend cycles on

- new names for RH-equivalent divisor coordinates;
- finite local selectors;
- shellwise or finite-prefix positivity as completed positivity;
- abstract zero-fed spectral models;
- generic HT, positivity, log-concavity, or moment arguments without literal source;
- legacy Suzuki entire-limit, Sonin scalar/position-side completion, or moving-polynomial
  even factorization;
- lexical HT/RH crossmatches without exact imports and identifier use.

## 11. Final frontier statement

The corpus has already solved most connector problems. Its remaining difficulty is not a
shortage of RH criteria. It is source acquisition.

Every leading route has the same abstract shape:

```text
literal prime/theta/Möbius/clock source
→ one global sign, recurrence, rate, or operator-realization theorem  [OPEN]
→ a fully formal zero-exclusion connector                              [PROVED]
→ RiemannHypothesis.                                                   [NOT PROVED]
```

The routes differ in the missing theorem:

- lower floor or Bohr asymptote for the first clock;
- fixed-width lower floor for rectangular Weil;
- all-order completed positivity for Hedenmalm/prime–arch;
- critical cancellation for Möbius;
- rate-controlled closure for Sonin;
- source-selected full-frequency Pick/Hermite–Biehler structure for Suzuki;
- relative-Volterra phase source-germ weld;
- off-diagonal core-current control for Xi Taylor;
- coherent global energy budget for Julia;
- source-built operator and spectrum inclusion for spectral/Deninger programs.

The disproof side is equally exact: one certified off-line zero or equivalent negative
finite witness would suffice, but the corpus produces none.

Therefore the honest current conclusion is:

> **RH is neither proved nor disproved. The formal frontier is a finite quotient of
> source-level open cores, led by first-clock, completed positivity, critical Möbius,
> Sonin/Suzuki, Xi-current, and Julia coherent-energy problems. All other
> RH-facing declarations are connectors, mirrors, infrastructure, or retired
> mechanisms unless and until they supply a new literal-source theorem.**

## Appendix A. Principal Lean anchors

- `RHTower/RiemannTower.lean`
- `RHTower/RHCharacterizations.lean`
- `RHTower/CCMFirstClockTailLowerBoundCompleteness.lean`
- `RHTower/CCMFirstClockAsymptoticBohrLaw.lean`
- `RHTower/CCMSingleClockCompleteSourceDivisorTomography.lean`
- `RHTower/CCMRectangularWeilCompleteness.lean`
- `RHTower/XiWeilPositivityCriterion.lean`
- `RHTower/HedenmalmCenterMixedOrientationBoundary.lean`
- `RHTower/PrimeArchThetaHankelDegreeTail.lean`
- `RHTower/PrimeArchHankelDeterminantCriterion.lean`
- `RHTower/MobiusLaplaceMellinPlancherelBridge.lean`
- `RHTower/MobiusLaplaceGammaHankelWall.lean`
- `RHTower/SoninCoupledPrimeArchGramTransfer.lean`
- `RHTower/SoninDilatedBandTransport.lean`
- `RHTower/SoninShellCutBandPacketTerms.lean`
- `RHTower/SoninShellCutBandBound.lean`
- `RHTower/SuzukiFiniteApertureHermiteBiehler.lean`
- `RHTower/SuzukiVolterraCartesianPhaseDefect.lean`
- `RHTower/StrictHermiteBiehlerGivesRH.lean`
- `RHTower/XiCTaylorThetaTailCoreCurrentCapstone.lean`
- `RHTower/CCMSharpPrimeWindowSubpowerGate.lean`
- `RHTower/QuadraticScaleSpectralRH.lean`
- `RHTower/DeningerHilbertKummer.lean`
- `RHTower/HedenmalmPrimeNormalWickBoundaryEnergy.lean`
- `RHTower/ThetaCuspCalibratedPowerReciprocalMomentLaw.lean`
- `RHTower/CCMFirstClockJuliaEquilibriumGram.lean`
- `RHTower/PrimeArchVerifiedHeightAccretivity.lean`
- `RHTower/XiPrimeSeamPairAsymptotics.lean`
- `RHTower/RiemannHypothesisSOTA2026.lean`
- `HTGeometry/SummableSpectrumScrewAlmostPeriodic.lean`
- `HTGeometry/SummableSpectrumScrewBohrCoefficients.lean`
- `HTGeometry/SummableSpectrumScrewRecurrence.lean`
- `HTGeometry/CarriedConclusion.lean`
- `HTGeometry/JuliaDefectEquilibriumPositiveDefinite.lean`
- `HTGeometry/AnalyticEulerTailExactFaithfulnessUniversalityLaw.lean`
- `HTGeometry/PrimeOrientationCompletedRingSignNoGo.lean`
- `HTGeometry/QuadraticContactPickObstruction.lean`
- `HTGeometry/FiniteReporterBlindness.lean`
- `HTGeometry/OrbitQuotientLiftNoGo.lean`
- `HilbertMetric/PrescribedEvaluationReconstruction.lean`
- `HilbertMetric/GaussianMetricStableRankFractureLaw.lean`
- `HilbertMetric/CCRFiniteBlockObstruction.lean`
- `HilbertMetric/ThreePointCorrelationAngle.lean`
- `HilbertMetric/DenseClosedScalarRigidity.lean`
