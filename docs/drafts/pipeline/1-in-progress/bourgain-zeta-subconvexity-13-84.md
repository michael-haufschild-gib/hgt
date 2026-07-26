# Bourgain critical-line subconvexity exponent 13/84

- **ID:** `bourgain-zeta-subconvexity-13-84`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / THEOREM (Lean target)
- **Source:** J. Bourgain, *Decoupling, exponential sums and the Riemann zeta
  function*, JAMS 30 (2017), 205--224, DOI 10.1090/jams/860.
- **Statement:** `[LITERATURE]` For every `ε > 0` there are `C > 0` and `T ≥ 1`
  such that, for every real `t` with `T ≤ |t|`,
  `‖riemannZeta (1/2 + t*I)‖ ≤ C |t|^(13/84+ε)`.

## Goal

Produce a dependency-closed, unconditional Lean theorem matching Bourgain's
critical-line bound. No spacing, decoupling, exponential-sum, or approximate
functional-equation estimate may enter as a hypothesis of the final declaration.

## Gates

- [x] 0 → 1 in-progress: exact asymptotic statement, primary source, dependency
  graph, and current Lean wall identified.
- [ ] 1 → 2 fully-proven: transcribe and audit a dependency-closed paper proof,
  including every theorem imported by Bourgain from earlier literature.
- [ ] 2 → 3 formalized: exact Lean theorem, targeted build, lint, and
  `#print axioms` pass.
- [ ] 3 → 4 publication-ready: source crosswalk and Lean certificate.

## Exact dependency ledger

1. `[LITERATURE]` Bourgain Theorem 1: multilinear decoupling for a
   non-degenerate curve in `R^4`. The proof imports planar curve decoupling and
   multilinear Fourier-restriction estimates.
2. `[LITERATURE]` Bourgain Theorem 2 and Corollary 3: the twelfth-power mean
   value `A₆ ≪ N^(6+ε)`, then the first-spacing estimate.
3. `[LITERATURE]` Section 3: Poisson/cubic localization, six-fold convolution,
   Bombieri--Iwaniec double large sieve, and Huxley's resonance-curve
   second-spacing estimate produce Theorem 4.
4. `[LITERATURE]` Section 4: Theorem 4 plus older exponent-pair bounds gives the
   uniform short exponential-sum estimate (3.19).
5. `[LITERATURE]` Classical approximate functional equation, partial summation,
   and dyadic dissection turn (3.19) into exponent `13/84`.

## Internal corpus audit

- `[CORPUS]` `ZetaVerticalSqrtBound.norm_riemannZeta_le_sqrt_norm_add_two_half`
  gives only square-root-scale growth.
- `[CORPUS]` first- and second-derivative van der Corput integral estimates are
  formalized in `VanDerCorput*.lean`.
- `[CORPUS]` `ZetaAFETransfer.zeta_norm_le_afe` is an unconditional
  Euler--Maclaurin transfer, not the symmetric height-dependent AFE.
- `[CORPUS]` `FourthMomentDiagonal.fourthMoment_bounded` retains its explicit
  off-diagonal double sum.
- `[LOCAL-RESEARCH] [PAPER-PROVED]`
  `hardy-critical-line-moment-anchor.md` contains a dependency-closed smooth
  symmetric AFE proof. This is also the first reusable Bourgain dependency and
  therefore enters Lean first.
- `[OPEN CORE]` After the smooth AFE, no analytic `L^p` decoupling,
  Bombieri--Iwaniec double large sieve, or Huxley second-spacing theorem exists
  in the corpus or current mathlib.

## Formalization order

1. Smooth symmetric AFE at conductor scale.
2. Partial-summation and dyadic reduction from uniform short logarithmic
   exponential sums to a critical-line zeta exponent.
3. Exponent-pair bounds used outside Bourgain's new estimate.
4. Double large sieve and Huxley second-spacing theorem.
5. Bourgain `A₆` mean value via curve decoupling.
6. Assemble the unconditional `13/84+ε` theorem and audit axioms.

## Log

- 2026-07-25 — primary paper and current Lean corpus audited. Route opened in
  Stage 1. Smooth symmetric AFE selected as first dependency because its complete
  paper proof already exists in the Stage-2 Hardy card and it is independently
  required by Bourgain Section 4.
- 2026-07-25 — `[BRIDGE] [LEAN-PROVED]` partial summation and dyadic reduction
  closed in `BourgainPartialSummation.lean`, `BourgainDyadicDissection.lean`,
  and `BourgainZetaReduction.lean`. The exact critical-line Dirichlet polynomial
  is now connected to blockwise logarithmic phase sums and to the unconditional
  Euler--Maclaurin zeta transfer. Target builds, representative axiom audits,
  umbrella wiring, and formal lint pass. Smooth conductor-length AFE remains
  the first open analytic dependency.
- 2026-07-25 — `[BRIDGE] [LEAN-PROVED]` Gaussian smooth-AFE contour
  infrastructure closed in six `SmoothAFEGaussian*.lean` modules: explicit
  vertical Gaussian majorants on every nonzero line, positive-abscissa
  invariance, entire divided-difference regularization, reciprocal contour
  limits, and exact unit residue across zero. Representative axiom audits use
  only `[propext, Classical.choice, Quot.sound]`. The remaining Stage-2 AFE
  core is now the zeta Dirichlet-series interchange, functional-equation
  reflection, and uniform Gamma-ratio/Stirling estimate; no Bourgain
  decoupling or spacing estimate has yet been discharged.
- 2026-07-25 — `[BRIDGE] [LEAN-PROVED]`
  `SmoothAFEZetaMellin.lean` closes the absolute-half-plane zeta expansion:
  explicit `p`-series/Gaussian bounds prove vertical integrability of
  `ζ(s+w)x^w exp(w²)/w` for `1 < Re(s)+c`, termwise integrability of the
  Dirichlet series, summability of integral norms, and the justified
  integral/`tsum` interchange. Remaining smooth-AFE core is coefficient
  identification with the canonical cutoff, contour shift of `ζ(s+w)`,
  functional-equation reflection, and uniform Gamma-ratio control.
- 2026-07-25 — `[BRIDGE] [LEAN-PROVED]`
  `SmoothAFEZetaDirichletExpansion.lean` identifies every termwise Mellin
  integral with the canonical Gaussian cutoff and proves the exact identity
  `A_c(s,x)=∑_{n≥1}n^{-s}V(n/x)` whenever `c>0` and
  `1<Re(s)+c`. The open smooth-AFE core is now the residue-bearing zeta
  contour shift, functional-equation reflection, and uniform Gamma-ratio
  estimate.
- 2026-07-25 — `[CORPUS] [LEAN-PROVED]`
  `BourgainLogExponentPair.hasLogExponentPair_zero_one` supplies the exact
  uniform-subinterval interface for the trivial pair `(0,1)`, using
  unimodularity and the triangle inequality. `[LITERATURE]` Bourgain's JAMS
  paper proves the `13/84` zeta exponent through its `A₆` first-spacing
  theorem, Bombieri--Iwaniec/Huxley second spacing, and older exponent-pair
  bounds; it does not make the current deep gap disappear by a direct
  elementary specialization. `[OPEN CORE]` The exact declaration
  `HasLogExponentPair (13/84) (55/84)` still requires formalizing that
  decoupling/spacing chain. No stronger corpus theorem currently supplies it.
- 2026-07-25 — `[BRIDGE] [LEAN-PROVED]` the smooth symmetric AFE contour
  chain now includes exact zeta contour shifts, both pole residues,
  functional-equation reflection, dual Dirichlet expansion, right-half-plane
  `χ` bounds, contour limits, and cutoff localization in the
  `SmoothAFEZeta*.lean` and `SmoothAFECutoffBounds.lean` modules. These target
  builds are unconditional; the final conductor-uniform Gamma-ratio
  localization and assembly into the zeta theorem remain open.
- 2026-07-25 — `[ARITHMETIC CORE] [LEAN-PROVED]` parabola triple fibers were
  reduced to representations by `u²+3v²`. A Euclidean-domain construction for
  the Eisenstein integers, finite-unit classification, injection into scalar
  divisors, and a direct `Oε(N(z)^ε)` Eisenstein divisor bound now prove
  `card_bourgainParabolaTripleMoment_fiber_subpower`. No divisor estimate is
  assumed.
- 2026-07-25 — `[DECOUPLING INPUT] [LEAN-PROVED]`
  `BourgainFiniteFourierParseval.lean`,
  `BourgainParabolaTorusL6.lean`, and
  `BourgainParabolaTwoTorusL6.lean` turn the fiber theorem into exact
  one- and two-torus polynomial Parseval identities and the literal weighted
  discrete-parabola estimate
  `∫_{T²}|Σaₙe(nu+n²v)|⁶ ≪ε H^ε(Σ|aₙ|²)³`.
  `BourgainParabolaTwoTorusL12.lean` also records the unconditional
  `H^(9+ε)` unit-coefficient twelfth-moment baseline.
  `[OPEN CORE]` Bourgain Theorem 1/Section 2 must supply the non-periodic
  localization, wave-packet/multiplier control, bilinear-to-linear induction,
  and resulting three-power improvement from `H^(9+ε)` to `H^(6+ε)`.
- 2026-07-25 — `[SECTION 2 INTERFACES] [LEAN-PROVED]`
  `BourgainUnitIntervalTorus.lean` identifies normalized circle averages with
  literal `[0,1]` Fourier integrals.
  `BourgainA6TorusBaseline.lean` formalizes Bourgain's exact
  `n,n²,N^(1/2)n^(3/2),N^(1/2)n^(1/2)` phase, proves equality between its
  four nested integrals and the internal torus model, and establishes the
  unconditional `N^(9+ε)` baseline.
  `BourgainPlanarBilinearL6.lean` proves exact four-torus Fubini
  factorization for the two independent parabola factors in (2.7) and its
  sharp subpower `L⁶×L⁶` estimate.  Together with the compiled separated
  pointwise/integrated decomposition and contracting recurrence, this closes
  the algebraic skeleton of (2.7), (2.25), and (2.27).
  `[OPEN CORE]` The genuine three-power gain still requires Theorem 1's
  non-periodic wave-packet localization, the Taylor remainder multiplier in
  (1.21)--(1.25), and the two successive scale changes leading to (2.10).
- 2026-07-25 — `[SMOOTH AFE] [LEAN-PROVED]`
  `SmoothAFEZetaChiPowerBound.lean` derives an explicit fixed-strip
  `|χ(1/2+δ+it)| ≪δ max(1,|t|)^(-δ)` estimate from the corpus's quantitative
  digamma bounds. `SmoothAFEZetaDualWeightConductor.lean` inserts that estimate
  into the exact negative Mellin contour and proves the conductor-uniform
  localization
  `‖Wτ(Y)-1‖ ≤ Cδ Y^δ / max(1,|τ|)^δ`.
  No Stirling estimate or approximate functional equation is assumed.
- 2026-07-25 — `[SECTION 2 GEOMETRY] [LEAN-PROVED]`
  `BourgainPolynomialCurveNondegenerate.lean` proves Bourgain's exact monomial
  Wronskian condition (1.1): the determinant for `(t,t²,t³,t⁴)` is `288`,
  uniformly when the four derivative columns are evaluated at independent
  points. It also proves the separated determinant in (2.11) equals `144` for
  `(t³,t⁴)` and remains at least `90` in absolute value throughout an explicit
  unit `C⁴`-jet neighborhood. `[OPEN CORE]` The normalized square-root Taylor
  remainders from (2.18)--(2.19) must now be proved to lie in this neighborhood;
  the decoupling theorem and multiplier/localization argument remain open.
- 2026-07-25 — `[SECTION 2 TAYLOR CONNECTOR] [LEAN-PROVED]`
  `BourgainTaylorRemainders.lean` replaces the paper's asymptotic notation
  `φ₃(t)∼t³`, `φ₄(t)∼t⁴` by exact normalized definitions. It proves the two
  fractional-power Taylor identities corresponding to (2.18)--(2.19),
  computes all third/fourth jets, and obtains the closed determinant
  `144(1+qs)^(-5/2)(1+qt)^(-7/2)(1+(5/2)qs-(3/2)qt)`.
  Consequently the actual normalized phases satisfy (2.11) pointwise for
  `0<q≤1/2`, `s,t∈[0,1]`. `[OPEN CORE]` Remaining Section-2 gap is now the
  quantitative curve-decoupling/localization theorem itself, not the Taylor
  nondegeneracy assertion.
- 2026-07-25 — `[SECTION 1/2 FULL WRONSKIAN] [LEAN-PROVED]`
  `BourgainTaylorScaling.lean` proves the literal physical-scale formulas
  (2.18)--(2.19), including every coefficient and power of `M/N₀`.
  `BourgainTaylorWronskian.lean` factors the full independent-point Wronskian
  for `(t,t²,φ₃,φ₄)` through the separated higher-jet determinant and proves
  the uniform lower bound `9/16` required by (1.1).  The corresponding
  separated determinant is uniformly at least `9/32`.
- 2026-07-25 — `[SECTION 1 LOCALIZATION] [LEAN-PROVED]`
  `BourgainQuadraticTaylorControl.lean` proves the Banach-valued quadratic
  Taylor remainder from a uniform third-derivative bound, propagates it
  through an arbitrary bounded frequency functional, and specializes the
  interval length `K^(-1/2)` to the exact phase-error scale `N K^(-3/2)` in
  (1.21)--(1.22). `[OPEN CORE]` The weighted Fourier multiplier estimate that
  absorbs this bounded phase perturbation, the lower-dimensional decoupling
  input (1.5), and Bourgain's scale induction remain to be formalized.
- 2026-07-25 — `[SECTION 1 MULTIPLIER/GEOMETRY] [LEAN-PROVED]`
  `BourgainPhasePerturbation.lean` replaces “the multiplier may be ignored”
  by explicit one-Lipschitz phase bounds for weighted finite sums and
  extension integrals, and composes them with the Taylor theorem at error
  `N C K^(-3/2)/2`.
  `BourgainSquareRootOsculatingGeometry.lean` identifies the literal
  first/second derivative matrix for
  `(t,t²,t^(3/2),t^(1/2))`, proves its determinant is exactly
  `3(b-a)^4/(8a³b³)` at parameters `a²,b²`, constructs the resulting linear
  and continuous-linear equivalences, and proves the exact Lebesgue Jacobian
  formula. Thus the nondegenerate change of variables in (1.23)--(1.24) is
  unconditional for the curve used in the application.
- 2026-07-25 — `[SECTION 1 BOOTSTRAP] [LEAN-PROVED]`
  `BourgainPowerScaleBootstrap.lean` formalizes the actual multiplicative
  power-scale recurrence `b(N)≲N^δb(N^(2/3))`, proves its exact finite
  iteration, and bounds the accumulated geometric exponent by `3δ`.
  `[OPEN CORE]` Continuous weighted planar `L⁶` decoupling (1.5), weighted
  cube localization, and the analytic inequality producing the recurrence
  remain missing; `BourgainScaleContraction.lean` concerns a different
  additive dyadic recurrence and cannot discharge this step.
- 2026-07-25 — `[SECTION 1 PLANAR INPUT] [LEAN-PROVED]`
  `BourgainPlanarDiscreteDecoupling.lean` states the exact finite extension
  `Σaₙe(nu+n²v)` and proves its weighted unit-square sixth-moment estimate
  from the arithmetic torus theorem.
  `BourgainScaledParabolaDecoupling.lean` then performs the literal physical
  change of variables `u=x/H`, `v=y/H²`: the `[0,H²]²` Jacobian is `H³`,
  the linear coordinate contributes exactly `H` periods, and the normalized
  physical moment equals the unit-torus moment with no extra power loss.
  It also proves periods `H,H²` and exact invariance under arbitrary
  translations of the physical square.
  `BourgainScaledPlanarBilinearL6.lean` proves exact Fubini factorization on
  `[0,H²]⁴`, identifies the normalized physical two-factor moment with the
  independent four-torus moment, and transfers the subpower estimate.
  All target builds and formal lint pass; representative `#print axioms`
  checks report only `propext`, `Classical.choice`, and `Quot.sound`.
  `[OPEN CORE]` This closes the finite physical-scale planar input, but not
  the arbitrary-`L¹` continuous weighted wave-packet theorem used verbatim in
  (1.5), nor the image-parallelepiped covering and recurrence production in
  (1.23)--(1.26).
