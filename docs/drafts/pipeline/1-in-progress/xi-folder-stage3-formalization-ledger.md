# Xi folder stage-3 formalization ledger

Target: every card in `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/xi/`
formalized unconditionally in Lean and promoted to `3-formalized`.

## Status

| # | Card | State | Lean modules |
|---|---|---|---|
| 1 | xi-determinant-logarithmic-singular-value-law | open | |
| 2 | xi-gamma-shape-completely-monotone-rh | Lean done (scalar and kernel equivalence, overclaim exclusion) | HTGeometry/CompletelyMonotoneTower, HTGeometry/AtomicHausdorffSource, HTGeometry/GeneralDirichletCompletelyMonotone, RHTower/XiGammaShapeCompleteMonotonicity, RHTower/XiGammaShapeCompletelyMonotoneExtension |
| 3 | xi-global-meixner-shape-landau-rh | Lean done | HTGeometry/GeneralDirichletLandau, RHTower/XiGlobalMeixnerShapeLandau |
| 4 | xi-hedenmalm-local-algebra-rank-census | Lean done | HTGeometry/PolynomialQuotientMultiplicationRank, HTGeometry/GcdDerivativeDistinctRoots, HTGeometry/HermiteBiehlerPairRankCensus, HTGeometry/FiniteMomentDivisorReconstruction, RHTower/XiHedenmalmLocalAlgebraRankCensus |
| 5 | xi-orientation-euler-safe-paired-cauchy-completeness | Lean done (targets 1-5: closure (9), kernel (14)-(15), splice (21)-(22), countable criterion (19), chain (26)) | RHTower/XiCauchyTransformCompleteness, RHTower/XiEulerSafePairedCompleteness, RHTower/XiEulerSafePairedClosure, RHTower/XiEulerSafePairedValueKernel, RHTower/XiEulerSafePairedRationalCriterion |
| 6 | xi-outer-euler-modulus-first-prime-seam-antialignment | Lean done | RHTower/XiOuterEulerModulusPrimeSeamAntialignment |
| 7 | xi-positive-paired-real-loewner-seam-log-weld | Lean done (targets 1-5) | RHTower/XiPositivePairedRealLoewnerSeam |
| 8 | xi-prime-seam-one-ended-cofinal-edge-collapse | Lean done (including the sparse-edge Calkin chain (7)-(9)) | HTGeometry/ArbitraryLabelEndReconstruction, RHTower/XiPrimeSeamOneEndedCollapse, RHTower/XiPrimeSeamSparseEdgeCalkin |
| 9 | xi-radial-jensen-schur-capacity-rigidity | Lean done | HTGeometry/SchwarzPickEstimate, RHTower/XiRadialJensenSchurCapacity |
| 10 | xi-reciprocal-translation-prime-seam-norm-law | Lean done | RHTower/XiReciprocalTranslationSeamNormLaw |
| 11 | xi-shift-loewner-prime-generator-law | open | |
| 12 | xi-square-descent-vertical-modulus-rh | Lean done (both directions + R* corollary) | RHTower/XiSquareDescentVerticalModulus, RHTower/XiSquareDescentVerticalModulusConverse |
| 13 | xi-supercharge-persistent-harnack-defect | open | |
| 14 | xi-unit-euler-pole-affine-section-translated-bezoutian | partial: unit-residue affine section (1)-(2), Bezoutian diagonal formula, and the necessity half of the classifier (6) done; sufficiency needs Hadamard genus zero | HTGeometry/HorizontalModulusDerivative, RHTower/XiUnitEulerPoleAffineSection |
| 15 | xi-theta-square-rate-hardy-reader | Lean done, PROMOTED | HTGeometry/CauchyMatrixDeterminant, CauchyDeterminantStep, HalfLineExponentialGram, HalfLineExponentialDistance, HalfLineExponentialCoDistance, PuncturedSineProduct, HalfLineExponentialReader, HalfLineExponentialResidualLimit, RHTower/XiThetaSquareRateBlaschkeLimit, XiThetaSquareRateReaderNorm, XiThetaSquareRateReaderL2 |

## Precise plan for each remaining item

1. **Card 2 converse** — DONE.  The route was Hausdorff, not Bernstein: sampling the completely
   monotone extension on `θ₀ + n` gives a Hausdorff completely monotone sequence, hence a finite
   source `μ` on `[0,1]`; the tilt `y^N dμ` has exactly the moments of the atomic measure
   `Σ_p B_p x_p^N δ_{x_p}` with `x_p = exp(-λ_p)`, `B_p = A_p exp(-θ₀ λ_p)`; uniqueness of the
   Hausdorff source identifies the two, the atom of `x_p` is `B_p`, and finiteness of `μ` bounds
   `Σ_p B_p`.  Combined with card 3's off-line divergence this gives the equivalence in both scalar
   and kernel form.
2. **Card 5 packaging** — done except the final build of the countable criterion.  (i) the paired
   kernel `K_pair` and identity `(15)` were obtained from
   `xiWeilPolarization_cauchy_eq_relativeResolvent_dividedDifference` after collapsing the four
   Schwarz blocks with the oddness and Schwarz symmetry of the relative trace; (ii) the closure
   statement used the closed real Schwarz-fixed fibre-constant sector and the orthogonal projection
   onto the closed real span; (iii) the Gaussian-rational reduction was done on the *Cauchy
   transform* side — continuity plus density of Gaussian rationals in a divisor-free ball — rather
   than by norm continuity of `w ↦ P_w`.
3. **Card 14 sufficiency**.  Needs the genus-one Hadamard package for `X_c = xi(1/2+·) - c`
   (an even, real, order-one entire function): reuse `OrderOneFixedDivisorRigidity` and the moving
   even canonical-product machinery in `HTGeometry/MovingEvenCanonicalSurgery.lean` rather than the
   `QuadraticSubtypeZero` class, whose growth hypothesis is far too strong here.
4. **Card 11**.  The Loewner generator identity, the finite-matrix positive integration law, the
   Euler--Gamma split and its local uniform convergence are elementary.  The critical-generator
   equivalence and the positive-shift obstruction need Nevanlinna--Pick extension for
   Caratheodory functions on a half plane; the corpus already owns Hardy's theorem, the
   Sondow--Dumitrescu monotonicity, and `Bottcher/DiskSchwarzPick.lean`.
5. **Card 13**.  Real hyperelliptic topology.  The formalizable core is the arc-count theorem: for
   a real polynomial of odd degree `2n+1` with `2r+1` simple real roots, the positivity set has
   exactly `r+1` components on the real projective line, giving `HarnackDefect = n - r`.
6. **Card 15** — DONE and promoted.  Paley--Wiener surjectivity was never needed: the reader is the
   normalised orthogonal residual of one heat exponential against the closed span of the others.
   Its norm came from a new chain — Cauchy determinant (mathlib gap) → consecutive determinant step
   → exponential Gram is a Cauchy matrix → Blaschke co-distance law → punctured Euler sine product
   (mathlib gap) + the corpus's `tendsto_euler_sinh_prod` → Blaschke limit → residual = limit of
   finite co-distances.
7. **Card 1**.  Riemann--von Mangoldt in counting form, plus compact-operator singular values,
   Schatten ideals and `det_2`.  The corpus already owns approximation numbers, `MemSchattenClass`,
   and `SchattenCriticalAsymptotic`.

## Remaining infrastructure to build

| Card | Missing classical input |
|---|---|
| 1 | Riemann–von Mangoldt asymptotic in operator form; compact-operator singular values, Schatten ideals, `det_2` |
| 2 | Bernstein/Hausdorff consumer: CM function on `(0,∞)` ⇒ Hausdorff source ⇒ summability at every positive shape |
| 5 | paired absolute-Euler value kernel and its Weil quadratic identity (the completeness core is now built) |
| 11 | Nevanlinna–Pick extension for Caratheodory functions on a half plane |
| 13 | real hyperelliptic topology: genus, real components, Harnack bound |
| 14 | Hadamard factorization for even entire functions of order `< 1` (genus zero), for the sufficiency half only |
| 15 | right half-plane Hardy space `H^2` and the Laplace Paley–Wiener unitary |

## Reusable corpus assets found

- `HTGeometry/CoherenceEndReconstruction.lean` — finite-boundary one-ended reconstruction.
- `RHTower/XiPrimeSeamCoherenceCollapse.lean` — canonical prime seam, cofinal decay.
- `RHTower/HeatAperturePrimeSeamReflection.lean` — single prime seam pins the critical line.
- `HTGeometry/QuotientIdealDimension.lean` — finite local algebra dimension and ideal codimension.
- `HTGeometry/PowerSumTorelli.lean`, `MultisetNewtonSolve.lean` — Newton inversion.
- `RHTower/SlabGermResidueTransport.lean` — contour power moments = multiplicity divisor moments.
- `RHTower/XiGuinandWeilRectanglePeeling.lean` — weighted rectangle argument principle for `XiC`.
- `RHTower/SchattenCriticalAsymptotic.lean`, `SoninEulerFiniteL2Lower.lean` — Schatten/Calkin layer.
- `HTGeometry/HausdorffMomentTheorem.lean` — Hausdorff moment theorem with uniqueness.
- `HTGeometry/GeneralDirichletLandau.lean` (NEW) — Landau for general Dirichlet series, Taylor
  expansion at a safe centre, complete monotonicity, radial Hankel positivity.
- `HTGeometry/SchwarzPickEstimate.lean` (NEW) — sharp Schwarz–Pick displacement, narrow-sector
  Schur lemma.
- `HTGeometry/HorizontalModulusDerivative.lean` (NEW) — horizontal modulus derivative and its
  monotonicity criterion, valid across the divisor.
- `HTGeometry/CompletelyMonotoneTower.lean` (NEW) — a completely monotone function on `(0,∞)` has
  alternating forward differences of every order, so its arithmetic samples are Hausdorff
  completely monotone.  This is step (i) of the card-2 converse.
- `RHTower/XiCauchyTransformCompleteness.lean` (NEW) — the Cauchy transform of a square-summable
  divisor vector is holomorphic off the divisor, decays vertically, and is killed by a vanishing
  real part on any ball.
