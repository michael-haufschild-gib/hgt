# Stage-2 → stage-3 formalization ledger — `not_new_scientific_knowledge`

Scope: every card in this folder must have its proven theorems formalized unconditionally in Lean 4
and then move to `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/`.

Folder size at sweep start (2026-08-16): **496** top-level cards, no subfolders.

## Working rules

- No added hypotheses standing for analytic inputs; no axioms; no `sorry`.
- Search the corpus first (`scripts/formal_tools.py research`, `rg`) before writing any new module —
  ~29 700 Lean files already exist.
- Check with `lake env lean <file>`; build only the oleans needed; wire new modules into the area
  umbrella but never build the umbrella.
- Audit axioms in a scratch file (`#print axioms`), expect only
  `propext`, `Classical.choice`, `Quot.sound`.
- One Lean process at a time; clean up stale processes.

## Promoted

| Date | Card | Lean module(s) |
|---|---|---|
| 2026-08-16 | `co6-involution-host-caveat` | `HTGeometry/InvolutionIdempotentHost.lean` |
| 2026-08-16 | `unbounded-one-coordinate-monodromy-obstruction` | `HTGeometry/ScalarMonodromyAlgebraicIndependence.lean` |
| 2026-08-16 | `suzuki-one-prime-fractional-carrier` | `RHTower/SuzukiOnePrimeFractionalCarrier.lean` (pre-existing) |
| 2026-08-16 | `endpoint-sheared-gram-ridge-parity` | `RHTower/EndpointShearedGramRidgeParity.lean` (+ `Z/2Z` sharpness witness) |
| 2026-08-16 | `finite-wick-contracted-interaction-matroid` | `HTGeometry/WickInteractionMatroidLabels.lean` (+ contraction rank law) |
| 2026-08-16 | `one-sided-compression-bound-not-bounded-operator` | `RHTower/OneSidedCompressionUnbounded.lean` |
| 2026-08-16 | `shifted-towers-do-not-fix-t0-tail-class` | `RHTower/ShiftedTowerTailClasses.lean` |
| 2026-08-16 | `shifted-euler-prime-orbit-pf2-failure` | `RHTower/ShiftedEulerPrimeOrbitPF2.lean` |
| 2026-08-16 | `theta-analytic-to-real-defect-kernel-is-offreal-divisor` | `RHTower/ThetaAnalyticRealDefectKernel.lean` |
| 2026-08-16 | `discriminant-cross-positive-interval` | `RHTower/DiscriminantCrossPositiveInterval.lean` |
| 2026-08-16 | `finite-degree-reciprocal-tests-height-limited` | `RHTower/FiniteDegreeReciprocalPerturbation.lean` |
| 2026-08-16 | `reciprocal-seam-t0-infinite-mass-obstruction` | `RHTower/ReciprocalSeamZerothMoment.lean` |
| 2026-08-16 | `real-source-microlocal-quartet-no-go` | `RHTower/RealSourceMicrolocalQuartet.lean` |
| 2026-08-16 | `single-even-frequency-not-stieltjes` | `HTGeometry/EvenFrequencySeamMoments.lean` |
| 2026-08-16 | `half-turn-repaired-frequency-not-markov` | `HTGeometry/EvenFrequencySeamMoments.lean` |
| 2026-08-16 | `positive-even-frequency-cone-not-markov` | `HTGeometry/EvenFrequencySeamMoments.lean` |
| 2026-08-16 | `finite-signed-even-frequency-atoms-not-markov` | `HTGeometry/EvenFrequencySeamMoments.lean` |
| 2026-08-16 | `bounded-half-turn-frequency-packets-fail-hankel` | `HTGeometry/EvenFrequencySeamMoments.lean` |
| 2026-08-16 | `finite-order-local-frequency-operators-not-markov` | `HTGeometry/EvenFrequencySeamMoments.lean` |
| 2026-08-16 | `relative-contraction-compression-exhaustion` | `HTGeometry/ContractionCompressionExhaustion.lean` |
| 2026-08-16 | `monomial-tail-gate-height-linear-no-go` | `RHTower/MonomialTailGateBound.lean` |
| 2026-08-16 | `loewner-contraction-congruence-normalization` | `RHTower/LoewnerCongruenceNormalization.lean` |
| 2026-08-16 | `bbm-pullback-metric-no-point-spectrum` | `RHTower/BBMMetricObstruction.lean` (pre-existing; wired + audited) |
| 2026-08-16 | `positive-jet-horizon-rh-level-blindness` | `RHTower/PositiveJetHorizonLevelBlindness.lean` |
| 2026-08-16 | `route-r-physical-bockstein-homological-nonerasure` | `RHTower/RouteRPhysicalBocksteinHomologicalNonErasure.lean` (pre-existing; verified + audited) |
| 2026-08-16 | `zeta-summation-constraint-graph-dense-collapse` | `RHTower/SummationGraphDenseCollapse.lean` |
| 2026-08-16 | `fixed-rank-hankel-tests-do-not-imply-stieltjes` | `RHTower/FixedRankHankelNonStieltjes.lean` |
| 2026-08-16 | `boundary-weyl-thresholds-have-no-formal-monotonicity` | `RHTower/BoundaryWeylThresholdNonMonotone.lean` |
| 2026-08-16 | `pole-budget-does-not-imply-uvarov-repair` | `RHTower/PoleBudgetUvarovNoGo.lean` |
| 2026-08-16 | `uvarov-repair-requires-boundary-kernel-positivity` | `HTGeometry/BoundaryKernelSchurSplit.lean` |
| 2026-08-16 | `rank-one-scalar-shadow-needs-kernel-exhaustion` | `HTGeometry/BoundaryKernelSchurSplit.lean` |
| 2026-08-16 | `stieltjes-bulk-exterior-christoffel-monotonicity` | `HTGeometry/StieltjesExteriorChristoffelMonotone.lean` |
| 2026-08-16 | `test-space-closure-q0-visible-rh` | `RHTower/ReciprocalAtomTestSpaceClosure.lean` |
| 2026-08-16 | `finite-rank-counterterm-kernel-visibility` | `RHTower/ReciprocalAtomCounterterm.lean` |
| 2026-08-16 | `continuous-counterterm-atom-locality` | `RHTower/ReciprocalAtomCounterterm.lean` |
| 2026-08-16 | `continuous-counterterm-local-domination-threshold` | `RHTower/ReciprocalAtomCounterterm.lean` |
| 2026-08-16 | `non-atomic-finite-rank-counterterms-rh-strength` | `RHTower/ReciprocalAtomCounterterm.lean` |
| 2026-08-16 | `source-aware-q0-alone-reciprocal-positivity` | `RHTower/ReciprocalAtomPolynomialApproximation.lean` |
| 2026-08-16 | `finite-hard-edge-counterterm-q0-rh-strength` | `RHTower/ReciprocalAtomPolynomialApproximation.lean` |
| 2026-08-16 | `support-vanishing-q0-filter-visible-rh` | `RHTower/ReciprocalAtomPolynomialApproximation.lean` |
| 2026-08-16 | `finite-boundary-ideal-q0-rh-equivalence` | `RHTower/ReciprocalAtomPolynomialApproximation.lean` |
| 2026-08-16 | `continuous-preconditioner-q0-visible-rh` | `RHTower/ReciprocalAtomPolynomialApproximation.lean` |
| 2026-08-16 | `uvarov-kernel-pregate-rh-equivalence` | `RHTower/ReciprocalAtomPolynomialApproximation.lean` |
| 2026-08-16 | `finite-prolate-channel-boundary-rh-strength` | `RHTower/ReciprocalAtomPolynomialApproximation.lean` |
| 2026-08-16 | `summable-exterior-boundary-measure-rh-strength` | `RHTower/ReciprocalAtomPolynomialApproximation.lean` |
| 2026-08-16 | `finite-linear-probe-rh-nonselection` | `RHTower/FiniteProbeRHNonselection.lean` |
| 2026-08-16 | `finite-codimension-landscape-rh-nonselection` | `RHTower/FiniteProbeRHNonselection.lean` |
| 2026-08-16 | `finite-seam-jet-rh-nonselection` | `RHTower/FiniteProbeRHNonselection.lean` |
| 2026-08-16 | `finite-type-source-functor-rh-nonselection` | `RHTower/FiniteProbeRHNonselection.lean` |
| 2026-08-16 | `shifted-stieltjes-hankel-strictness-infinite-support` | `HTGeometry/ShiftedHankelStrictPositivity.lean` |
| 2026-08-16 | `all-order-seam-jet-function-complete` | `RHTower/SeamJetFunctionComplete.lean` |
| 2026-08-16 | `seam-log-derivative-weld-identity` | `RHTower/SeamWeldIdentity.lean` |
| 2026-08-16 | `triangular-seam-coordinates-function-complete` | `RHTower/SeamJetFunctionComplete.lean` |
| 2026-08-16 | `xf1-square-tests-outside-weil-class` | `RHTower/SeamSquareTestNotAdmissible.lean` |
| 2026-08-16 | `d2-countable-window-basis` | `RHTower/CountableWindowBasis.lean` |
| 2026-08-16 | `determinant-line-trivialization-zero-divisor-blindness` | `RHTower/DeterminantLineDivisorBlindness.lean` |
| 2026-08-16 | `acyclic-finite-fibers-derived-limit-zero` | `RHTower/AcyclicFiniteFibersDerivedLimit.lean` |
| 2026-08-16 | `translation-invariant-defect-form-orbit-classification` | `RHTower/TranslationInvariantDefectForm.lean` |
| 2026-08-16 | `xi-hurwitz-scalar-comparison-codimension-no-go` | `RHTower/HurwitzScalarComparisonNoGo.lean` |
| 2026-08-16 | `involutive-reflection-quadratic-rigidity` | `HTGeometry/InvolutiveReflectionQuadraticRigidity.lean` (+ `HTGeometry/FiniteOrderHadamard.lean`) |
| 2026-08-16 | `polynomial-drift-rational-outer-factor-rigidity` | `HTGeometry/PolynomialDriftRationalOuterFactorRigidity.lean` (+ `RHTower/FiniteZeroHadamardProduct.lean`, `HTGeometry/PolynomialDriftExpansion.lean`, `HTGeometry/FiniteOrderPolynomialDescent.lean`, `HTGeometry/AlgebraicOverStateFieldOrder.lean`) |
| 2026-08-16 | `ht-infinite-additive-torsor-staircase` | `HTGeometry/DerivativeShadowStaircase.lean` (+ `HTGeometry/OneSidedJetIndependence.lean`) |
| 2026-08-16 | `prime-translation-koszul-off-unitary-contractibility` | `RHTower/PrimeTranslationKoszulOffLine.lean` (+ `HTGeometry/KoszulCartanContraction.lean`, `RHTower/UnitaryResolventOffCircle.lean`) |
| 2026-08-16 | `prime-loop-connectivity-mixed-word-obstruction` | `RHTower/PrimeLoopMixedWordObstruction.lean` |
| 2026-08-16 | `reciprocal-seam-admissible-domain-q1` | `RHTower/ReciprocalSeamAdmissibleDomain.lean` |
| 2026-08-16 | `finite-t0-schur-threshold-divergence` | `RHTower/FiniteT0SchurThresholdDivergence.lean` |
| 2026-08-16 | `hurwitz-quadratic-n2-density-shadow` | `FullyProvenNewTargets.hurwitz_quadratic_n2_density_shadow` (pre-existing; verified + audited) |
| 2026-08-16 | `semilocal-prolate-control-deformation` | `RHTower/SemilocalProlateControlDeformation.lean` |
| 2026-08-16 | `semilocal-prolate-unitary-transport-trilemma` | `RHTower/SemilocalProlateUnitaryTransport.lean` |
| 2026-08-16 | `euler-support-transverse-divisor-rigidity` | `RHTower/RelativeStripDivisorReflection.lean` |
| 2026-08-16 | `euler-divisor-ultrametric-stability` | `RHTower/EulerDivisorUltrametricStability.lean` |
| 2026-08-16 | `stieltjes-log-weld` | `RHTower/StieltjesWeld.lean`, `RHTower/StieltjesLogWeldTierOne.lean` (pre-existing) + new `RHTower/DirichletMonomialIndependence.lean` |
| 2026-08-16 | `projective-horizon-pure-tail-fermionic-fiber` | pre-existing chain (`ProjectiveHorizonPureTailFiber`, `OccupationFactorInjective`, `PureFibreOccupationBijection`, `PureFibreCardinality`, `ShiftInvariantSubspace`, `QuotientIdealDivisor`, `QuotientIdealDimension`, `InvariantSubspaceRootSubset`, `RootSubsetInvariantSubspace`, `InvariantSubspaceIff`) + new `HTGeometry/PureFibreExteriorOccupation.lean` |
| 2026-08-16 | `projective-horizon-irreducible-simple-ramification` | pre-existing chain, verified + audited: `HTGeometry/SquaredJetCoefficientIndependence.lean`, `HTGeometry/DualRectangularSection.lean`, `HTGeometry/SchurCofactorLocus.lean`, `HTGeometry/CriticalSchurPrimeDivisor.lean`, `HTGeometry/CriticalSchurGenericCorank.lean`, `HTGeometry/CriticalSchurUniformizer.lean` |
| 2026-08-16 | `leading-laurent-coefficient-differential-algebraicity` | `HTGeometry/CoefficientwisePowerSeriesDerivation.lean`, `HTGeometry/FormalParameterRelationNormalization.lean`, `HTGeometry/LaurentCoefficientwiseDerivation.lean`, `HTGeometry/LeadingLaurentCoefficientDescent.lean` |

## Already carrying a stage-3 certificate (verify, then move the paper card)

- `square-aperture-von-mangoldt-correlation-energy` — forward implication and exact identity are
  formalized (`RHTower/CCMSharpPrimeWindowSquareCorrelationEnergy.lean`, axiom-clean). **Open gate:**
  the reverse implication `RH ⇒ C_M = O_δ(M^{1+δ})` needs a formal von Koch–Schoenfeld bound
  `|ψ(x) − x| ≪ √x log²x` under RH. Nothing weaker than `ψ(x) − x = O_ε(x^{1/2+ε})` is required.
- `universal-typed-event-network-fixed-carrier-no-go` — `HTGeometry/EventNetworkFixedCarrier.lean`
  covers the algebraic no-go; `HTGeometry/TraceClassQuantumCorner.lean` covers certified corners.
  **Open gate:** the literal Hilbert direct-sum corner must be proved completely positive, normal
  and trace-nonincreasing (i.e. construct a `TraceClassQuantumCorner` instance for
  `⊕^{ℓ²} H_i` with its inclusion isometries). The last card gate (monoidal-locality obstruction)
  is an open research target, not debt.

## Known blocking infrastructure (shared across several cards)

1. **von Koch–Schoenfeld**: `RH → |ψ(x) − x| ≤ √x log(x)²/(8π)` for `x > 73.2`, or any
   `O_ε(x^{1/2+ε})` form. Blocks the reverse half of several RH-equivalence cards.
2. ~~Riemann–von Mangoldt zero counting~~ — **not needed**: the corpus already owns the
   unconditional genus-one convergence `RHTower.xiSpectralPoint_inv_sq_summable` and
   `RHTower.xiDivisorSupport_infinite` (`RHTower/XiCanonicalProduct.lean`,
   `RHTower/XiZerosInfinite.lean`), together with a complete Xi Hadamard factorization in
   `RHTower/XiHadamardFactorization.lean`. Use those wherever a card cites `N(T) = O(T log T)`
   only to get convergence of `Σ_ρ |ρ|^{-k}`, `k ≥ 2`.
3. ~~Hadamard factorization for finite-order entire functions~~ — **built, both halves**:
   `HTGeometry/FiniteOrderHadamard.lean` proves the zero-free half
   `exists_polynomial_exp_of_ne_zero_of_growth` (zero-free entire with
   `‖f z‖ ≤ exp(C(1+‖z‖)^d)` ⇒ `f = exp(polynomial)`) from `exists_entire_log_of_ne_zero`,
   `borel_caratheodory` and `exists_polynomial_of_polyGrowth`, together with the reusable
   `FiniteOrderEnvelope` predicate and its closure API;
   `RHTower/FiniteZeroHadamardProduct.lean` proves the divisor-carrying half
   `exists_polynomial_mul_expPolynomial_of_envelope` (finite order + finitely many zeros ⇒
   `p · exp q`) at every finite order, generalizing the corpus's subquadratic
   `RHTower.exists_finiteDivisorFactor_mul_exp_of_finite_zeroSet`.
4. **von Neumann algebra generation** (`W*(S)` for a set of operators, and
   `W*(D, H_x) = B(ℓ²)`): needed by `additive-heat-diagonal-generates-full-operator-algebra`.
   mathlib has `VonNeumannAlgebra` but no generated-algebra API.
5. **Derived inverse limits** (`R lim` of a diagram of zero objects): needed by
   `acyclic-finite-fibers-derived-limit-zero`.
6. **Complex-dynamics layer** (Böttcher coordinate, equilibrium measure of a Cantor Julia set,
   winding-number integration): needed by the three `bottcher-*` monodromy cards.
7. **Fredholm determinants and Riesz spectral theory for compact operators** (eigenvalue stability
   under norm perturbation; `det_F(I + zB)` as the canonical limit of finite truncations): needed by
   `semilocal-prolate-defect-triangular-determinant-blindness`.  The strict-lowering, local
   nilpotence and finite-truncation-determinant parts are elementary; only the compact/trace-class
   extension clauses need this layer.
8. **Clunie composition growth** (`T(r, f ∘ g)/T(r,g) → ∞` for transcendental entire `f,g`, outside
   an exceptional set): needed by `autonomous-cap-derivative-shadow-law` and
   `asymptotically-exponential-algebraic-cascade-unit-cost`.
9. **Lipshitz diagonal `D`-finiteness** (the diagonal of a `D`-finite series is `D`-finite): needed
   by `G3-corank-dichotomy`.
10. ~~Selberg-class relative-strip rigidity~~ — **built**:
   `RHTower/RelativeStripDivisorReflection.lean` carries the abstract normal-convergence and
   divisor-reflection theorem named by `euler-support-transverse-divisor-rigidity`'s 2→3 gate
   (`differentiableAt_dirichletSeries`, `exp_dirichletSeries_ne_zero`, `mem_band_of_reflection`,
   `max_re_le_of_reflection`, `re_eq_half_of_reflection`, `eq_empty_of_reflection_lt_half`,
   `summable_of_sparse_support`, `summable_of_partialSum_bound`).  **Still open:** the concrete
   Selberg-class instantiation (an actual completed Euler product with its functional equation);
   the consumer `euler-divisor-ultrametric-stability` is now fully formalized and promoted, with
   `(NE)` discharged by `divisorExponent_le_of_reflection`.
11. **Torus shrinking targets** (Haar measure on `𝕋^V`, forest coordinates, Borel–Cantelli):
   needed by `coherence-graph-volume-recurrence-exponent-law`.
12. **Kummer/radical provider for `U0`** (`PhibKummerInputs` / `PhibRadicalData` /
   `PhibSquareRootDeckData` discharged unconditionally): the `u0-phi-independence*` wrappers in
   `FullyProvenNewTargets.lean` are otherwise complete.

## New reusable infrastructure added by this sweep

- `HTGeometry/FiniteOrderHadamard.lean` — the `FiniteOrderEnvelope` growth predicate with full
  closure API (`const`, `add`, `sub`, `neg`, `mul`, `compAffine`, `of_sq`, polynomials,
  exponentials of polynomials) and **Hadamard's zero-free factorization at every finite order**:
  a nowhere-vanishing entire function with envelope `exp(C(1+‖z‖)^d)` equals `exp(p)` for a
  polynomial `p`.  Generalizes the corpus's order-one `exists_linear_of_ne_zero_of_growth`.
- `HTGeometry/InvolutiveReflectionQuadraticRigidity.lean` — the reflection difference-of-squares
  split, its hyperexponential normal form, the resulting order-one ADE, and the
  `sin z - z cos z` witness.
- `RHTower/FiniteZeroHadamardProduct.lean` — the divisor-carrying Hadamard product at every
  finite order: an entire function with a finite-order envelope and finitely many zeros is
  `p · exp q` with `p, q` polynomials (`finiteDivisorPoly`,
  `exists_polynomial_mul_expPolynomial_of_envelope`).
- `HTGeometry/PolynomialDriftExpansion.lean` — the shift expansion `P(y+a) - P(y)` in the base
  point, with the exact top coefficient `n · lead(P) · a` (`driftCoeff`,
  `eval_driftCoeff_expansion`, `eval_driftCoeff_pred`).
- `HTGeometry/FiniteOrderPolynomialDescent.lean` — a nonconstant polynomial dominates its argument
  (`‖w‖ ≤ R + c‖P w‖`), so finite order descends through a polynomial outer factor.
- `HTGeometry/AlgebraicOverStateFieldOrder.lean` — the differential-order bound for elements
  *algebraic over* a state field; the corpus previously required membership in it.
- `HTGeometry/ExpPolynomialRational.lean` — `G · exp T = Q` with `G, Q` nonzero polynomials forces
  the exponent `T` to be constant, by an exact polynomial degree comparison.
- `HTGeometry/OneSidedJetIndependence.lean` — **the one-sided independence criterion**: a sequence
  is algebraically independent exactly when each term is transcendental over the field generated by
  its strict successors (`algebraicIndependent_of_transcendental_tail`), plus descent of
  transcendence along a subalgebra inclusion (`transcendental_of_le_subalgebra`).
- `HTGeometry/DerivativeShadowStaircase.lean` — the jet-tail tower as a staircase: each step is a
  simple primitive extension of transcendence degree at most one, and hypertranscendence is exactly
  the all-ones staircase.
- `HTGeometry/KoszulCartanContraction.lean` — left exterior multiplication between exterior powers,
  the **Cartan identity** `ι_φ(e ∧ ω) + e ∧ ι_φ ω = φ(e)·ω`, the chain homotopy from an invertible
  coordinate, and exactness of the Koszul complex of a linear functional.
- `RHTower/UnitaryResolventOffCircle.lean` — a unitary minus a scalar off the unit circle is
  invertible, with the reverse-triangle lower bound `| |λ|-1 | ‖y‖ ≤ ‖(U-λ)y‖`.
- `RHTower/FiniteT0SchurThresholdDivergence.lean` — the telescoping test
  `t Q_n(t) = 1 - (1-t/R)^n` and the unshifted Hankel tower with a chosen finite part; no finite
  zeroth moment makes the tower PSD at all orders.
- `RHTower/SemilocalProlateControlDeformation.lean` — the second resolvent identity and the
  relative-resolvent corner splitting, in an abstract associative `ℂ`-algebra.
- `RHTower/SemilocalProlateUnitaryTransport.lean` — a scaling/grading unitary must match the first
  Jacobi coefficient of two cyclic pairs; two distinct prolate parameters force the same.
- `RHTower/EulerDivisorUltrametricStability.lean` — the max-triangle law for absolute-convergence
  abscissae (`abscissa_le_max`) and for the outer divisor exponent (`divisorExponent_le_max`), the
  two critical-ball threshold classes, the monotone `max`-preserving exponentiation, and
  ultrametric path rigidity (`constant_of_connected_of_ultrametric`).
- `RHTower/RelativeStripDivisorReflection.lean` — normal convergence and holomorphy of a
  generalized Dirichlet series on its half-plane of absolute convergence, the sparse-support and
  accumulated-variation abscissa bounds, and the divisor reflection band `1 - A ≤ Re ρ ≤ A` with its
  two threshold classes.
- `HTGeometry/CoefficientwisePowerSeriesDerivation.lean` — a derivation of the coefficient ring
  extended coefficientwise to formal power series (`coeffwiseAdd`), its Leibniz rule, the formal
  parameter as a differential constant, and the commutation of constant-term extraction with every
  jet.  This is gate item (a) of `leading-laurent-coefficient-differential-algebraicity`.
- `HTGeometry/FormalParameterRelationNormalization.lean` — removal of the common parameter power
  from a formal-parameter differential relation (`exists_normalized_relation`,
  `eval₂_of_eq_C_X_pow_mul`) and the assembled power-series descent
  (`differentialAlgebraicOver_constantCoeff_of_formalRelation`).  Gate item (b) and the
  power-series half of the assembly.
- `HTGeometry/LaurentCoefficientwiseDerivation.lean` — the coefficientwise derivation on
  `LaurentSeries K = HahnSeries ℤ K`: `laurentCoeffwise`, the Leibniz rule proved by summing both
  product terms over **one** Hahn antidiagonal (`HahnSeries.coeff_mul_left'`/`coeff_mul_right'`
  applied with the original supports, since a coefficientwise derivative has smaller support),
  every monomial `E^m` a differential constant, restriction to the power-series derivation, and the
  jet shift `D^j F = E^{ord F} · D^j (powerSeriesPart F)`.
- `HTGeometry/LeadingLaurentCoefficientDescent.lean` — the degreewise **parameter rescaling** of a
  differential relation (`parameterRescale`, `coeff_parameterRescale`, `parameterRescale_ne_zero`)
  and the identity `ofPowerSeries_eval₂_parameterRescale` showing that substituting `E^m · v i` for
  the variables is, up to one fixed power `E^c`, evaluation of the rescaled relation at `v` — with
  `k(d) = c + m·deg(d)` realizable in `ℕ` for either sign of `m`.  Gives
  `differentialAlgebraicOver_leadingCoeff_of_laurentRelation` and its contrapositive.
- `RHTower/DirichletMonomialIndependence.lean` — the **triviality lemma for Dirichlet polynomials**:
  a finite combination of `n^{-t}` vanishing at every real exponent has all coefficients zero
  (`coeff_eq_zero_of_dirichletSum_eq_zero`), hence the family `n ↦ (s ↦ n^{-s})` over the positive
  integers is linearly independent over `ℂ` (`linearIndependent_dirichletMonomial`).  Smallest-modulus
  rescaling argument; only real exponents are needed.
- `HTGeometry/PureFibreExteriorOccupation.lean` — the exterior occupation dictionary: occupation
  states are the standard index set `Set.powersetCard` of the exterior-power basis, horizon exchange
  is particle–hole complementation (an involution), the pure critical fibre itself indexes a basis of
  `⋀^m K^L`, and the rank of that exterior power is the critical binomial multiplicity.
- `HTGeometry/InvolutionIdempotentHost.lean` — self-inverse elements ↔ idempotents over a
  commutative ring with `2` invertible.
- `HTGeometry/ScalarMonodromyAlgebraicIndependence.lean` — unbounded scalar monodromy forces
  transcendence over a fixed subalgebra.
- `HTGeometry/WickInteractionMatroidLabels.lean` — **`contract_eRk_add_eRk_eq`, the relative-rank
  law for matroid contraction (a mathlib gap)**, plus the labeled algebraic matroid layer.
- `RHTower/OneSidedCompressionUnbounded.lean` — diagonal inner products of a bounded operator are
  bounded by the operator norm; `ℓ²(ℕ)` basis layer.
- `RHTower/ShiftedTowerTailClasses.lean` — exponential-scale summability comparison and three
  separated weight classes.
- `RHTower/ShiftedEulerPrimeOrbitPF2.lean` — shifted local Euler orbit, its generating identity,
  and its negative order-two Toeplitz minor.
- `RHTower/ThetaAnalyticRealDefectKernel.lean` — the analytic/real defect comparison and its exact
  RH equivalence (uses `SlabMassSquareCertificate.riemannHypothesis_iff_xiC_zero_im_eq_zero`).
- `RHTower/DiscriminantCrossPositiveInterval.lean` — exact root interval of the degree-one
  discriminant cross term and its universal scale bound.
- `RHTower/FiniteDegreeReciprocalPerturbation.lean` — **coercive Hermitian perturbation stability**
  (`posDef_add_of_coercive`) and the conjugate-pair reciprocal blindness theorem.
- `RHTower/ReciprocalSeamZerothMoment.lean` — reciprocal seam atoms, absolute convergence of every
  positive-order moment, divergence of the zeroth, and the `Infinite XiZeroCopy` instance.
- `RHTower/RealSourceMicrolocalQuartet.lean` — real even quartet polynomial, its exact zero set,
  and the point-supported distribution whose Laplace transform it is.
- `HTGeometry/EvenFrequencySeamMoments.lean` — the whole seam-moment layer of the FE-even frequency
  family: closed form `T_k = (-1)^(k+1) M_k/(2k-1)!`, half-turn repair, sign alternation, the
  measure-level positive cone, finite signed atoms, bounded packets against the sharp threshold
  `(17 + 2√70)/3`, and polynomial coefficient multipliers. Builds on the pre-existing
  `HTGeometry/SingleEvenFrequency.lean`.
- `HTGeometry/ContractionCompressionExhaustion.lean` — dense compression exhaustion for a bounded
  operator, and the rank-one finite-depth blindness witness.
- `RHTower/MonomialTailGateBound.lean` — coercivity is bounded by every diagonal entry; the shifted
  Hankel gate decays like `R^(2d)`.
- `RHTower/LoewnerCongruenceNormalization.lean` — **Sylvester congruence invariance for complex
  Hermitian matrices** (`posSemidef_congruence_iff`, `posDef_congruence_iff`,
  `negativeSubspace_congruence`) and the relative-contraction normalization.
- `RHTower/PositiveJetHorizonLevelBlindness.lean` — the `ξ - ξ(2)` countermodel: same positive
  jets, same functional equation, same Schwarz reality, same growth envelope, off-line zero.
- `RHTower/SummationGraphDenseCollapse.lean` — the finite summation graph in `ℓ² ⊕ ℂ` has trivial
  orthogonal complement, so its closure is everything; includes `ellTwo_const_eq_zero`.
- `RHTower/FixedRankHankelNonStieltjes.lean` — the exact quadratic-form split of a signed-atom
  shifted Hankel block, the **explicit Lagrange-budget threshold** `ε = 1/(1 + Σ L_j(1)²)` that
  replaces the eigenvalue/compactness step, and the node-polynomial failure vector.
- `RHTower/BoundaryWeylThresholdNonMonotone.lean` — dual-vector extraction from non-proportional
  functionals, the realizing positive definite bulk form, and the variational Schur threshold.
- `RHTower/PoleBudgetUvarovNoGo.lean` — the one-negative-square pole-budget form, its positive
  completion, the invisible negative direction, and the degree-one evaluation-functional layer.
- `HTGeometry/BoundaryKernelSchurSplit.lean` — **the coordinate-free rank-one Schur split.**
  `exists_kernelRiesz` builds the `ker β`-representative of any vector from kernel positive
  definiteness alone (orthogonal projection ∘ operator, injective hence surjective in finite
  dimension); `repairedForm_split` is the exact congruence transport
  `H[v] = A[v - (βv)(q - w)] + ‖βv‖²(A q + t - A w)`; `repairedForm_pos_iff` /
  `repairedForm_nonneg_iff` are the scalar Schur criteria; `shadow_scalar_not_faithful` is the
  positive-scalar/negative-kernel countermodel on `ℂ²`.
- `HTGeometry/StieltjesExteriorChristoffelMonotone.lean` — **zero location for Stieltjes moment
  bulks** (`ShiftedPositiveAt`, `shiftedPositiveAt_of_measure`, `monicOrtho_root_ge`) and the
  resulting exterior monotonicity of the Christoffel–Darboux diagonal and of the Christoffel
  function (`cdKernel_diag_strictAntiOn`, `christoffel_strictMonoOn`).  The monotonicity proof is
  purely algebraic — the node product, not the logarithmic derivative.
- `RHTower/ReciprocalAtomTestSpaceClosure.lean` — **the whole reciprocal-atom test layer on the
  actual `xi` divisor**: the folded atom set `Y`, the compact test set `K = Y ∪ {0}`
  (`isCompact_xiReciprocalTestSet`), isolatedness of every nonzero point, the conjugation-symmetric
  isolator and its continuity on `K`, the form `xiQZero`, its uniform-norm modulus
  (`norm_xiQZero_sub_le`), transfer of positivity to uniform limits, and the atom-visibility
  criterion equivalent to RH.  This is the reusable base for the whole `Q₀` card family.
- `RHTower/ReciprocalAtomCounterterm.lean` — folded atom multiplicities (`xiAtomMultiplicity`,
  finite fibers, conjugate equality), the exact isolator readings `M_a a ζ²` and `2 M_a Re(a ζ²)`,
  and the counterterm layer: finite-rank kernel visibility, atom locality, the local domination
  thresholds, the zero-fed rank-one countermodel, and the vanishing-point-mass criterion.
- `RHTower/ReciprocalAtomPolynomialApproximation.lean` — **an elementary replacement for Mergelyan
  on the reciprocal test set.**  `exists_realPolynomial_atomIsolator_approx` builds, for any atom
  and any prescribed vanishing order at the hard edge, a real polynomial approximating the
  conjugation-symmetric isolator uniformly on `Y`: Lagrange basis over the finitely many test
  points of norm `≥ ‖a‖/2`, times `(z/a)^N`, coefficientwise symmetrized.  On top of it:
  `riemannHypothesis_iff_forall_polynomial_xiQZero_nonneg`, the hard-edge counterterm theorem,
  the preconditioner/filter visibility dichotomy, the finite-boundary-ideal equivalence, and
  the unconditional first-trivial-zero pre-gate (`-4/25` is not an atom).
  `xiQZero_polynomialTest_eq_hankel` identifies `Q₀[p]` with the shifted-moment Hankel form.
- `RHTower/FiniteProbeRHNonselection.lean` — **the even-polynomial perturbation sector of `ΞC`.**
  `xiPerturbed R t = ΞC t + R(t²)` with parity, Schwarz reality, entirety, the inherited order-one
  envelope, and the seam-jet divisibility clause.  Two reusable algebraic engines:
  `exists_indep_pair_of_finiteCodim` (a finite-codimension subspace of `ℝ[X]` still meets
  `Xᴺ⁺¹ℝ[X]` in a 2-dimensional slice) and `exists_nonreal_spanning` (**an algebraic replacement
  for the open mapping theorem**: two `ℝ`-independent real polynomials span `ℂ` over `ℝ` at some
  non-real point, proved by the shifted Wronskian vanishing identically).  Consequences: finite
  linear probes, finite-codimension landscape slices, prescribed seam jets, and finite-type source
  functors all fail to select RH.
- `HTGeometry/ShiftedHankelStrictPositivity.lean` — the shifted Hankel quadratic form of a measure
  as a weighted square integral, and strict positive definiteness of every finite block from
  `d+1` charged positive points (with the singular-block contrapositive).
- `RHTower/SeamJetFunctionComplete.lean` — holomorphic germs with equal Taylor coefficients agree
  (`eventuallyEq_of_iteratedDeriv_eq`), entire functions agreeing near a point are equal
  (`entire_eq_of_eventuallyEq`), and the all-order seam-log jet determines an even entire function
  up to its central scalar, hence determines its zero divisor.  Also `triangular_determines`:
  a triangular coordinate change over the seam-log coefficients is invertible.
- `RHTower/SeamWeldIdentity.lean` — `Ξ' w / (w Ξ w) = 2 logDeriv Φ (w²)` for `Ξ w = Φ (w²)`, its
  holomorphic extension across the seam, and the odd-to-even tower division.
- `RHTower/SeamSquareTestNotAdmissible.lean` — the coefficient reversal `seamRevPoly`, the exact
  hard-edge exponent of the reciprocal-seam square test, its non-interval-integrability across the
  seam, and its exactly polynomial decay at infinity.
- `RHTower/CountableWindowBasis.lean` — rational windows isolate the points of any discrete set, so
  a countable window family detects all off-seam divisor mass.
- `RHTower/DeterminantLineDivisorBlindness.lean` — polynomial sections of the trivial line realize
  any prescribed finite divisor; nowhere-zero homotopies already contain the nonvanishing claim;
  signed crossing counts cancel.
- `RHTower/AcyclicFiniteFibersDerivedLimit.lean` — `lim` and `lim¹` of a tower as kernel/cokernel of
  shift-minus-identity, their vanishing on towers of zero objects, and contractibility of the
  specialized finite prime complexes in the strip.
- `RHTower/TranslationInvariantDefectForm.lean` — a translation-invariant Hermitian form pairs only
  conjugate frequencies, off-real orbits are isotropic, and each such orbit is a hyperbolic plane.
- `RHTower/HurwitzScalarComparisonNoGo.lean` — the exponential seam defect `q(1-s) - q(conj s)`
  vanishes along the critical line and has nonzero transverse slope, so it is not a continuous
  scalar multiple of any holomorphic germ vanishing there.

## Triage of the remaining folder (2026-08-16 scan)

**Warning learned the hard way:** "no open gate box" does *not* mean "formalized". Several such
cards (e.g. `zeta-summation-constraint-graph-dense-collapse`) named a Lean module that proved only
one auxiliary lemma. Always compare the card's numbered statements against the module's actual
declaration list before promoting.

- 131 cards have open gate boxes that are **only** Lean/formalization boxes — these are the
  highest-yield targets. Many say "optional finite-dimensional theorem".
- 75 cards carry no open box at all (status must be read from prose).
- 11 cards already name a Lean declaration but still have an open Lean box.

Known heavy prerequisites still outstanding, with the cards they gate:

- ~~entire-function **order** — needed by the `finite-*-rh-nonselection` family.~~  **Resolved
  2026-08-16 without an order lower bound**: the perturbation differs from `ξ` by a polynomial, so
  it carries exactly the corpus envelope `XiC_order`; the whole family is now stage 3.
- Newton's inequalities for elementary symmetric functions — `pa9-turan-newton-floor`.
- Hölder + a reflection-stable meromorphic carrier — `gamma-reflection-clock-observable-split`
  (the corpus has `hypertranscendentalOver_ratFunc_gammaUpperMero` and
  `hypertranscendentalOver_ratFunc_digammaMero`, but `upperEndMeroField` is a germ field at the
  upper end and is not stable under `z ↦ 1 - z`; the log-derivative route
  `R'/R = 2ψ + π cot` avoids the algebraic-extension step).

## Triage snapshot

- 83 cards carry no open gate box at all (status must be read from the prose).
- 165 cards mention at least one Lean module that already exists in `formal/`.
- 330 cards mention no Lean module at all.
