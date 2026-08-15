# Stage 2 → Stage 3 promotion ledger

Working note for the sweep that formalizes every card sitting directly in
`docs/drafts/pipeline/2-fully-proven/` (subfolders excluded) and moves it to `3-formalized/`.

Promotion recipe:

1. Audit the card's numbered statements against real Lean declarations — never against the card's
   own Lean table (`card-lean-tables-can-be-stale-or-absent`).
2. Formalize the missing statements unconditionally (no `sorry`, no `axiom`, no unproved premise).
   Structural hypotheses that *define* the objects are part of the statement and are allowed;
   unproved analytic inputs are not.
3. `lake env lean <module>` clean **including warnings**, umbrella import added,
   `#print axioms` = `propext, Classical.choice, Quot.sound`.
4. `git mv` the paper card to `3-formalized/`, set `Stage: 3-formalized`, add a
   `Formalized companion:` pointer, and write `<id>-formalized.md` beside it.
5. Repoint inbound links that named the old `2-fully-proven/<id>.md` path.

## Promoted

| Card | New Lean work | Modules |
|---|---|---|
| `one-replica-local-pauli-planar-cavity-decay` | exact Pauli pencil, Dyson--Hall atomlessness, algebraic coordinate laws, scalar absolute continuity, Fourier and operator-norm decay | `HTGeometry/OneReplicaTracelessPauliSpectralDecay`, `FiniteDysonHallAtomlessness`, `FreeFockMatrixSemicircleCoordinateLaw`, `FreeFockMatrixSemicircleFourierDecay` (new) |
| `radial-krylov-projected-complete-incidence-law` | exact radial/Krylov projection, incidence, return-error, and Gaussian-mixture family | `HTGeometry/KrylovProjectedCompleteIncidenceLaw` |
| `bures-incidence-minimax-coarea-law` | separable positive-reporter Alberti approximation and compact-target minimax/product-capacity closure | `HTGeometry/FiniteDimensionalOperatorAlbertiLaw`, `SeparableBuresPositiveReporterLaw`, `SeparableBuresAlbertiApproximationLaw`, `SeparableBuresCompactTargetMinimaxLaw` |
| `positive-shell-koszul-cartier-obstruction-reciprocity` | source-specific positive-shell analytic carrier, finite/countable Koszul homology, conormal and exterior-basis laws | `RHTower/PositiveShellKoszulCartierObstruction`, `HTGeometry/CommonFactorKoszulHomology` |
| `route-g2-relative-volterra-source-germ-weld` | none (verified only) | `RHTower/SuzukiVolterraSourceGermWeldRigidity` |
| `intrinsic-replica-observer-spectral-action-law` | none (verified only) | `HTGeometry/IntrinsicReplicaObserverSpectralActionLaw`, `HTGeometry/LocalHamiltonianObserverSpectralActionLaw` |
| `route-r-degree-six-gamma-corona-local-global-fracture` | warning fix | `RHTower/RouteRDegreeSixGammaCoronaLocalGlobalFracture` |
| `fixed-observer-channel-codimension-law` | quantum block consequence `(4)` | `HTGeometry/FixedObserverBlockChannelCodimension` (new) |
| `mass-shifted-three-point-orbit-polarity-no-go` | actual-Xi chamber + confluent polarity | `RHTower/MassShiftedThreePointOrbitPolarity` (new) |
| `mass-shifted-stochastic-order-null-flag-collapse` | none (already complete) | `HTGeometry/MonotoneLikelihoodRatio`, `RHTower/XiShiftedHankelBoundaryStochasticOrderNoGo` |
| `route-j-cell-hodge-boundary-diagonal-rigidity` | warning fix + audit | `RHTower/CCMFirstClockPrimitivePromotedCellHodgeBoundaryRigidity` |
| `route-e-block-defect-energy-reduction` | note fix + audit | `RHTower/MobiusBlockDefectCompression`, `RHTower/MobiusBlockDefectEnergy` |
| `route-e-forward-interval-hall-reduction` | interval sufficiency + quarter threshold | `HTGeometry/ForwardWindowHallMatching` (new) |
| `exact-penalty-robust-circuit-bellman-duality` | Theorems A–C in full | `HTGeometry/ExactPenaltyCircuitBellman` (new) |
| `static-orbit-net-no-go-and-circuit-bellman-law` | Theorems A–D in full | `HTGeometry/EuclideanSphereCoveringBound`, `HTGeometry/StaticOrbitNetBellmanLaw` (both new) |
| `all-replica-local-casimir-hall-expansion` | boxed `(6)` bi-tightness and `(7)` off-kernel Hall | `HTGeometry/CentralCasimirComplementHallExpansion` (new) |
| `nearest-neighbor-chain-projective-spectral-maximality` | qubit specialization + Corollary 2 `(18)` | `HTGeometry/NearestNeighborQubitChainMaximalRank`, `CommutingHermitianSpectrumSum`, `CommutingTermTemporalRankBound` (all new) |
| `complete-graph-local-projective-spectral-maximality` | complete-graph instance + `(13)` | `HTGeometry/CompleteGraphLocalProjectiveMaximality` (new) |
| `fast-forwardable-stratum-codimension-obstruction` | tube inclusion, budget step, Gaussian shell positivity, `(4)`–`(6)`, `(14)`–`(15)` | `HTGeometry/FastForwardableStratumCodimension`, `GaussianIntervalPositivity` (both new) |
| `mixed-periodic-synthesis-carrier-obstruction` | shifted small-ball, fine-lattice density, `(3)`, `(5)`, boxed `(6)` | `HTGeometry/MixedPeriodicCarrierObstruction`, `LatticeGaussianDensity` (both new) |
| `geometric-skeleton-brown-ramp-transfer-law` | Theorems A, B, C in full | `HTGeometry/GeometricSkeletonBrownRamp` (new) |
| `disconnected-local-spectral-factorization-genericity` | none (already complete in the hypergraph form) | `HTGeometry/DisconnectedProjectiveGapModuleLaw`, `HypergraphComponentFactorization`, `HypergraphProjectiveSpectralFactorization`, `BlockSumSpectralGenericity` |
| `beta-threshold-complete-incidence-law` | all six Lean layers: Hoeffding sandwich, beta-density derivative, coarea `(12)`/`(17)`, return-paid-once `(18)`, replica projector `(19)`–`(22)`, monomial separation `(25)`–`(26)` | `HTGeometry/BinomialTailBetaThreshold`, `BetaThresholdIncidenceLaw`, `BoundedReplicaThresholdProjector` (all new) |
| `two-replica-singlet-pauli-hall-expansion` | `(7)` on any register, global `(11)`, both directions of `(12)`, and the assembly `(14)`–`(17)` giving the boxed `(4)` | `HTGeometry/TwoReplicaTensorHilbertSchmidt`, `TwoReplicaEdgeHallExpansion`, `TwoReplicaEdgeHallAssembly` (all new) |
| `traceless-local-two-query-haar-separation-law` | identity-coordinate gap; the literal product-stabilizer score with its transfer expansion `(5)`; the exact Haar value `(3)` for that score; the comparison capstone `(4)` | `HTGeometry/TracelessPauliIdentityCoordinate`, `ProductStabilizerPhysicalScore`, `FiniteUnitaryHaarReindex`, `RankOneProjectionConjugation`, `LiteralTwoQueryHaarBenchmark` (all new) |
| `positive-source-weights-do-not-bound-loewner-budget` | arbitrary-source Finsupp Loewner assembly, unbounded positive-cone scaling obstruction, and exact normalized mass-cap equivalence | `RHTower/PositiveSourceLoewnerBudget` (new) |
| `li-kernel-not-coefficient-positive` | literal reciprocal-seam first-kind Chebyshev kernel, exact first/second Taylor coefficients, strict sign obstruction, and `n = 1` certificate | `RHTower/LiReciprocalKernelCoefficientSign` (new) |
| `scale-invariant-source-orientation-cannot-pay-budget` | form-level scale-invariant source-orientation cone theorem and one-sided recession gate | `RHTower/SourceNormalizationBudgetGates` (new) |
| `finite-source-normalizations-leave-budget-recession` | exact affine normalization class, preserved recession directions, two-sided zero gate, and PSD corollary | `RHTower/SourceNormalizationBudgetGates` (new) |
| `degree-one-discriminant-tail-stability` | exact five-term tail expansion and error budget, strict-margin positivity, conjugate-pair negative square, and finite-bulk pair update | `HTGeometry/DegreeOneDiscriminantTailStability` (new) |
| `finite-degree-shifted-hankel-tail-stability` | literal Rayleigh `lambda_min`, exact Frobenius/row-sum budgets, both strict tail gates, and every principal determinant | `HTGeometry/FiniteDegreeShiftedHankelTailStability` (new) |
| `real-axis-kernel-positivity-nonselector` | literal three-by-three Hermitian inverse pair, negative index two, full real-axis kernel polynomial and explicit off-curve negative direction | `HTGeometry/RealAxisKernelPositivityNonselector` (new) |
| `dirichlet-real-analytic-postcomposition-high-line-sign-rigidity` | generic real-analytic germ capstone, literal every-height coordinate corollary, and Route-I sharp-window specialization | `HTGeometry/DirichletAnalyticPostcompositionSignRigidity`, `RHTower/CCMSharpPrimeWindowAnalyticPostcompositionNoGo` (re-audited) |
| `square-zero-compatibility-defect` | exact polarization, square-zero compatibility equivalence, and symmetric two-scalar form over arbitrary commutative rings | `HTGeometry/SquareZeroCompatibilityDefect` (re-audited) |
| `involution-selects-minimal-event-record` | complementary involution projectors, exact kernel/range and cokernel record, and trace-two `4/6/4` specialization | `HTGeometry/EventInvolutionComplement` (re-audited) |
| `noninvertible-event-complementary-record-boundary` | postcomposition kernel no-go, faithful-record dimension lower bound, equal-parent kernel/cokernel bijection, rank-six boundary, and scaling noncanonicity | `HTGeometry/EventComplementaryRecord` (re-audited) |
| `fixed-carrier-quadratic-variation-flatness` | exact absorption cocycle, diamond flatness, Gram-square restriction defect, compression curvature, and unit-test converse | `HTGeometry/NestedProjectionQuadraticVariation` (re-audited) |
| `pure-spinor-color-cancellation-normal-selection` | literal Cartan coordinate pairing, all same-sector and weak-scalar exclusions, and surjectivity for every nonzero colour bivector | `HTGeometry/PureSpinorColorNormalSelection` (re-audited) |
| `color-gram-minkowski-orbit-theorem` | Gram positivity, Cauchy--Binet/Lorentz cone, left-unitary orbit equivalence, positive-cone surjectivity, and quotient homeomorphism | `HTGeometry/ColorGramMinkowskiCone`, `ColorGramMinkowskiOrbit` (re-audited) |
| `event-square-zero-unification-boundary` | exact generic two-sided radical closure, square-zero product, endpoint bimodule actions, upper-block product/commutator, direct-product quotient, and typed quadratic cancellation | `HTGeometry/EventSquareZeroUnificationBoundary`, `EventSecondOrderSoldering` (re-audited) |
| `split-event-quadratic-soldering-boundary` | complete split-event block classification, universal endpoint-soldering no-go, quadratic covariant cancellation, parallel composite, and conjugacy lock | `HTGeometry/EventSecondOrderSoldering` (re-audited) |
| `sonin-aperture-ward-curvature-transgression` | trace-class compression curvature, literal negative Hilbert--Schmidt square, faithful flatness, and canonical Ward transgression | `RHTower/TraceClassCompressionCurvature`, `SoninApertureCurvatureTrace`, `SoninApertureWardCurvature` (re-audited) |
| `sonin-aperture-ward-cohomology-fourier-parity-no-go` | aperture Bianchi/gauge coboundary, Fourier parity, invariant-reader annihilation, and exact Ward-energy flatness iff | `RHTower/SoninApertureWardPotential`, `SoninApertureFourierParityNoGo` (re-audited) |
| `square-aperture-positive-excess-convex-duality` | literal nonnegative finite square-aperture dual, exact optimizer/defect, prime-side Fubini identity, sharp-source normalization, and explicit conditional RH consumer | `RHTower/CCMSharpPrimeWindowSquarePositiveExcessDuality` (re-audited) |
| `strict-two-group-kernel-abelian-boundary` | minimal Peiffer-kernel centrality, centre inclusion, pair commutativity, and faithful-source abelianness | `HTGeometry/PeifferKernelAbelianBoundary` (re-audited) |
| `crossed-pure-factorization-refinement` | arbitrary-field crossed block factorization and exact four one-index factor refinement | `HTGeometry/CrossedPureFactorizationRefinement` (re-audited) |
| `finite-carrier-spacelike-compression-defect` | finite tensor-square kernel lower bound, noninjectivity, injectivity classification, surjective equality, and self-equivalence corollary | `HTGeometry/FiniteCarrierSpacelikeCompression` (re-audited) |
| `independent-composition-boundary-record-conservation` | exact finite record lower bound, minimal-completion bijectivity/surjectivity, kernel-record equivalence, and total reconstruction equivalence | `HTGeometry/IndependentCompositionBoundaryRecord` (re-audited) |
| `event-order-diamond-carrier-boundary` | typed endpoint-gauge covariance, attachment, matrix trace boundary, universality, and exact one-carrier block-diamond reconstruction | `HTGeometry/EventOrderDiamond` (re-audited) |

| `burnol-divided-shift-evaluation-separation-law` | none (verified only) | `RHTower/BurnolDividedShiftEvaluationSeparation` |
| `burnol-holonomy-cauchy-sector-separation` | none (verified only) | `RHTower/BurnolHolonomyCauchySectorSeparation` |
| `burnol-all-prime-completion-singular-potential-entrance-wall` | all of `(AW0)`--`(AW17)` | `RHTower/BurnolAllPrimeCompletionWall`, `RHTower/BurnolPrimeLogSummability` (both new) |
| `burnol-all-prime-window-hilbert-cartier-jet-wall` | all of `(HJ1)`--`(HJ29)` | `RHTower/BurnolAllPrimeWindowEnergy`, `RHTower/BurnolReciprocalStokesSewing` (both new) |
| `burnol-poisson-subordinate-smooth-cartier-entrance-wall` | all of `(PS1)`--`(PS16)`, incl. the Glasser integral | `RHTower/BurnolPoissonSubordinateWall`, `RHTower/BurnolGlasserIntegral` (both new) |
| `burnol-first-wall-cartier-residue-cancellation-law` | *(in progress)* `(1)`, `(2)`, `(4)`, `(8)`--`(11 fwd)`, `(13)`--`(23 fwd)`, `(24)`--`(28)`, `(29 fwd, pointwise)` | `RHTower/BurnolFirstWallZeroDividedSource`, `RHTower/BurnolFirstWallSourceDecay`, `RHTower/BurnolFirstWallSourceMass`, `RHTower/BurnolFirstWallExteriorMass`, `RHTower/BurnolFirstWallCrossingCorrelation`, `RHTower/BurnolReflectedRawSource`, `RHTower/BurnolReflectedDividedShift` (all new) |
| `burnol-gamma-bockstein-first-wall-extraction-law` | all of `(1)`--`(22)` | `RHTower/BurnolBocksteinLimit` (new), `RHTower/BurnolFirstWallCrossingCorrelation`, `RHTower/BurnolReflectedPotential`, `RHTower/BurnolGammaStein*`, `RHTower/BurnolDyadicCommutatorStaircase` |
| `burnol-cofinite-cartier-wall-trace-horizon` | all of `(CH1)`--`(CH23)` | `RHTower/BurnolCofiniteHorizonGerm` (new), `RHTower/BurnolPrimeCartierWallTrace` |
| `burnol-prime-two-causal-cartier-collar-law` | all of `(3)`--`(25)` | `RHTower/BurnolGammaSteinCollarKernel`, `RHTower/BurnolGammaSteinMoments`, `RHTower/BurnolCollarKernelSeries`, `RHTower/BurnolPrimeTwoCollarSymbol` (all new) |

| `nomological-homotopy-geometry` (26-card field batch) | exact theorem witness for every card; new finite-dimensional gauge spectral-flow invariance/pure-gauge rigidity; missing minimal-law umbrella wiring | `HTGeometry/NomologicalHomotopyGeometry/*`, `HilbertMetric/NomologicalCrossGram` |
| `centralizer-centered-shortcut-history-recurrence-energy-law` | none (verified only) | `HTGeometry/StaticShortcutRecurrenceEnergyLaw`, `StaticShortcutReplicaProjectorFrameLaw` |
| `observer-channel-recurrence-production-dichotomy-law` | none (verified only) | `HTGeometry/StaticShortcutRecurrenceChannelProductionLaw` |
| `resolution-quotient-replica-frame-capacity-law` | none (verified only) | `HTGeometry/ResolutionQuotientReplicaFrameCapacityLaw` |
| `return-excised-cross-recurrence-capacity-law` | none (verified only) | `HTGeometry/StaticShortcutCrossRecurrenceCapacityLaw` |
| `selector-partition-observer-channel-recurrence-law` | none (verified only) | `HTGeometry/StaticShortcutSelectorPartitionLaw` |
| `static-circuit-two-memory-orthogonality-law` | Bochner ensemble collision `(14)`/`(27)`; vectorized conjugation channel and replica tensor powers; one-gate moment channel with its depth-`s` word expansion `(16)`--`(19)`; static diagonal flow, completed static projection, universal sector and the concrete three-sector collision `(20)`; zero-temperature reconstruction `(28)`--`(30)` | `HTGeometry/StaticCircuitEnsembleZeroTemperature`, `PureConjugationChannel`, `StaticCircuitReplicaWordDictionary`, `StaticCircuitReplicaSectorRealization` (all new) |
| `local-circuit-heap-capacity-law` | heap Green reporter and its accessibility bound, trace partition sum with the negative-binomial value, optimized weight, finite heap incidence, one-dimensional gate alphabet with its length-independent degree bound, capacity entropy split and `o(D)` profile limit | `RHTower/LocalCircuitHeapGreenReporter` (new) |
| `concurrent-causal-heap-accessibility-law` | trace monoid with cancellativity and length grading, Boltzmann trace law with exact cylinder mass and expected prefix count, concurrent causal accessibility with its complexity sandwich and Green relation, causal heap capacity, soft causal reporter with dimension-free Lipschitz/transport/Duhamel stability, free-word first-entrance reduction, and the relative-entropy projection of the preparation action | `RHTower/CircuitTraceMonoid`, `CircuitTraceBoltzmann`, `CircuitCausalAccessibility`, `CircuitSoftCausalReporter`, `CircuitFreeWordFirstEntrance`, `CircuitPreparationActionEntropy` (all new) |

## New reusable infrastructure built during the sweep

- `HTGeometry/BinomialTailBetaThreshold` — Hoeffding's lemma for a two-point variable
  (`1 - x + x e^t ≤ exp(t x + t²/8)`, from mathlib's sub-Gaussian MGF and the Bernoulli measure),
  the binomial head/tail Chernoff bounds `≤ exp(-2 r s²)`, and the exact identity
  `B'_{r,k} = r C(r-1,k-1) u^{k-1}(1-u)^{r-k}` with unit mass.  mathlib has Hoeffding's lemma but
  no binomial tail polynomial and no Chernoff–Hoeffding tail bound.
- `HTGeometry/BoundedReplicaThresholdProjector` — `r`-fold tensor powers of vectors and operators
  in the product basis `Fin r → n`, slotwise multiplication/adjoint, the product factorization
  `⟨v^{⊗r}, (⊗ A_i) v^{⊗r}⟩ = ∏ ⟨v, A_i v⟩`, and the Gram identity
  `⟨w, Mᴴ M w⟩ = ∑ |(M w)_c|²` (the source of every positivity statement).

- `HTGeometry/TwoReplicaTensorHilbertSchmidt` — a sitewise two-replica tensor product has the
  trace, the adjoint and the Hilbert–Schmidt pairing of a product, factor by factor; plus the
  local orthogonality relations between `span{I, F}` and the replica differences `D_a`, `F D_a`.
- `HTGeometry/TwoReplicaEdgeHallAssembly` — the endpoint-evaluation reader `edgeReader`: fixing one
  matrix index pair at each endpoint and multiplying back the two identity/swap letters inverts a
  tensor-product family on one mismatch type.  Use this instead of a Gram-matrix argument whenever
  the spectator letters are linearly independent but **not** orthogonal (`Tr(I·F) = 2 ≠ 0`).

- `HTGeometry/FiniteUnitaryHaarReindex` — **normalized Haar transfers along a change of matrix
  index type**: the pushforward along a continuous surjective group hom of compact groups is a Haar
  probability measure and `Measure.haarMeasure_unique` pins it down.  Two instances must be fed by
  hand: `IsHaarMeasure (finiteUnitaryHaar κ)` (it is a `def`, so mathlib's instance is invisible)
  and `SecondCountableTopology` on both `Matrix κ κ ℂ` and its unitary subtype.  mathlib has Haar
  invariance under translations only.
- `HTGeometry/RankOneProjectionConjugation` — a Hermitian idempotent of unit trace pairs with every
  observable as one diagonal entry of the observable conjugated by a fixed unitary.  Use this
  whenever a corpus result is stated for a *prepared coordinate state* and you have a pure state.
- `HTGeometry/ProductStabilizerPhysicalScore` — sitewise tensor products of single-qubit matrices;
  the stabilizer **density matrix** `(I + s σ_p)/2` (Hermitian, idempotent, unit trace) with its
  exact six-state Pauli pairing.  Going through densities rather than state vectors keeps `√2` out
  of all twenty-four evaluations.

- `HTGeometry/CirclePoincareWirtinger` — **Wirtinger's inequality**: for a `C¹` function on
  `[a,b]` with equal endpoint values, the mean-square deviation from the average is at most
  `((b-a)/2π)²` times the mean square of the derivative.  Proved from mathlib's `AddCircle`
  Parseval identity plus the Fourier-coefficient/derivative relation.  mathlib has no Poincaré or
  Wirtinger inequality anywhere.

- `RHTower/BurnolPrimeLogSummability` — `∑ 1/(p (log p)²) < ∞` by telescoping, Euler divergence on
  the prime subtype, `log^k = o(x^δ)`, and `u^k e^{-2y√u} ≤ C/u²`.
- `RHTower/BurnolGlasserIntegral` — `∫₀^∞ e^{-t²-b²/t²} dt = (√π/2) e^{-2b}` and the `1/2`-stable
  subordination identity `e^{-y√λ} = (y/(2√π)) ∫₀^∞ s^{-3/2} e^{-y²/(4s)} e^{-sλ} ds`.
- `RHTower/BurnolGammaSteinMoments` — the master collar moment `∫ 2z e^{-z} z^{s-1} P(z) du` as a
  Gamma combination, via the substitution `z = C e^{-2u}`.

- `HTGeometry/FixedObserverBlockChannelCodimension` — block tangent channel, real dimension
  `2(d−1)`, observer rank = QFI rank.
- `HTGeometry/ForwardWindowHallMatching` — one-sided window Hall matching ⇔ interval condition.
- `HTGeometry/ExactPenaltyCircuitBellman` — gate words, reachable layers, exact-penalty value,
  Bellman equation, unit gate step, maximal-subsolution duality, compact-gate exact recovery at a
  finite threshold, and the Lipschitz-certificate condition number.
- `HTGeometry/EuclideanSphereCoveringBound` — volumetric packing bound for Euclidean balls,
  maximal separated nets, and the `(1 + 2L/ε)^m` Lipschitz-image net for the unit sphere.
  mathlib has the covering-number *definitions* but no ball-packing bound.
- `HTGeometry/CentralCasimirComplementHallExpansion` — completing a Hermitian central-Casimir
  family by its kernel projector; exact bi-tightness and exact Hall expansion off the kernel.
  (Four RCLike scaling declarations in `CentralCasimirHallExpansion` were made public for this.)
- `HTGeometry/CommutingTermTemporalRankBound` — additive spectra have at most the summed anchored
  temporal rank; `m` commuting `v`-level terms give rank at most `m(v−1)`.
- `HTGeometry/CommutingHermitianSpectrumSum` — **every eigenvalue of a sum of pairwise commuting
  Hermitian matrices is a sum of eigenvalues of the summands**, proved without a simultaneous
  eigenbasis (block-diagonality in one summand's eigenbasis).  mathlib has no such lemma and no
  `spectrum (a+b) ⊆ spectrum a + spectrum b` for commuting elements.  Plus the commuting-term
  temporal-rank law and the tensor-factor level count.
- `HTGeometry/NearestNeighborQubitChainMaximalRank` — the `q = 2` path law with simple spectrum.
- `HTGeometry/CompleteGraphLocalProjectiveMaximality` — the all-to-all two-local architecture as a
  connected hypergraph, with simplicity, maximal projective independence and rank `q^n − 1`.
- `HTGeometry/GaussianIntervalPositivity` — the standard Gaussian charges every nondegenerate
  interval, box, and sup-norm shell.  mathlib has the density and its positivity but not the
  resulting set positivity.
- `HTGeometry/FastForwardableStratumCodimension` — bounded synthesis certificates, the Duhamel
  tube, the relative-budget step, the Gaussian codimension ceiling, and the deterministic radial
  tube volume.
- `HTGeometry/LatticeGaussianDensity` — the standard Gaussian density floor on `|x| ≤ 2`, the
  *shifted* small-interval and small-ball bounds, the separated-centres bound, and the
  fine-lattice density: the `δ/t`-neighbourhood of a `1/t`-rescaled full lattice keeps a
  `t`-independent share of Gaussian mass.
- `HTGeometry/MixedPeriodicCarrierObstruction` — the radial identity, the mixed tube inclusion,
  and the codimension ceiling `κ ≤ m − dim W − rank Γ` in both Gaussian and Haar form.
- `HTGeometry/GeometricSkeletonBrownRamp` — uniform simulation complexity, backward circuit
  composition, the geometric-skeleton lower ramp, the easy-seed upper ramp, and the skeleton
  length / union-bound / replica-order arithmetic.
- `HTGeometry/StaticOrbitNetBellmanLaw` — coefficient Hamiltonians, the `√m` and Duhamel Lipschitz
  bounds, the static orbit net, the min-plus layer recursion, the max-plus overlap recursion
  (general pullback form plus the unitary instance and the monotone-reader form), and the robust
  Bellman calibration lower bound.

## Shared infrastructure for the trace/heap cluster

`RHTower/CircuitTraceBoltzmann` adds the Boltzmann layer: summability below the dependence radius,
the partition function with its lower bound one and negative-binomial upper bound, the normalized
mass with modularity and monotonicity, the exact cylinder mass `z^{|u|}`, the normalized weight
`traceWeight` summing to one, and the expected causal-prefix count.

`RHTower/CircuitCausalAccessibility`, `CircuitSoftCausalReporter`,
`CircuitFreeWordFirstEntrance` and `CircuitPreparationActionEntropy` build the reporter layer:
the causal success event, its accessibility and preparation action, the two-weight comparison and
its optimum, the Green relation, the causal heap-capacity law, the soft (clipped-ramp) reporter
with its `1/δ` Lipschitz constant, Kantorovich--Rubinstein transport stability and Duhamel source
stability, the free-word first-entrance collapse, and Gibbs' inequality with the information
projection of the preparation action.

`RHTower/CircuitTraceMonoid` builds the trace monoid itself: append congruence of the independent
swap relation, the monoid structure on `List α / TraceEq`, the length morphism, left and right
cancellativity (from the parent's pair-projection reconstruction), the causal prefix order with its
cylinder equivalence `Trace ≃ ↑u`, and the length grading
`(Σ ℓ, FixedTraceClass independent ℓ) ≃ Trace independent`.

`RHTower/LocalCircuitHeapGreenReporter` builds the measure-side layer: the heap Green reporter and
its accessibility bound, the trace partition sum with its negative-binomial value, the optimized
geometric weight, the finite heap incidence, the one-dimensional gate alphabet `ChainLetter` with a
chain-length-independent dependence-degree bound, and the capacity entropy split with its `o(D)`
profile limit.

Both are the shared engine for `concurrent-causal-heap-accessibility-law`,
`first-entrance-gate-renewal-prefix-law`, and `first-entrance-gate-capacity-discrepancy-law`.

## FEG-1 — first-entrance gate renewal and prefix law

- Promoted `2-fully-proven/first-entrance-gate-renewal-prefix-law.md` → `3-formalized/`.
- Every statement of the card is Lean-certified unconditionally: `(ER)`, `(2.1)`, Cor. 2.2--2.4,
  Thm 3.1 (`(FH)` and `(Kraft)`), Thm 4.1 `(CS)` with the unreachable case, Cor. 4.2 `(TR)`,
  Thm 5.1 `(IP)` with its minimizer, Cor. 5.2 `(EM)`, Thm 6.1 `(CU)`, Section 7 `(RC)`.
- Modules: `RHTower/DiscreteMarkovRenewal`, `RHTower/GateWordFirstHit`,
  `RHTower/GateWordRenewalBridge`, `RHTower/GateWordComplexityLaws`,
  `RHTower/GateWordInformationProjection`.
- Reusable infrastructure now available for the sibling capacity-discrepancy card:
  - the whole discrete renewal engine (`greenMass`, `entranceMass`, `returnMass`, `returnIterate`,
    the first-entrance split bijection, the Neumann resolvent, the geometric bounds);
  - the uniform gate chain on `List Γ` (`gateKernel`, `gatePath`, `wordTarget`) together with the
    theorem that positive-weight paths are exactly canonical prefix chains, which converts any
    path-sum statement into a word-sum statement;
  - prefix-free word combinatorics (`wordCompletions`, the Kraft inequality) and the minimal
    hitting word (`exists_minimal_hitting_word`);
  - word counting in `ℝ≥0∞` (`tsum_list_length_apply`) and the geometric gate prior with its
    summability and unit mass;
  - a general information projection (`isLeast_discreteRelativeEntropy`, `conditionedWeight`) over
    an arbitrary index type, which supersedes the trace-specific version in
    `RHTower/CircuitPreparationActionEntropy` for new work.
- Verification: targeted foreground `lake env lean` green on all five modules; `#print axioms` on
  every capstone reports only `propext`, `Classical.choice`, `Quot.sound`.

## Corpus facts found during the sweep (do not rebuild)

- Duhamel operator bound: `HTGeometry.exp_skewAdjoint_sub_exp_skewAdjoint_norm_le` and
  `HTGeometry.selfAdjoint_unitaryEvolution_norm_sub_le` in
  `HTGeometry/FiniteHorizonCStarPerturbationLaw.lean`.
- Lipschitz image cover: `HTGeometry.externalCoveringNumber_image_le` in `HTGeometry/BoxDimension.lean`.
- mathlib owns `Metric.externalCoveringNumber` / `packingNumber` / `maximalSeparatedSet`
  (`Mathlib/Topology/MetricSpace/CoveringNumbers.lean`); it has **no** ball-packing volume bound.
- MLR saturation: `HTGeometry/MonotoneLikelihoodRatio.lean`.
- Strong Xi height gap `41/2`: `RHTower/XiEndpointStrongHeightGap.lean`;
  centered strip `u < 1/4`: `RHTower.xi_divisor_support_centered_re_sq_lt_quarter`.
- Pauli product-input observer rank constant: `HTGeometry.productInputObserverRank`.

## In flight

`nearest-neighbor-chain-projective-spectral-maximality` — its main theorem `(2)`, simple spectrum,
recurrence density `(17)` and the spanning-path corollary are all already in the corpus
(`NearestNeighborQuditPathGenericityLaw`, `NearestNeighborQuditPathRecurrenceLaw`,
`ArbitraryGraphLocalHamiltonianGenericityLaw.hermitianSuperspaceMaximalSet_…`,
`MaximallyProjectiveEnergy.injective`, `maximallyProjectiveEnergy_orientedGap_injective`).
Corollary 2 `(18)` is now `HTGeometry/CommutingTermTemporalRankBound.anchoredTemporalRank_sum_le_three_mul`
(new).  What remains is a small assembly module stating the card's claims at `q = 2` and the
operator-level step "commuting terms ⇒ additive spectrum" (simultaneous diagonalisation).

`weak-interaction-singular-quantum-time-expansion` — remaining: `(7)`'s finite-family Hausdorff
assembly (easy, given the already-formalized C* Heisenberg stability bound), and the local
generator `(4)`–`(5)`, which is the sibling card `local-interaction-replica-collision-extremality`.

`instant-exact-complexity-calibration-singularity-law` — its `(4)` is already
`HTGeometry.le_lipschitzConstant_of_certificate`; its `(7)` needs equation `(6)` of the parent
card `algebraic-two-local-instant-exact-complexity`, which is not yet formalized.  Do the parent
first.

## Scoped, not yet done

- `local-interaction-replica-collision-extremality` — Theorems A and B are already
  `ReplicaCollisionExtremality` (`fidelityReplicaResonantMass_eq_collisionMass`,
  `fidelityReplicaCollisionMass_floor_le`, `all_fidelityReplicaCollisionMass_eq_floor_iff`).
  Remaining: Theorem C (assemble from the path law), C2 (instantiate
  `AffineLinePolynomialAvoidance` with the obstruction polynomials plus `ρ(A) ≤ n(q−1)`),
  E `(9)` (uniform-weight specialisation) and F `(10)`–`(12)` (the combinatorial limit
  `a_{D,m} → m!` plus moment-determinacy of `Exp(1)`).
- `component-recurrence-torus-and-replica-factorization-law` — component-histogram law done in
  `ComponentReplicaCollisionLaw`; the product-torus embedding `(1)`–`(3)` and the uniform-SFF
  product/asymptotics remain.
- `weak-interaction-singular-quantum-time-expansion` — `(7)`'s finite-family Hausdorff assembly,
  plus Theorem C/C2 of the card above.

## Scoped: needs the product-torus Poincaré programme

`low-replica-complete-incidence-influence-law` and
`cubic-phase-seeded-static-local-full-scale-plateau-law` both need
`Var_{m_d}(F) ≤ ∑_j ∫ |∂_j F|²` on the `d`-torus with constant one, for **Lipschitz** `F`
(the statistic is a max of smooth functions, so it is only a.e. differentiable).

State of that programme:

- one-dimensional Wirtinger for `C¹` periodic functions: **done**
  (`HTGeometry/CirclePoincareWirtinger.wirtinger_intervalIntegral`).
- still to build: (i) Wirtinger for absolutely continuous / Lipschitz periodic functions;
  (ii) the binary law of total variance `Var_{μ⊗ν} F = E_x Var_ν F(x,·) + Var_μ (E_ν F)`;
  (iii) the Jensen step `Var_μ (E_ν F) ≤ E_y Var_μ F(·,y)`; (iv) the induction over `Fin d`
  through `measurePreserving_piFinSuccAbove`.  Items (ii)–(iii) are Fubini plus algebra; (i) and
  (iv) are the real work.  Do **not** try to get the dimension-free constant from a coupling or
  a one-step Cauchy–Schwarz: both lose a factor `d`.

## Audited, next in line

`local-interaction-replica-collision-extremality` is the highest-leverage remaining card: its
Theorems C/C2 gate `weak-interaction-singular-quantum-time-expansion`, and its `a_{D,m}` layer
gates the corollary of `component-recurrence-torus-and-replica-factorization-law`.

Already in the corpus (`HTGeometry/ReplicaCollisionExtremality`): Theorem A
(`finiteSpectralSurvivalFidelity_pow_expansion`,
`finiteSpectralSurvivalFidelityMean_eq_replicaPhaseAverage`,
`symmetricPhaseAverage_tendsto_resonanceIndicator`,
`finiteSpectralSurvivalFidelityMean_tendsto_collisionMass`) and Theorem B
(`fidelityReplicaCollisionMass_floor_le`, `fidelityReplicaResonanceExcess_eq_zero_iff`,
`all_fidelityReplicaCollisionMass_eq_floor_iff`, `forall_replicaRigidAt_iff_maximallyProjectiveEnergy`).

Remaining, with the intended route:

- **C** — assemble from the (now stage-3) chain-genericity law plus Theorem B.  Note the promoted
  chain card is `q = 2`; general `q` needs `ArbitraryGraphLocalHamiltonianGenericityLaw`.
- **C2** — instantiate `AffineLinePolynomialAvoidance` with the obstruction polynomials plus
  `ρ(A) ≤ n(q−1)`.
- **E** `(9)` — uniform-weight specialization of Theorem B.
- **F** `(10)`–`(12)` — the combinatorial limit `a_{D,m} → m!` and moment-determinacy of `Exp(1)`.

`a_{d,m}` does **not** exist in the corpus.  Do not define it through multinomial coefficients:
define it as a pair count, `a d m = #{(X,Y) : (Fin m → Fin d)² | hist X = hist Y} / d^m`, which is
the same object the corpus collision mass already uses.  Then `(11)`–`(12)` split as: injective `X`
contribute `descFactorial d m * m!` (for injective `X` the fibre `{Y : hist Y = hist X}` is exactly
the `m!` rearrangements), and non-injective `X` number at most `C(m,2) d^{m-1}` with fibres at most
`m!`, so their share is `O(1/d)`.  The one real sub-lemma is `hist Y = hist X ↔ ∃ σ, Y = X ∘ σ`.

Moment-determinacy of `Exp(1)` (Carleman) is a separate mathlib gap and is the actual wall for
Theorem F's weak-convergence form; the moment identity `(12)` itself is not.

## Blocked only on another stage-2 card

- `instant-exact-complexity-calibration-singularity-law` — its own theorem `(4)`/`(8)` is
  `HTGeometry.le_lipschitzConstant_of_certificate` and
  `le_mul_lipschitzConstant_of_certificate_of_linear_approach`; `(9)` is
  `penaltyValue_le_wordCost` at the empty word; `(5)`/`(10)` is the corpus Duhamel bound at
  `K = 0`.  Only the application `(7)` is open, and it needs `(6)` — the exponential
  exact-complexity lower bound of `algebraic-two-local-instant-exact-complexity`.  Parent first.

## Cards needing a deep published theorem built from scratch

Each is a formalization project in its own right; the card's own mathematics is otherwise
dependency-closed.

- `route-e-cofactor-amplified-e3-token-supply`, `route-e-forbidden-support-e3-stability` —
  Matomaki-Teravainen all-interval `E3` theorem.
- `mass-bessel-cofinal-radiation-divergence`, `mass-bessel-infinite-radiation-jet-obstruction` —
  uniform sectorial large-argument asymptotics for `K1`; the cards prescribe replacing `K1` by its
  Fourier integral and proving deep-time Laplace asymptotics.
- `local-chain-metric-recurrence-exponents` — Kleinbock-Margulis extremality of analytic
  nondegenerate manifolds.
- `cusp-spectrum-radius-law` — the Selberg class, the standard twist, and Kaczorowski-Perelli
  continuation.  Everything downstream is already `[LEAN-PROVED]`; the card's own reuse audit
  confirms those three inputs are absent from the corpus.
- `route-e-beurling-local-axiom-firewall` — an explicit Diamond-Montgomery-Vorhauer-style Beurling
  system with `N(X) = kX + O(X^t)`, `t < 1`, and zeta zeros off the critical line.
- `algebraic-two-local-instant-exact-complexity` — rational Hilbert specialization and
  transcendence-degree layers above `RHTower/FiniteLindemannWeierstrass.lean`.

## Known deep external dependencies (attack last, expect long builds)

- `route-e-cofactor-amplified-e3-token-supply`, `route-e-forbidden-support-e3-stability` —
  Matomäki–Teräväinen all-interval `E₃` theorem.  Not in mathlib, not in the corpus.
- `mass-bessel-cofinal-radiation-divergence`, `mass-bessel-infinite-radiation-jet-obstruction` —
  uniform sectorial large-argument asymptotics for `K₁` (the card itself prescribes replacing `K₁`
  by its Fourier integral `∫ e^{-ixξ} e^{-t√(ξ²+a²)} dξ` and proving deep-time Laplace asymptotics).
  Corpus owns a Schlaefli-integral Bessel layer (`HTGeometry/BesselOrder*.lean`).
- `local-chain-metric-recurrence-exponents` — Kleinbock–Margulis extremality of analytic
  nondegenerate manifolds (metric Diophantine approximation).  Not in mathlib.
- `algebraic-two-local-instant-exact-complexity` — rational Hilbert specialization and
  transcendence-degree layers above `RHTower/FiniteLindemannWeierstrass.lean`.

## Remaining

Everything still listed by `ls docs/drafts/pipeline/2-fully-proven/*.md`.

## Universal-law-field certification

| Card | New Lean work | Modules |
|---|---|---|
| `positive-doctrine-additive-intervention-nondescendence-and-response-coframe-law` | full derivative, factorization classification, coframe tomography, recurrence/open lift | `HTGeometry/ConstitutivePositiveResponse` |
| `observationally-identical-law-systems-and-intervention-separation-law` | complete passive-reader no-go and injective intervention record | `HTGeometry/ConstitutiveInterventionSeparation` |
| `independent-slot-transitivity-and-cross-organ-nonprediction-law` | dependent finite slot transitivity, empty/full phase, constant invariant | `HTGeometry/ConstitutiveIndependentSlotNoGo` |
| `serial-reconstruction-radius-failure-and-hidden-pair-survivor-law` | three-point rejection of false radius monotonicity; exact pair/diameter survivor | `HTGeometry/ConstitutiveReconstructionNoGo` |

`euler-q-gamma-process-zeta-divisor-translation-law` is not promoted: Lean now certifies its local
q-Pochhammer/q-Gamma probability and integral-response core plus finite exchange, but not its global
prime/zeta/divisor theorem.  See
`docs/drafts/pipeline/2-fully-proven/universal-law-field/_LEAN-CERTIFICATION.md`.
# Universal-law-field adaptive experimental effectivity certification (2026-08-09)

- `adaptive-experimental-procompletion-effectivity-gap-law.md`
  → `3-formalized/universal-law-field/`
- Lean module:
  `GaloisForLFunctions.HTGeometry.ConstitutiveAdaptiveProcompletion`
- Certified: every Boolean profile has finite effective realizations; constant-one profile is
  coherent but not effective; every finite adaptive decision tree is exactly mimicked by an
  effective finite-support law; no finite adaptive effectivity classifier exists.
- Verification: targeted foreground `lake build` green; owned-module checks green; no project
  axioms or computation proofs. Repo-wide lint is currently blocked by unrelated concurrently
  created unwired modules and stale generated indexes.
- Dedicated field umbrella `GaloisForLFunctions.HTGeometry.UniversalLawField` built green.

# Universal-law-field adaptive cost certification (2026-08-09)

- `adaptive-mimic-cost-coercivity-and-infinite-action-boundary-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveAdaptiveCost`.
- Certified: canonical transcript support is contained in every mimic and minimizes every
  nonnegative additive cost; exhaustive all-true experiments have exact minimum support `N`;
  coercive weights force all effective lifts beyond every bounded action sublevel.
- Dedicated field umbrella build green; no project postulates or computation proofs.

# Universal-law-field Gamma response-lifetime certification (2026-08-09)

- `gamma-corona-response-kernel-persistence-and-bockstein-lifetime-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveGammaResponseLifetime`.
- Certified: general exact response-kernel transport; surjective additive fixed-corona Gamma
  semigroup; weighted-ideal/response-kernel identification; monotone kernel persistence and exact total-kernel transport; sharp open Bockstein
  death set; critical survival; `sInf` lifetime `|t|/2`; centered-distance readout.
- Chain-level source coframe conservation and RH remain open.

# Universal-law-field prefix effectivity-horizon certification (2026-08-09)

- `prefix-effectivity-horizon-recurrent-phase-and-open-action-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveEffectivityHorizon`.
- Certified: one prefix-history producer forces stabilized finite observers, pointwise convergence
  to a coherent non-effective boundary, singleton production, exact cardinal action, period-two
  phase, positive erasure, and arbitrarily large action at simultaneous observer/phase returns.
- Dedicated universal-law-field umbrella wired; no project postulates or computation proofs.

# Universal-law-field finite-jet realization-boundary certification (2026-08-09)

- `finite-jet-realization-boundary-and-continuous-classifier-no-go.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveFiniteJetBoundary`.
- Certified: exact DA/HT realization of every finite jet; mutual density; empty interiors;
  nonclosed global strata; no continuous Boolean finite-jet classifier.
- Targeted module build green; universal-law-field umbrella wired; no project postulates or
  computation proofs.

# Universal-law-field locally finite realization-tower certification (2026-08-09)

- `locally-finite-realization-tower-global-section-and-nonproperness-necessity-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveRealizationKonig`.
- Certified: finite roots plus finite one-step extension fibres force a compatible global section;
  nonempty finite realization towers are the exact corollary.
- Targeted module build green; universal-law-field umbrella wired; no project postulates or
  computation proofs.

# Universal-law-field surjective-erasure certification (2026-08-09)

- `surjective-erasure-infinite-dimensionality-and-gamma-bockstein-no-finite-model-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveSurjectiveErasure`.
- Certified: same-carrier surjective erasure forces infinite dimensionality; every genuine
  fixed-corona Gamma-Bockstein death event forces an infinite-dimensional carrier; literal corona
  is not finite-dimensional.
- Targeted module build green; universal-law-field umbrella wired; `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`; no project postulate or computation proof.

# Universal-law-field history-polarization certification (2026-08-09)

- `additive-positive-groupoid-cost-triviality-and-directed-history-necessity-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveHistoryPolarization`.
- Certified: every nonnegative additive groupoid cost vanishes; same for nonnegative real part of
  additive complex groupoid weight; directed natural-number histories carry nonzero additive cost.
- Targeted module build green; universal-law-field umbrella wired; no project postulate or
  computation proof.

# Universal-law-field extension-memory certification (2026-08-09)

- `same-defect-pair-split-nonsplit-extension-and-carry-holonomy-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveExtensionCarry`.
- Certified: exact split and nonsplit events with the same endpoint objects and four-element middle
  size; additive splitting versus nonsplitting; zero versus nonzero binary carry; period-two common
  observation; closed split lift versus nonzero nonsplit kernel holonomy and period-four closure.
- Targeted module build green; universal-law-field umbrella wired; `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`; no project postulate or unresolved theorem premise.

# Universal-law-field observer-unitization pump certification (2026-08-09)

- `observer-unitization-recurrence-open-history-and-cost-nondescendence-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveObserverUnitization`.
- Certified: exact identity observation of all powers; exact linear action; injective lifted power
  history; action cannot descend through unitizing observer; bundled four-organ exchange theorem.
- Targeted module build green; universal-law-field umbrella wired; no project postulate or
  computation proof.

# Universal-law-field process-tomography partial certification (2026-08-09)

- `multilinear-process-tomography-blind-sector-and-positive-robustness-law.md` remains Stage 2.
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveProcessTomography`.
- Certified: exact annihilator blind sector; reconstruction iff spanning; proper instruments iff
  nonzero blind direction; affine record equality; open-interior constraints preserve distinct
  opposite blind perturbations.
- Pending: product-slot dimension formula and quantitative PSD spectral bound/specialization.
- Targeted module build green; universal-law-field umbrella wired; no project postulate or
  computation proof.

# Universal-law-field parity-contextuality certification (2026-08-09)

- `connected-parity-context-proper-face-blindness-and-positive-state-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveParityContextuality`.
- Certified: image of the unsigned `ZMod 2` incidence map of a connected graph is exactly the
  even-charge hyperplane, so a global classical law exists iff the total parity charge vanishes;
  the cokernel is canonically one dimensional and the boundary has rank `|V| − 1`; every proper set
  of contexts is jointly satisfiable for an arbitrary charge, so an odd charge is invisible on
  every proper observer face; each context of degree at least two has `2^(d−1)` local classical
  laws of which `2^(d−2)` fix any prescribed value of any incident observable, so the uniform local
  laws have marginal `1/2` and agree on every shared observable while no global law exists; the
  triangle and the Peres–Mermin skeleton `K(3,3)` are certified instances.
- Targeted module build and universal-law-field umbrella build green; `formal_tools.py lint
  --check-generated` passes; `#print axioms` reports only `propext`, `Classical.choice`, and
  `Quot.sound`; no project postulate, hypothesis interface, or computation proof.

# Universal-law-field irreducible-interaction certification (2026-08-09)

- `irreducible-n-ary-law-proper-face-invisibility-and-unbounded-interaction-spectrum.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveIrreducibleInteraction`.
- Certified: the alternating `N`-ary bracket `det(colours) • z` on `(Fin N → ℝ) × ℝ` has all
  composites identically zero, so every generalized Jacobi identity holds for any sign convention
  and the law is uncurved and minimal; restriction to any colour face with fewer than `N` colours
  is the zero law, while the total law is not abelian and cannot be equivalent to an abelian law;
  its first nonvanishing arity is exactly `N` and is an equivalence invariant; every arity
  truncation below `N` reports an abelian law; the product tower of all blocks squares to zero, an
  arity-`M` observer annihilates every block of order above `M`, the invisible tail is an infinite
  independent family meeting the visible head only at zero, and the full interaction-output space
  `ℕ → ℝ` is not locally compact.
- Reuses the corpus minimal-formal-law layer `NomologicalHomotopyGeometry.MinimalLawLeadingJet`
  (`MinimalLaw`, `MinimalLawEquiv`, `FirstNonzero`, `IsAbelian`) rather than rebuilding it.
- Targeted module build and universal-law-field umbrella build green; `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`; no project postulate, hypothesis interface, or
  computation proof.

# Universal-law-field determinant-torsion certification (2026-08-09)

- `determinant-torsion-exact-history-phase-quotient-and-open-log-lift-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveDeterminantTorsion`.
- Certified: the based two-term complex `C(u)` is acyclic for every nonzero `u` and all such
  complexes have identical (zero) homology; the comparison scalar is the determinant of the
  differential and is multiplicative under orthogonal direct sums; a basis-preserving chain
  isomorphism `C(u) → C(v)` exists iff `u = v`, while unrestricted gauge collapses the entire
  nonzero family, so the source marking is load-bearing; the positive shadow `|τ|²` identifies two
  nonzero histories exactly when they differ by a `U(1)` phase; and the loop `exp(2πiNt)` has
  constantly zero homology, constant positive shadow one, closed determinant history, an open
  logarithmic lift with endpoint increment `2πiN`, and that increment is the logarithmic-derivative
  integral.
- Targeted module build and universal-law-field umbrella build green; `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`; no project postulate, hypothesis interface, or
  computation proof.

# Derived-selection-geometry Cartier-torsion certification (2026-08-09)

- `universal-monodromy-cartier-torsion-fitting-energy-law.md`
  → `3-formalized/derived-selection-geometry/`
- Lean modules: twenty-one under
  `GaloisForLFunctions.HTGeometry.DerivedSelectionGeometry.*` (`IdentityWall`,
  `TwoPathIncompatibility`, `SourceOrientation`, `SourceNormalEquation`,
  `RegularReaderExclusion`, `ReflectionEnergy`, `LocalPort`, `FibreDichotomy`,
  `ExteriorResponse`, `FittingPresentation`, `FittingInvariance`, `FittingEnergy`,
  `TwoTermResolution`, `DerivedFibre`, `QuotientDerived`, `IncompatDerived`, `NormalDefect`,
  `DerivedPullback`, `RiemannPullback`, `SupportSelection`, `NormalCone`).
- Certified: the minimal `T_q`-stable boundary of the two-path defect is the full wall ideal in
  both legs, so the incompatibility module is `(R ⧸ I)²` with annihilator `I` and zeroth Fitting
  ideal `I²`; the literal cyclic source first kills the anti-diagonal and leaves the single
  orientation line `R ⧸ I` with Fitting ideal `I`, whence `Fitt₀(Q) = Fitt₀(Q_src)²`; every map
  from either module into an `I`-torsion-free reader vanishes; the length-one free resolution
  computes `Ext¹(Q,R) ≅ Q`, `Tor₁(Q, R⧸I) ≅ (R⧸I)²`, `Ext¹(Q_src,R) ≅ R⧸I`,
  `Tor₁(Q_src, R⧸I) ≅ R⧸I`, with everything above degree one zero; ordinary specialisation of the
  boundary at the identity is the zero map while its derived specialisation is the full squared
  conormal module and equals `Tor₁`; reflection reverses the conormal class and fixes its square,
  and the reflected energy generates exactly the zeroth Fitting ideal of the two-leg module; the
  rank-`M` port has the same local Cartier support and scales the conormal by `M`; the normal-cone
  algebra is `k[e]` with `σ(e) = -e`, `in_I(K) = 2e`, `in_I(E) = e²`, `in_I(q^M-1) = Me`,
  `in_I(E_M) = M²e²` and `e ≠ 0`; the scalarised exterior response has radical `0 ⊕ ker(ΛS)`, is
  degenerate below `dim W` ports and is never separable; a uniform response on an orthonormal
  family has restricted norm exactly `|c|√N` and is nonclosable; the arithmetic pullback is
  realised by an explicit algebra structure and its derived fibre is nonzero exactly on the
  critical line; and the derived pullback along any `R`-algebra is `Ann_A(u-1)` in degree `-1` and
  `A ⧸ (u-1)` in degree `0`, with `End_R(Q_src) ≅ R ⧸ I` and every construction after passage to
  the quotient inheriting the annihilator, hence localising to zero off the wall.
- New reusable infrastructure absent from mathlib: zeroth Fitting ideals with presentation
  independence; two-term projective resolutions; `Ext`/`Tor` computed from a two-term resolution;
  the associated graded ring of an ideal filtration with its graded multiplication.
- Targeted module builds and the `GaloisForLFunctions.HTGeometry` umbrella build are green;
  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`; no project
  postulate, hypothesis interface, or computation proof.

# Universal-law-field quadratic-filling certification (2026-08-09)

- `quadratic-proof-filling-closed-endpoint-and-open-history-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveQuadraticFilling`.
- Certified: in the free group on two letters the null word `aⁿ bⁿ a⁻ⁿ b⁻ⁿ` lies in the normal
  closure of `[a,b]`, so its class is trivial in the presented group and in `ℤ²`; its reduced word
  has length exactly `4n`; the least number of conjugates of `[a,b]^{±1}` needed to express it —
  the van Kampen area — is exactly `n²`, the upper bound by the explicit `n × n` grid built from
  the two commutator expansion identities and the lower bound by the integer Heisenberg
  representation, in which the relator becomes a central generator and any `k`-cell filling has
  central exponent at most `k` in absolute value; and the area of the reversed word is the same, so
  the unsigned cost forgets orientation.
- New corpus infrastructure: the integer Heisenberg group with its group instance and central
  subgroup, van Kampen fillings/`area` for the free group on two letters, and a
  reduced-word criterion from `List.IsChain`.
- Targeted module build and universal-law-field umbrella build green; `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`; no project postulate, hypothesis interface, or
  computation proof.

# Universal-law-field doctrine-lattice certification (2026-08-09)

- `equivalence-lattice-nondistributivity-finite-recurrence-and-cofinal-lift-reconstruction-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineLattice`.
- Certified: on a three-element source the three point doctrines have pairwise meet the equality
  relation and pairwise join the indiscrete relation, so the lattice of equivalence relations is
  nondistributive; the induced history on `ZMod m` closes after exactly `m` steps and not before;
  a finite family of congruence doctrines has joint period exactly the least common multiple and
  infinite fibres; the cofinal family of all congruence doctrines has intersection the equality
  relation, so it separates points and reconstructs the open lift; the phase doctrine on `ℂˣ` has
  quotient exactly the positive reals and turns the `N`-fold winding loop into a constant history
  while its logarithmic lift stays open.
- Reuses `HTGeometry.ConstitutiveDeterminantTorsion` (`loopHistory`, `logLift`) rather than
  rebuilding the winding loop.
- Targeted module build and universal-law-field umbrella build green; `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`; no project postulate, hypothesis interface, or
  computation proof.

# Universal-law-field endpoint-insufficiency certification (2026-08-09)

- `derived-homotopy-endpoint-insufficiency-for-torsion-and-filling-cost-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveEndpointInsufficiency`.
- Certified: every observer of the based two-term family that sees only its homology is constant,
  while the determinant history separates units, so torsion does not factor through the derived
  category; every observer of words that sees only the represented group element is constant on the
  null words, while the van Kampen area is `n²`; every observer of the grid fillings that sees only
  their Euler characteristic is constant, since all of them have the Euler characteristic one of a
  disk, while their cell counts are `n²`.
- Reuses `HTGeometry.ConstitutiveDeterminantTorsion` (acyclicity, determinant history) and
  `HTGeometry.ConstitutiveQuadraticFilling` (null words, area) rather than rebuilding them.
- Targeted module build and universal-law-field umbrella build green; `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound` (the Euler statements need only `propext`); no
  project postulate, hypothesis interface, or computation proof.

# Universal-law-field bulk-boundary certification (2026-08-09)

- `cyclic-bulk-boundary-character-fusion-recurrence-and-open-lift-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveBulkBoundaryFusion`.
- Certified: the three one-dimensional `C₃` boundary conditions have equal dimension, equal
  one-dimensional endomorphism algebra, and equal positive character norm, are pairwise
  nonisomorphic, and are separated by the bulk character `ω^j`; fusion multiplies characters and
  therefore adds the grade, so the boundary observer is periodic with exact period three, while the
  marked fusion count and its logarithmic lift `2πin/3` are injective and stay open.
- Targeted module build and universal-law-field umbrella build green; `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`; no project postulate, hypothesis interface, or
  computation proof.

# Universal-law-field polyscopic-matching certification (2026-08-09)

- `proper-face-matching-map-four-phase-and-total-law-defect-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutivePolyscopicMatching`.
- Certified in the 0-truncated (set-valued) chart: realizability and uniqueness of a compatible
  proper-face datum are exactly nonemptiness and subsingletonness of the fibre of the matching map;
  the matching map is a bijection iff every compatible proper-face law has a unique total law; the
  reconstructible, contextual, interaction, and mixed phases are exhaustive and pairwise exclusive
  and are invariant under objectwise equivalence of diagrams; in a linear chart the kernel is the
  hidden interaction invisible on every proper face and the cokernel the compatible-looking face
  data not produced by a total law; the amplitude-scaled irreducible `N`-ary law realizes the
  interaction phase natively (every proper colour face stays the zero law, distinct amplitudes give
  distinct total laws) and an odd-charge parity context system realizes the contextual phase (every
  proper observer face satisfiable, total law object empty).
- **Card correction.** Section 4.1's claim that the parity Čech diagram over the subset poset has a
  nonempty proper-face matching object is not certified and appears false: the poset of proper
  subsets contains the maximal faces `V \ {v}`, whose shadows already determine every context
  equation, so the limit over proper faces coincides with the global law object and the naive
  subset diagram lands in the reconstructible phase. The contextual phase is instead certified by
  recording each proper face's satisfiability as its shadow, which is exactly what
  `exists_parityBoundary_eq_on_of_ne_univ` and `properFace_blindness` supply.
- Corollary 2.4 (higher homotopy of the realization space) is out of scope: neither mathlib nor the
  corpus carries infinity-categories. Its zero-truncated content — the realization set and its
  emptiness/multiplicity — is certified.
- Targeted module build and universal-law-field umbrella build green; `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`; no project postulate, hypothesis interface, or
  computation proof.

# Universal-law-field determinant-gluing certification (2026-08-09)

- `determinant-glued-contextual-exact-law-positive-erasure-and-cycle-memory-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveDeterminantGluing`.
- Certified: the determinant sign `paritySign` is an injective character of the parity group, so the
  vertex determinant constraint is exactly the parity incidence equation and the total determinant
  anomaly is exactly the total charge; every glued family has trivial anomaly, so odd charge is a
  literal gluing anomaly; a global exact law exists iff the charge is even iff the anomaly is one;
  when it exists the set of global exact laws is a torsor over the cycle space and has exactly
  `2 ^ (|E| + 1 - |V|)` elements; every local determinant complex is acyclic with positive shadow
  one and every proper observer face is exact for every charge, so those three readings do not see
  the anomaly.
- Reuses `HTGeometry.ConstitutiveParityContextuality` (incidence boundary, criterion, proper-face
  solvability, rank) and `HTGeometry.ConstitutiveDeterminantTorsion` (acyclicity, positive shadow).
- Targeted module build and universal-law-field umbrella build green; `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`; no project postulate, hypothesis interface, or
  computation proof.

# Universal-law-field abelian determinant-flux certification (2026-08-09)

- `abelian-determinant-flux-effectivity-cycle-memory-and-positive-quotient-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveAbelianDeterminantFlux`.
- Certified for an arbitrary abelian coefficient group and an arbitrary oriented finite graph
  (tail and head maps, connectivity as an inductive link relation): `Π ∘ ∂_A = 1`; a vertex law is
  globally realizable iff its total charge is one; hence `range ∂_A = ker Π`, and `Π` is surjective,
  so the four-term sequence `1 → ker ∂_A → A^E → A^V → A → 1` is exact; every nonempty realization
  fibre is a torsor under `ker ∂_A`; every proper observer face is realizable for an arbitrary
  charge, so a nontrivial total anomaly is invisible there; and a coefficient quotient `p` commutes
  with the total charge, so the `P`-observer declares the anomaly trivial exactly on `ker p`.
- Surjectivity onto the kernel is proved by the link-flux construction plus a support induction, not
  by a spanning tree; this is the multiplicative oriented analogue of the walk argument of
  ULF-CTX-1.
- **Not certified:** `ker ∂_A ≅ A^{β₁(G)}` (DF.6, stated in the card "after choosing a cycle
  basis"); mathlib has no spanning-tree cycle basis. The numerical content is certified in the
  `A = F₂` specialization by `ULF-DGLU-1` (`2^(|E| + 1 − |V|)` realizations).
- Targeted module build and universal-law-field umbrella build green; `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`; no project postulate, hypothesis interface, or
  computation proof.

# Universal-law-field Moore-cell certification (2026-08-09)

- `even-moore-law-cell-effectivity-memory-and-positive-topology-collapse-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveMooreLawCell`.
- Certified: over the oriented coefficients, for odd degree every nonzero boundary law has exactly
  one filling, so both law-homology groups are trivial; for even degree a boundary is fillable iff
  it is positive, a positive boundary has exactly the two fillings `±y^{1/n}`, the kernel of the
  boundary on units is exactly `{±1}`, and the cokernel has exactly the two classes `±1`; over the
  positive coefficients every boundary has exactly one filling for every degree, so passing to the
  absolute value simultaneously repairs a nonfillable negative boundary and merges the two oriented
  fillings; consequently the even Moore boundary is neither injective nor surjective on units — the
  mixed phase — while its positive base change has singleton fibres.
- Targeted module build and universal-law-field umbrella build green; `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`; no project postulate, hypothesis interface, or
  computation proof.

# Universal-law-field strict-inversion/Cartier certification (2026-08-09)

- `strict-inversion-cartier-base-change-zero-defect-and-odd-conormal-survivor-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveStrictInversionCartier`.
- Certified over `k[q,q⁻¹]` for an arbitrary commutative ring: Cartier specialization does not see
  the strict inversion (`ε ∘ σ = ε` on every element, by Laurent induction); the exact identity
  `σ(q−1) = −q⁻¹(q−1)`, hence `σ`-stability of `I = (q−1)`; the conormal class is odd, `σ(e) + e`
  lying in `I²`; the inversion-invariant positive displacement `q + q⁻¹ − 2` equals `(q−1)²q⁻¹`, so
  the odd sign disappears after squaring; and every multiplicative radial gain `p^{2a}` is already a
  positive square, so square-root fillability declares every radius trivial and cannot select the
  critical origin.
- **Not certified:** the derived equivalence (IC.4) and the `Tor₁(S,S)` identification (IC.8); both
  are formal consequences of the certified ring-level facts, but the derived-functor layer is not
  constructed in the corpus.
- Targeted module build and universal-law-field umbrella build green; `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`; no project postulate, hypothesis interface, or
  computation proof.

# Universal-law-field metric-phase certification (2026-08-09)

- `metric-phase-exactness-cost-winding-and-cofinal-strictness-law.md`
  → `3-formalized/universal-law-field/`
- Lean modules: `GaloisForLFunctions.HTGeometry.ConstitutiveMetricPhaseExactness` and the new
  reusable `GaloisForLFunctions.HTGeometry.HilbertBlockOperator`.
- Certified — Theorem 1: the determinant amplitude `e^{iφ} sin α`; the Gram law `TᴴT` is
  phase-blind with determinant `sin²α` and eigenvectors `(1,∓1)` of eigenvalues `1 ∓ cos α`, the
  squared singular values; acyclicity for `0 < α ≤ π/2`; Gram phase erasure versus determinant phase
  separation; and the worst filling energy `(1 − cos α)⁻¹`, attained.
- Certified — Theorem 2: exact `2π`-periodicity of the observed law, the logarithmic determinant
  lift, its `2πi` advance per period and winding `N` after `N` periods.
- Certified — Theorem 3: the Hilbert direct sum of the aperture blocks is bounded by `√2`,
  injective, has dense range, is not surjective, has nonclosed range, and both `(1 − cos α_n)⁻¹`
  and the determinant free energy `−∑ log sin α_n` diverge.
- New corpus infrastructure: `HilbertBlockOperator` generalizes the corpus's *scalar* block diagonal
  on `lp K 2` to arbitrary uniformly bounded operator-valued blocks, with injectivity, dense range
  from blockwise surjectivity, and the non-invertibility/nonclosed-range consequences of blocks that
  are not uniformly bounded below.
- Targeted module build and universal-law-field umbrella build green; `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`; no project postulate, hypothesis interface, or
  computation proof.

# Universal-law-field A₂ stability-wall certification (2026-08-09)

- `a2-law-stability-wall-positive-chamber-erasure-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveStabilityWall`.
- Certified: a subrepresentation of `E = (ℂ →id ℂ)` is a pair of subspaces with `U₁ ≤ U₂` and
  there are exactly three, so the unique nonzero proper subobject is `S₂`; in the open upper
  half-plane the phase order is the sign of the cross product, hence `E` is stable iff
  `arg z₂ < arg z₁` and strictly semistable when the two phases agree; on the explicit family
  `z₁ = exp(i(π/2+θ))`, `z₂ = exp(i(π/2−θ))` with `|θ| < π/2` the extension is stable exactly for
  `θ > 0`, while `z₁ + z₂ = 2i cos θ` and the modulus packet `(1, 1, 2|cos θ|)` is identical at `θ`
  and `−θ`, so no rule factoring through the three positive moduli can determine stability.
- The phase-order engine `arg_lt_arg_iff_cross_pos` (with `arg_div_eq_sub`) is new reusable content:
  mathlib has no comparison lemma for `Complex.arg` on the upper half-plane.
- Targeted module build and universal-law-field umbrella build green; `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`; no project postulate, hypothesis interface, or
  computation proof.

# Universal-law-field isotropic intervention-port certification (2026-08-09)

- `isotropic-law-passive-gauge-intervention-port-and-open-projective-history-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveIsotropicInterventionPort`.
- Certified: with the plane modelled as `ℂ` and the source law the standard Gaussian, every
  rotation preserves the law exactly (`Measure.map R_t (stdGaussian ℂ) = stdGaussian ℂ`), so no
  passive statistic, moment or positive quadratic form sees the rotation parameter, and the Gram
  identity `R_t R_t^* = 1` holds; after the marked intervention `do(U₁ = 0)` the response is
  supported on `span(R_t i)`, and two such lines coincide exactly when the parameters differ by an
  integer multiple of `π`; the projective interventional history is therefore `π`-recurrent while
  its angle lift is unbounded; and the orientation-reversing swap has the same passive law and Gram
  operator but determinant `−1`, with its interventional support on the other axis.
- Uses mathlib's `ProbabilityTheory.stdGaussian` and `stdGaussian_map` for the multivariate
  Gaussian and its isometry invariance; no Gaussian theory had to be rebuilt.
- Targeted module build and universal-law-field umbrella build green; `#print axioms` reports only
  `propext`, `Classical.choice`, and `Quot.sound`; no project postulate, hypothesis interface, or
  computation proof.

# Universal-law-field marked-symmetry experiment quotient certification (2026-08-09)

- `marked-symmetry-experiment-quotient-recurrence-and-lift-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveMarkedSymmetryQuotient`.
- Certified: for an arbitrary group action, two transformations have the same marked response
  exactly on a right coset of the stabilizer, and the response descends to a continuous injection of
  `H ⧸ Stab_H(ν)` which is a closed embedding when `H` is compact and the law space Hausdorff; for a
  compact topological group, every continuous one-parameter subgroup returns to every neighbourhood
  of the identity at arbitrarily large times, and meeting the stabilizer gives exact periodicity of
  the marked response; a response loop that is null-homotopic has a closed lift along any covering,
  and along a universal covering the lift closes exactly when the homotopy class is trivial.  The
  exact instantiation is certified concretely: the half-turn subgroup of `SO(2)` is `{±1}`, is `πℤ`
  in the angle coordinate, and is the stabilizer of the marked axis; `Circle ⧸ K ≃* Circle` with the
  squaring map as projection; the half-turn intervention path projects to the once-around response
  loop, whose mathlib path lift along `Circle.exp` ends at `2πn` — distinct deck translations for
  distinct windings — so the response is closed while the lifted history is open, and the response
  loop is therefore not null-homotopic.
- Uses mathlib's covering-space and monodromy layer (`IsCoveringMap.liftPath`,
  `IsQuotientCoveringMap.monodromyPerm_injective`, `Circle.isCoveringMap_exp`) directly; no covering
  theory had to be rebuilt.  The recurrence proof replaces the paper's closure-of-semigroup argument
  by a pigeonhole against a finite subcover, which needs no structure theory of compact groups.
- Targeted module elaboration and universal-law-field umbrella build green with no warnings;
  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`; no project
  postulate, hypothesis interface, or computation proof.

# Universal-law-field equivariant-response blindness certification (2026-08-09)

- `equivariant-intervention-response-blindness-and-transverse-mark-necessity-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveEquivariantResponseBlindness`.
- Certified: on charted spaces over models with corners, an invariant doctrine map satisfies the
  naturality identity `dP_{gx} ∘ g_* = dP_x`, so an equivariant intervention field has a
  `G`-invariant first response and an arbitrary equivariant family has a combined response that is
  literally a function on `MulAction.orbitRel.Quotient G X`; separation of two points of one orbit
  by a first-order coframe forces the doctrine map to be non-invariant, some intervention to be
  non-equivariant, the action to be non-smooth, or the doctrine map to be non-differentiable.
  Non-sufficiency of the escape is certified on one concrete model — the rotation group acting on
  `ℂ` with doctrine `z ↦ z · conj z`: the conjugation field is non-equivariant and separates
  (`−2` against `2`), while the orbit-tangent modulated field `z ↦ (Re z)·i·z` is equally
  non-equivariant and has identically zero response.
- The §2 radial-source instantiation is a **reuse**: `gradeDiag`, `identityTrace`, `kummerCocycle`,
  `radialMultiplier` and their invariance theorems already exist in
  `HTGeometry.ConstraintRelativity.IdentitySectorRadialBlindness`.  The new content is
  `kummerReporter`, its gauge invariance, and `kummerReporter_not_separating`: the whole
  valuation/Kummer reporter coframe is constant on radial orbits, so it can never select the radial
  origin.  `absoluteGrade_zero` derives the normalisation `ν 0 = 1` instead of assuming it.
- Targeted module elaboration and universal-law-field umbrella build green with no warnings;
  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`; no project
  postulate, hypothesis interface, or computation proof.

# Universal-law-field antisymmetric wall-response certification (2026-08-09)

- `a2-positive-wall-antisymmetric-intervention-response-selection-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveAntisymmetricWallResponse`.
- Certified: the A₂ wall family has passive positive packet `(1, 1, 4 cos²θ)`, even in `θ`; the two
  component responses to the intervention `h = 1`, fixed before the wall is observed, are the
  genuine derivatives `d/dε|₀ |z_j + ε|² = 2 Re z_j`, equal to `∓2 sin θ`; the antisymmetric
  response is `Δ(θ) = 4 sin θ`; and on `|θ| < π/2` the extension is stable exactly when `Δ > 0`,
  strictly semistable exactly when `Δ = 0`, and unstable exactly when `Δ < 0`.  The capstone
  `antisymmetric_response_not_factoring` certifies that this response does not descend through the
  positive quotient: the packets at `θ` and `−θ` agree while `Δ` changes sign.
- Reuses `ConstitutiveStabilityWall` (ULF-LSW-1) and `ConstitutivePositiveResponse` verbatim.  New
  content: the real parts of the charges, the derivative form of the responses, the swapped
  cross-product lemma, and the two previously missing legs of the stability trichotomy — unstable
  and strictly semistable.
- Targeted module elaboration and universal-law-field umbrella build green with no warnings;
  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`; no project
  postulate, hypothesis interface, or computation proof.

# Universal-law-field metaplectic action-history certification (2026-08-09)

- `complex-gaussian-fixed-law-positive-erasure-and-metaplectic-history-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveMetaplecticActionHistory`.
- Certified: for `S_θ(z) = ½ e^{iθ} z²` the critical locus is `{0}` for every `θ`, the second
  derivative is the constant `e^{iθ}` whose Gram shadow `conj(H) H` is identically one, the oriented
  line `ι_θ(y) = e^{-iθ/2} y` pulls the action back to `y²/2` with Jacobian `e^{-iθ/2}`, and the
  resulting oriented Gaussian amplitude is exactly `√(2π) e^{-iθ/2}`.  The action, the critical
  locus, the Hessian and the unoriented line are `2π`-periodic; the oriented parametrization and the
  amplitude satisfy `ι_{θ+2π} = −ι_θ` and `Z(θ+2π) = −Z(θ)`, the amplitude is nonzero so the history
  provably does not close at `2π`, and it closes at `4π`.
- The amplitude is defined as the pullback line integral, with `descentLine_hasDerivAt` certifying
  the Jacobian; the Gaussian value comes from mathlib's `integral_gaussian` via
  `integral_complex_ofReal`.  Nothing is posited.
- Scope kept as the card states it: this is a classical Picard–Lefschetz/metaplectic bridge, not
  field core.  No hypertranscendence, arithmetic selection or completion is claimed.
- Targeted module elaboration and universal-law-field umbrella build green with no warnings;
  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

# Universal-law-field Toeplitz defect/index certification (2026-08-09)

- `toeplitz-recurrent-boundary-open-defect-history-and-index-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveToeplitzDefectIndex`.
- Certified on `lp (fun _ : ℕ => ℂ) 2`: the `n`-fold unilateral shift satisfies `S*ⁿSⁿ = 1`; the
  defect `Dₙ = 1 − SⁿS*ⁿ` is exactly the truncation onto the first `n` coordinates, is an
  orthogonal projection, and has an explicit linear isomorphism of its range with `ℂⁿ`, so its rank
  is `n`; the cocycle law `D_{n+r} = Dₙ + Sⁿ D_r S*ⁿ` holds with the two summands annihilating each
  other in both orders; the root-of-unity boundary observer is `m`-periodic and returns to one along
  `n = km` while the defect rank diverges; `ker Sⁿ = ⊥` and `ToeplitzSpace ⧸ range Sⁿ ≅ ℂⁿ`, giving
  index `−n`; the boundary expression `[1 − S*ⁿSⁿ] − [1 − SⁿS*ⁿ]` evaluates to `−rank Dₙ = −n`; and
  for `n > 0` **no invertible operator differs from `Sⁿ` by a compact operator**, hence no unitary
  lift exists.
- The `n`-fold shift is primitive (a coordinate reindexing), so no induction on operator powers is
  needed anywhere.  Clause 8 uses mathlib's Fredholm alternative for compact operators; clause 7 is
  certified computationally because mathlib has no C*-algebra K-theory — `K₀(𝒦)`, the Toeplitz
  extension and the six-term sequence are **not** constructed and are not claimed.
- Targeted module elaboration and universal-law-field umbrella build green with no warnings;
  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

# Universal-law-field balanced-defect zero-index certification (2026-08-09)

- `balanced-defect-zero-index-recurrent-boundary-and-open-history-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveBalancedDefectZeroIndex`.
- Certified on the doubled Hardy space `WithLp 2 (H × H)`: for `Tₙ = Sⁿ ⊕ S*ⁿ` the initial and final
  defects are exactly `0 ⊕ Dₙ` and `Dₙ ⊕ 0`, both of rank `n` (explicit linear isomorphisms of their
  ranges with `range Dₙ`); `ker Tₙ` and `ToeplitzPair ⧸ range Tₙ` are both isomorphic to the
  `n`-dimensional `defectSubmodule n`, so the index vanishes identically; the symbol
  `diag(zⁿ, z⁻ⁿ)` has determinant `1` at every point of the circle and the rank-evaluated signed
  class `[Kₙ] − [Cₙ]` is zero; the unsigned energy is `2n` and diverges along `n = km`, exactly where
  the doubled root-of-unity observer has returned to the identity matrix.
- The §3 abstract cancellation theorem is formalized in full generality: for any additive hom
  `φ : M →+ G`, every diagonal pair lies in `ker δ`, all diagonal pairs share one signed defect, and
  any map applied after `δ` is therefore constant on balanced pairs — so no invariant factoring
  through the signed defect can reconstruct the unsigned energy.
- Reuses `ConstitutiveToeplitzDefectIndex` (ULF-TOEPLITZ-1) verbatim; the shift layer is not
  rebuilt.  As there, the `K₀(𝒦)`/`K₁(C(S¹))` packaging is **not** constructed (mathlib has no
  C*-algebra K-theory) and is not claimed; the certified content is the determinant identity and the
  rank-evaluated class, which is proved equal to the Fredholm index.
- Targeted module elaboration and universal-law-field umbrella build green with no warnings;
  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

# Universal-law-field experimental-dimension certification (2026-08-09)

- `passive-fibre-size-hidden-dimension-and-minimal-experiment-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveExperimentalDimension`.
- Certified: if the joint response of a passive observer and a finite family of experiments is
  injective, then every passive fibre injects into the product of the experimental codomains, so
  `|F_y| ≤ ∏ |Yᵢ| ≤ k^r` and `log_k |F_y| ≤ r`; for linear observers the joint kernel is
  `ker q₀ ⊓ ⨅ ker ℓᵢ`, injectivity forces `r ≥ dim ker q₀` by rank–nullity on the hidden space, and
  exactly `dim ker q₀` extended coordinate functionals achieve it; hence
  `edim q₀ = dim ker q₀` whenever `ker q₀` is finite-dimensional, and no finite budget exists at all
  when it is not — `isExperimentBudget_nonempty_iff` states the dichotomy.
- The finite-information half is proved **without** assuming the state space finite: the injection
  into the finite experimental codomain already forces each fibre to be finite.
- Name note: `jointObserver` was already taken by `ConstitutiveDoctrineLattice`; the linear observer
  here is `linearJointObserver`.  Per-file `lake env lean` does not see umbrella-level collisions.
- Targeted module elaboration and universal-law-field umbrella build green with no warnings;
  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

# Universal-law-field monoid-bialgebra Hopf-envelope certification (2026-08-10)

- `monoid-bialgebra-hopf-envelope-antipode-defect-and-one-sided-representation-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveMonoidBialgebraHopfEnvelope`.
- Certified: `k[t] = AddMonoidAlgebra k ℕ` with the group-like coproduct is a bialgebra whose
  generator is group-like and not a unit, so the antipode identity at the generator is
  contradictory; the Laurent algebra is a Hopf algebra with `S(t) = t⁻¹`; every algebra map from
  `k[t]` into a Hopf algebra sending the generator to a group-like element factors uniquely through
  the Laurent algebra, the factorization composes back to the original map, and every basis image of
  the extension is again group-like; `ℕ → ℤ` is the group completion in its universal form; the
  unilateral-shift representation `ρ(t) = V` does not extend to the Laurent algebra because that
  would make `V` invertible while it is not surjective; for **any** unital algebra map killing the
  Toeplitz defect the images of `V` and `V*` are two-sided inverses and the representation extends
  uniquely; and the erased defect `1 − VV*` is exactly the rank-one projection onto `e₀`.
- Reuses mathlib's `AddMonoidAlgebra`/`LaurentPolynomial` bialgebra and Hopf instances and the
  certified `ConstitutiveToeplitzDefectIndex` shift layer.  Mathlib has no Calkin algebra (compact
  operators are a submodule, not a two-sided ideal with quotient ring), so clause 7 is stated for a
  general defect-killing quotient — strictly stronger than the Calkin case.
- Targeted module elaboration and universal-law-field umbrella build green with no warnings;
  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

# Universal-law-field invariant-positivity/KMS certification (2026-08-10)

- `invariant-positivity-reversibility-wall-and-kms-irreversibility-measure-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveInvariantPositivityKMSWall`.
- Certified: on a compact Hausdorff monoid with an invariant Borel probability of full support every
  left translation is surjective, hence every element is invertible, the monoid carries a group
  structure, and inversion is continuous (via a new closed-graph criterion); an absorbing zero
  collapses the invariant probability to a point mass, so full support is load-bearing.  For an
  isometry with positive energy the KMS exchange identity gives `φ(vⁿw ⁿ) = qⁿ`,
  `φ(1 − vⁿwⁿ) = 1 − qⁿ` and `φ(vⁿ(1 − vw)wⁿ) = (1 − q)qⁿ`, and forces `q = 1` if the image of `v`
  is invertible.  On the universal Toeplitz realization the Gibbs state `∑ₙ (1−q)qⁿ⟨eₙ, · eₙ⟩` is
  normalized, gives `qⁿ` on range projections and `(1−q)qⁿ` on history layers whose masses sum to
  one, kills every off-diagonal monomial, and is faithful.
- New reusable infrastructure: `continuous_of_isClosed_graph` (mathlib has no closed-graph
  criterion), proved by an ultrafilter argument.
- Scope: mathlib has no C*-dynamical systems, KMS states, or Calkin algebra, so §2 is certified from
  the defining equations of the setting and §3 exhibits the state explicitly; the §3 uniqueness
  claim is not formalized as such — its two ingredients are.
- Reuses `ConstitutiveToeplitzDefectIndex` verbatim.  Targeted module elaboration and
  universal-law-field umbrella build green with no warnings; `#print axioms` reports only `propext`,
  `Classical.choice`, and `Quot.sound`.

# Universal-law-field time-reversal likelihood-cocycle certification (2026-08-10)

- `time-reversal-likelihood-cocycle-observer-contraction-and-open-history-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveTimeReversalLikelihoodCocycle`.
- Certified: for a measurable involution `Θ` and a path law `P` equivalent to `Θ_*P`, the
  time-asymmetry variable `Σ = llr P (Θ_*P)` satisfies `Σ∘Θ = −Σ` a.e., `E_P e^{−Σ} = 1`, and
  `E_P Σ = D(P‖Θ_*P) ≥ 0` with equality exactly when the law is reversible; for a reversal-compatible
  observer `q`, `e^{−Σ_q}∘q` is the conditional expectation of `e^{−Σ}`, the divergence contracts
  (`D(q_*P‖q_*Q) ≤ D(P‖Q)`), the gap equals `∫_Y D(P_y‖Q_y) d(q_*P)(y)` for the disintegrations, and
  equality holds exactly when the two disintegrations agree over the observation; and a `±1` path
  with positive drift makes the finite mod-`m` observer return to zero at arbitrarily late times
  while the path escapes and the production rate tends to `(2p−1) log(p/r) > 0`, almost surely, via
  the strong law of large numbers.
- New infrastructure (absent from mathlib): `klDiv` invariance under a measurable embedding; the
  observer graph map as a measurable embedding; the conditional divergence as an integral of
  fibrewise divergences; and, from these plus mathlib's disintegration and chain rule, the
  **data-processing inequality for `klDiv`**.
- Recurrence is proved without Markov-chain theory: a `±1` path with positive drift hits every level
  above its start, and each level is reached only after at least that many steps.
- Targeted module elaboration and universal-law-field umbrella build green with no warnings;
  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

# Universal-law-field polar-amplitude Fisher–phase certification (2026-08-10)

- `projective-amplitude-fisher-phase-and-hidden-history-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutivePolarAmplitudeFisherPhase`.
- Certified: `polarEquiv` is an explicit bijection between projective classes of full-support
  amplitudes and pairs (open probability, relative-phase class), with both round trips proved;
  the Fubini–Study speed of a polar tangent is `(1/4)∑ dpᵢ²/pᵢ + ∑ pᵢ dφᵢ² − (∑ pᵢ dφᵢ)²`, and
  `hasDerivAt_polarAmp` shows the tangent used is the actual derivative of the polar curve; the
  pure-phase loop `ψᵢ(t) = √pᵢ e^{i kᵢ t}` has constant probability observer, closes at `2π`, has
  Fubini–Study speed equal to the weighted variance of the integer velocities, length
  `2π√Var`, Berry connection value `∑ pᵢ kᵢ` and holonomy `exp(2πi ∑ pᵢ kᵢ)`; the length vanishes
  exactly when all velocities agree; and the `N = 2` instance gives length `π` and holonomy `−1`.
  The no-go is certified concretely: `(1,1)` and `(1,−1)` share a probability vector and are not
  proportional.
- Targeted module elaboration and universal-law-field umbrella build green with no warnings;
  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

# Universal-law-field visible-kernel/purification-gauge certification (2026-08-10)

- `hidden-history-elimination-forces-positive-kernel-and-purification-gauge-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveVisibleKernelPurificationGauge`.
- Certified: the visible kernel `K_{bb'} = ∑ₐ Ψ_{ab} conj(Ψ_{ab'})` is positive semidefinite with
  trace `∑|Ψ|²`, has rank equal to the rank of the amplitude matrix, is rank at most one exactly
  when the amplitude is an outer product, and reproduces every visible expectation as a trace;
  the maximally entangled amplitude leaves the maximally mixed kernel `(1/d)·I`, of rank `d`, so for
  `d ≥ 2` it is not a rank-one amplitude; the balanced coherent amplitudes at phases `0` and `π`
  share a diagonal and differ as kernels; every positive semidefinite kernel is a Gram matrix; and
  two Gram factorizations of one kernel have coefficient maps of equal length, hence differ by a
  length-preserving linear equivalence.
- New infrastructure absent from mathlib: `rank_le_one_iff_vecMulVec` (rank ≤ 1 ⟺ outer product)
  and `gaugeEquiv` (two surjective maps of equal length differ by a length-preserving equivalence,
  built from the two first-isomorphism equivalences across an identification of kernels).
- Targeted module elaboration and universal-law-field umbrella build green with no warnings;
  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

# Universal-law-field cyclic-process four-shadow certification (2026-08-10)

- `cyclic-unitary-process-four-shadow-reconstruction-and-withheld-response-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveCyclicProcessFourShadow`.
- Certified: the transfer function of `mₙ = ∑ wⱼλⱼⁿ` is `∑ wⱼ/(1−λⱼz)` on the unit disc; the orbit
  Gram matrices are positive semidefinite with rank exactly `min(N+1, r)`; the moments satisfy the
  order-`r` recurrence of the spectrum polynomial; the Hankel determinant is
  `(det V)²∏wⱼ ≠ 0`; the recurrence coefficients solve the Hankel system; two admissible processes
  agreeing on the first `2r` moments have equal coefficients, equal spectrum polynomials, equal
  weights and equal moments forever; the withheld response `m_{2r}` is `−∑_{k<r} a_k m_{r+k}`; the
  observer recurs at arbitrarily late times; and the marked phase lift escapes.
- New infrastructure absent from mathlib: discrete recurrence of powers in a compact topological
  group (pigeonhole against a finite subcover), and the rank of a rectangular weighted Vandermonde
  matrix via invertible square submatrices.
- Targeted module elaboration and universal-law-field umbrella build green with no warnings;
  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

# Universal-law-field three-realization packet certification (2026-08-10)

- `atomic-differential-operator-three-realization-process-law.md`
  → `3-formalized/universal-law-field/`
- Lean module: `GaloisForLFunctions.HTGeometry.ConstitutiveThreeRealizationPacket`.
- Certified: the response `mₙ = ∑ wⱼλⱼⁿ` of a finite spectral packet with complex nonzero weights
  is simultaneously the `n`-th moment of the atomic measure `∑ wⱼ δ_{λⱼ}`, the `n`-th jet at the
  origin of the exponential polynomial `f(t) = ∑ wⱼ e^{λⱼ t}` (which `p(D)` annihilates at every
  point), the state-space response `cᵀAⁿb`, the unitary orbit correlation `⟨v, Uⁿ v⟩` in the
  positive chamber, and the `n`-th Taylor coefficient of `∑ wⱼ/(1−λⱼz)`; the Hankel window factors
  as `V_Nᵀ diag(w) V_N` with `rank ≤ min(N+1, r)` and `rank = r` once `r ≤ N+1`; the first `2r`
  responses determine the recurrence coefficients, the spectrum polynomial, the weights and every
  later response; and `m_{2r} = −∑_{k<r} a_k m_{r+k}` is predicted before observation.
- Correction: the card's equation (11), `rank H_N = min(N+1, r)`, is false in the unsaturated
  regime `N+1 < r` and is now refuted in Lean — three cube roots of unity with uniform positive
  weight give `m₀ = 1`, `m₁ = m₂ = 0`, hence `rank H₁ = 1 < 2`; with signed weights `m₀` itself can
  vanish.  The Toeplitz/Gram identity `rank G_N = min(N+1, r)` of §5 is unaffected.  §8 of the
  paper card carries the correction.
- New infrastructure absent from mathlib: integrability of an unbounded integrand against a Dirac
  measure, and `det_ne_zero_of_rank_eq_card` (full rank forces nonzero determinant, the converse of
  `Matrix.rank_of_isUnit`).
- Targeted module elaboration and universal-law-field umbrella build green with no warnings;
  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

# Universal-law-field doctrine-memory-spectrum certification (2026-08-10)

- `doctrine-relative-process-memory-spectrum-and-hypertranscendence-law.md`
  → `3-formalized/universal-law-field/`
- Lean modules: `GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineMemorySpectrum`,
  `GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineMemoryWitnesses`.
- Certified: for an analytic germ at the origin, bounded Hankel rank of the response sequence,
  a nonzero constant-coefficient recurrence, a nonzero constant-coefficient linear differential
  equation, and the exponential-polynomial form are all equivalent; finite base-aware linear memory
  (the `ℂ(z)`-span of the jets, cleared of denominators) is exactly a nonzero linear differential
  equation with polynomial coefficients; differential algebraicity is a finite order bound and
  hypertranscendence is algebraic independence of every finite jet over `ℂ(z)`; and the three
  doctrines are strictly separated by `exp(z²)` (infinite Hankel memory, one linear state,
  transcendental with `f' = 2zf`), `tan` (no finite linear memory, transcendental with `f' = 1+f²`)
  and `Γ(z+1)` (no algebraic differential equation of any order).
- New infrastructure absent from mathlib: Kronecker's Hankel-rank theorem with a compactness proof
  of the converse; the entire Taylor extension of a recurrent response; the two transfer lemmas
  between an entire function and its restriction to `ℝ`; `tendsto_eval_div_pow`; and the `ℂ(z)`
  jet-span calculus with closure under differentiation.
- Targeted module elaboration and universal-law-field umbrella build green with no warnings;
  `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

# Universal-law-field q-Gamma process certification (2026-08-10)

- `q-gamma-positive-recurrent-hypertranscendental-process-and-open-history-law.md`
  → `3-formalized/universal-law-field/`
- Lean modules: `GaloisForLFunctions.HTGeometry.QBinomialTheorem`, `…ConstitutiveQGammaProcess`,
  `…QGammaAnalytic`, `…QDigamma`, `…QGammaBellSubstitution`, `…QShiftField`, `…QShiftInverse`,
  `…QIncrement`, `…QIncrementAnalytic`, `…QTranscendence`, `…ShiftEliminationEngine`,
  `…ShiftEigenrelationEngine`, `…QDigammaHypertranscendental`, `…QGammaHypertranscendental`.
- Certified: the complex q-binomial theorem; the positive atomic q-Gamma law and its exponential
  response; the GNS realization with a positive-definite moment matrix and a compact resolvent;
  integer-time recurrence and the open marked lift; the exact tilt/entropy law and both
  Kullback--Leibler derivative values; and **Pastro's q-analogue of Hölder's theorem** —
  `Γ_q` satisfies no algebraic differential equation over `ℂ[z]` on `Re z > 0`.
- New infrastructure absent from mathlib: the two-variable q-shift field `ℂ(z,u)` with its fixed
  field, coboundary obstruction and `u`-degree obstruction; the transcendence of `qᶻ` over `ℂ(z)`;
  the closed form of every jet of the q-digamma shift law; diagonal/rank-one `ℓ²` operators and
  their compactness; and two abstract shift engines (elimination and eigenrelation) that subsume
  the classical `ℂ(z)` Hölder machinery.
- Verification: targeted foreground `lake env lean` on every new module green; universal-law-field
  umbrella build green (11,531 jobs); `#print axioms` on every capstone reports only `propext`,
  `Classical.choice`, `Quot.sound`.  Repo-wide lint is currently blocked only by unrelated
  concurrently created unwired `RHTower` modules and the generated indexes they restale.

# Universal-law-field q-Gamma five-chart certification (2026-08-10)

- `q-gamma-five-chart-reconstruction-and-marked-presentation-rigidity-law.md`
  → `3-formalized/universal-law-field/`
- Lean modules: `GaloisForLFunctions.HTGeometry.QGammaFiveChart`,
  `…MarkedCyclicRigidity`, `…AbsConvergentPowerSeries`, `…QGammaGNSChart`.
- Certified: the atom order and equations (5) and (6); the atomic law as a measure with its
  singleton masses; the identification of its characteristic function with the q-Gamma
  characteristic process and the resulting Fourier reconstruction; the germ chart by analytic
  continuation across the strip carrying the imaginary axis; **Theorem 3.1** — uniqueness of the
  marked unitary equivalence of two cyclic unitary presentations with equal matrix coefficients,
  over an arbitrary group; cyclicity of the q-Gamma GNS source vector; **Corollary 4.1**, the
  five-chart equivalence; and **Corollary 5.1**, invariance of every reconstructed quantity.
- New infrastructure absent from mathlib: diagonal unitaries of `ℓ²`; extension of an isometry from
  a dense subspace of an infinite-dimensional Hilbert space (mathlib's `LinearIsometry.extend` is
  finite-dimensional only); and vanishing of the coefficients of an absolutely convergent power
  series vanishing on the unit circle.
- Verification: targeted foreground `lake env lean` on every new module green; universal-law-field
  umbrella build green (11,541 jobs); `#print axioms` on every capstone reports only `propext`,
  `Classical.choice`, `Quot.sound`.

### ULF-EQG-1 — Euler q-Gamma process, random-integer law, zeta-divisor translation (2026-08-10)

- Moved `euler-q-gamma-process-zeta-divisor-translation-law.md` from `2-fully-proven` to
  `3-formalized` with the companion `-formalized.md`.
- Twenty-two Lean modules; the last two theorems closed in this pass were 7.1 (hypertranscendence
  of the response) and the analytic half of 9.1 (normal convergence, zero-freeness and holomorphy
  of the genus-one renormalised product).
- New reusable infrastructure: reciprocal closure of differential algebraicity, proved by realising
  the substitution `y_j ↦ A_j/g^{j+1}` as a polynomial map and showing it is injective by testing on
  the digamma pair `ψ, 1/ψ` and invoking Hölder's theorem; the domain-local ring and propagation
  calculus for algebraic differential equations; and the genus-one deviation calculus built on the
  corpus's Weierstrass elementary factor estimate.
- Verification: targeted foreground `lake env lean` on every new module green; universal-law-field
  umbrella build green (11,575 jobs); `#print axioms` on every capstone reports only `propext`,
  `Classical.choice`, `Quot.sound`.

### ULF-MPTB-1 — Multilinear process tomography, blind sector, positive robustness (2026-08-10)

- Moved `multilinear-process-tomography-blind-sector-and-positive-robustness-law.md` from
  `2-fully-proven` to `3-formalized` with the companion `-formalized.md`.
- Closed the two clauses the card had left at paper level: equation (7), the product-slot dimension
  formula, and equation (8), the quantitative positive-definite perturbation bound with its
  distinctness and affine/record clauses.
- New reusable infrastructure: `finrank_piTensorProduct` (mathlib has the basis but not the rank),
  `piTensorProduct_map_injective` (slotwise injective maps induce an injective tensor map, via the
  splitting of each slot inclusion over a field), and `exists_uniform_positive` (the least
  eigenvalue as a uniform positivity constant, from compactness of the unit sphere).
- Verification: targeted foreground `lake env lean` on both new modules green; universal-law-field
  umbrella build green (11,577 jobs); `#print axioms` on every capstone reports only `propext`,
  `Classical.choice`, `Quot.sound`.

## ULF-GAS-1 — abelian zeta gas, two-observable divisor dictionary, condensation wall law

- Promoted `2-fully-proven/universal-law-field/` →
  `3-formalized/universal-law-field/abelian-zeta-gas-two-observable-divisor-dictionary-and-condensation-wall-law.md`
  with companion `…-formalized.md`.
- All eight theorems certified unconditionally: 2.1 (zeta-Gibbs measure), 3.1/(GAS.5) (socle
  bridge), Cor. 3.2/(GAS.6)(GAS.7), 4.1 (unique KMS state at every `σ > 0`, in C\*-form), 5.1
  (condensation walls plus the squarefull sector), 6.1/(GAS.9)(GAS.10) (the two divisor calculi and
  the natural boundary at `Re u = −σ`), 7.1/(GAS.11) (renormalisation semigroup, all three clauses),
  8.1/(GAS.12)–(GAS.14) (entropy equals the von Mangoldt mass).
- New reusable infrastructure: partition generating functions in `ℝ≥0∞` (mathlib's Euler proof is in
  `Archive`, not importable); `tprod_split_nat` (finite splitting of a multipliable family in a
  commutative *monoid* — mathlib's version needs a group and `ℂ` is not one under multiplication);
  the monomial monoid of a Toeplitz gas as a restricted sum of bicyclic monoids; a GNS construction
  for a `*`-algebra that is not yet a C\*-algebra (mathlib's `GelfandNaimarkSegal` assumes one), via
  `PreInnerProductSpace.Core` and `UniformSpace.Completion`; and an elementary positivity
  certificate reducing to mathlib's Schur product theorem through the telescoping identity
  `q^{max(b,d)} = q^b q^d q^{-min(b,d)}`.
- Two mathematical simplifications found while formalizing: the natural boundary needs only that
  `ζ` has zeros of unbounded ordinate (the *depths* supply the density, not a Riemann–von Mangoldt
  count), and existence of the KMS state needs no convergence at all because the monomial algebra is
  the algebraic, not the C\*, tensor product.
- Verification: targeted foreground `lake env lean` green on every module; `#print axioms` on every
  capstone reports only `propext`, `Classical.choice`, `Quot.sound`; final foreground
  `lake build GaloisForLFunctions.HTGeometry.UniversalLawField` green at 11,590 jobs.

## FEG-2 — first-entrance gate capacity and discrepancy law

- Promoted `2-fully-proven/first-entrance-gate-capacity-discrepancy-law.md` → `3-formalized/`.
- New reusable infrastructure: `RHTower/ReversibleKilledWalk` packages a finite reversible chain as
  a structure and proves the killed Dirichlet form, both carré-du-champ identities, the spectral
  window `(1-a)‖f‖² ≤ E(f) ≤ (1+a)‖f‖²`, Cauchy--Schwarz for the killed form by discriminant, and
  invertibility of the killed operator by finite-dimensional injective-implies-surjective — so the
  dual negative-energy norm needs no matrix inverse.
- `RHTower/GateCapacityDiscrepancy` transports the parent's discounted entrance mass to real values
  and proves Bellman--Dirichlet, uniqueness, the Dirichlet principle, capacity/charge, `(CM)`,
  `(SM)`, `(CW)`, `(CD0)`, `(CD)`, `(GO)`, `(GS)`, `(DM)`.
- `RHTower/GateInverseWordCapacity` proves the inverse-word conversion with no group structure
  (pulling a tube back along a gate is the tube around the inversely transported target), hence the
  first-hit mass of a moving target is the equilibrium potential of the backward chain, and the
  parent's complete-union law becomes the capacity union bounds.
- Verification: targeted foreground `lake env lean` green on all three modules; `#print axioms` on
  every capstone reports only `propext`, `Classical.choice`, `Quot.sound`.

## GWG-1 — gate-walk Green--Bellman tropicalization law

- Promoted `2-fully-proven/gate-walk-green-bellman-tropicalization-law.md` → `3-formalized/`.
- Theorem A already existed in `HTGeometry/GateWalkGreenBellmanTropicalization` in the
  `approxComplexity` encoding; the new `RHTower/GateWalkGreenBellman` re-proves it in the word-sum
  encoding in `ℝ≥0∞` because Theorems B--D need the sum over words, not over lengths.  Both are
  kept; `wordEval` and the pre-existing `wordAct` are the same `foldr`.
- New: the transfer-operator iterate identity `(4)`, the tropical limit `(8)`, the soft radial
  kernel with its Harnack and Lipschitz laws `(12)`--`(16)`, and the complete-union bound `(17)`.
- Theorem E is added to `HTGeometry/StaticCircuitEnsembleZeroTemperature` as a real-exponent
  `p`-norm sandwich with the one-hot saturation and the entropy--temperature price `(21)`/`(22)`.
- Verification: targeted foreground `lake env lean` green; `#print axioms` on every capstone
  reports only `propext`, `Classical.choice`, `Quot.sound`.

## ARR-1 — autonomous return complexity reflection law

- Promoted `2-fully-proven/autonomous-return-complexity-reflection-law.md` → `3-formalized/`.
- `RHTower/AutonomousReturnReflection` builds the projective Choi distance on unitaries out of the
  corpus `pureStateTraceDistance`, so the triangle inequality is inherited rather than reproved;
  bi-invariance and inversion invariance are trace identities.  Robust complexity is `ℕ∞`-valued, so
  the unreachable case is a genuine infinity and no reachability hypothesis appears anywhere.
- Certified: `(4)`, `(5)`, `(6)`--`(8)`, `(B1)`--`(B6)`.

## Small-card sweep

Four cards whose Lean target was a single interface theorem:

- `cofinal-typed-obstruction-identity-model` → new `HTGeometry/IdentityRationalObstructionModel`;
  the constant rational model's typed obstruction is the number of positive decompositions of the
  weight, acting on the rational line.
- `digamma-gamma-hypertranscendental-near-connector` → already carried by
  `HTGeometry/DigammaGammaHypertranscendentalNear`; verified, wired, axiom-audited, promoted.
- `spectral-character-prescribed-birth-realizability` → new
  `HTGeometry/SpectralCharacterBirthRealizability`; the coordinate jet realizes any prescribed birth
  order exactly for nonzero projective characters.
- `schanuel-stage-one-hermite-lindemann` → already carried by `RHTower/SchanuelStageWitnesses`;
  verified, axiom-audited, promoted.
- `independent-periods-fraction-field-connector` → new
  `HTGeometry/IndepPeriodsFractionFieldConnector`; integral and rational period independence are the
  same interface, and the `i`, `i√2` witness now discharges `IndepPeriods` unconditionally.

## Shared infrastructure: the torus Poincaré inequality

`HTGeometry/UnitTorusPoincare` proves the sharp Poincaré inequality on `UnitAddTorus d` from
mathlib's multivariate Fourier basis.  Mathlib has neither Wirtinger nor any Poincaré inequality, so
this is new corpus mathematics.

The proof avoids both integration by parts and Fubini: translation invariance of Haar gives
`ĉ_n(f(·+a)) = mFourier n a · ĉ_n(f)`, Parseval turns the squared translate difference into
`∑_n |mFourier n a − 1|² |ĉ_n|²`, and dividing by `h²` and letting `h → 0` along a punctured
neighbourhood replaces each weight by `4π² n_j²` — the limit is taken on finite frequency sets, so no
dominated-convergence or a.e.-differentiability argument is needed anywhere.

- `sum_freq_sq_mul_sq_mFourierCoeff_le`: the Fourier form, for every finite frequency set.
- `integral_sq_sub_sq_integral_le`: the variance form `Var(f) ≤ C/(4π²)` from a quadratic bound on
  coordinate translate differences.

Cards that need the product-circle Poincaré law (`low-replica-complete-incidence-influence-law`,
`onset-recurrence-dimension-independence-law`, `cubic-phase-seeded-static-local-full-scale-plateau-law`)
can now consume it; the remaining work there is the a.e.-gradient bound that supplies the hypothesis.

## Shared infrastructure: the gradient of a finite maximum

`HTGeometry/FiniteMaxGradient` proves that wherever a finite maximum of differentiable functions is
differentiable, its derivative equals the derivative of an active member.  The proof needs no
convexity and no uniqueness of the maximizer: the difference `max − X_z` has a local minimum at the
point in every direction, so its directional derivative vanishes.

- `hasFDerivAt_finiteMax_eq`, `exists_fderiv_finiteMax_eq`: the derivative identification.
- `norm_fderiv_finiteMax_le`: a uniform derivative bound passes to the maximum.
- `lipschitzWith_finiteMax`, `abs_finiteMax_sub_finiteMax_le`: the Lipschitz transfer.

This is the missing step behind every card whose observable is a complete-dictionary maximum: the
card proofs say "at almost every differentiability point the gradient lies in the convex hull of the
active gradients", and this module supplies exactly that in the form the estimates use.

## Remaining stage-2 cards: what each still needs

The cards left in `2-fully-proven` all need genuinely new mathematics, not plumbing.  Triage:

- **Torus/variance cluster** (`low-replica-complete-incidence-influence-law`,
  `onset-recurrence-dimension-independence-law`,
  `cubic-phase-seeded-static-local-full-scale-plateau-law`): the two new modules above are the hard
  half.  What remains is the transfer chain — lift a Lipschitz torus observable to a periodic
  function on `ℝ^d`, apply Rademacher, and turn the a.e. gradient bound into the translate-difference
  hypothesis of `integral_sq_sub_sq_integral_le` by dominated convergence.
- **Projective Haar cluster** (`static-ensemble-coverage-time-barrier-law`): needs the Beta law of a
  coordinate of a Haar-random unit vector, i.e. the measure of a projective ball.  Mathlib has the
  sphere measure but not this law.
- **Diamond-norm cluster** (`markovian-return-recovery-complexity-reflection-law`): needs the
  completely bounded norm and the classification of CPTP maps with CPTP inverse.
- **Analytic-number-theory cluster** (`route-e-*`, `route-t-*`): rests on published all-interval
  theorems (Matomäki--Teräväinen) that are not in mathlib.
- **Special-function cluster** (`mass-bessel-*`): needs Bessel `K` asymptotics from scratch.
- **Diophantine cluster** (`local-chain-metric-recurrence-exponents`): rests on Kleinbock--Margulis
  extremality.
- **Operator-ideal cluster** (`determinant-defect-completion-law`): needs Schatten classes and
  regularized determinants.

## Shared infrastructure: gradient bound to variance bound on the torus

`HTGeometry/TorusTranslateDifference` closes the chain from an almost-everywhere gradient bound to
the sharp variance bound.  A Lipschitz torus observable lifts to the vector model, mathlib's
Rademacher theorem gives almost-everywhere differentiability, coordinate translate differences on the
torus equal coordinate difference quotients of the lift on the fundamental box, and dominated
convergence converts the pointwise gradient bound into the quadratic translate hypothesis of
`UnitTorusPoincare`.

- `integral_torus_eq_integral_box`, `integral_translate_diff_eq`: the lift and its integral transfer.
- `tendsto_integral_diffQuotient`: the dominated-convergence step.
- `translate_diff_le_of_ae_fderiv_bound`: the translate hypothesis, with slack.
- `variance_le_of_ae_fderiv_bound`: **`Var(F) ≤ K / (4π²)`** from `∑_j |∂_j F̃|² ≤ K` a.e.

Together with `FiniteMaxGradient` this is the complete analytic engine the torus/variance cluster
needs; what remains per card is the concrete phase-orbit computation of the gradient bound.

## Promoted: low-replica complete-incidence influence law

Complete.  Every boxed statement `(5)`--`(23)` is Lean-certified and the card is in
`3-formalized`.  Two modules closed the last gap:

- `HTGeometry/ReplicaScheduleAsymptotics` — `(6)`--`(10)`: the prescribed-error, logarithmic and
  observation-time replica schedules, and the two asymptotic transfers `(8)`/`(9)` over an arbitrary
  sequence of probability spaces (`Ω : ℕ → Type*`), so no fixed ambient torus is assumed.
- `HTGeometry/ThresholdTransportLightFilter` — `(18)`--`(23)`: the calibrated cutoff `C/ρ²`, the
  two threshold event inclusions, and the two-sided transport of the light-filtered reporter mean to
  the unfiltered incidence probability.

Reusable for the remaining torus/variance cards: `UnitTorusPoincare` (sharp Fourier Poincaré),
`TorusTranslateDifference` (a.e. gradient to variance), `FiniteMaxGradient` (active gradient of a
finite max), `PhaseOrbitGradient` (phase-orbit overlap derivatives, Bessel step, light filter),
`BinomialTail*` and `ReplicaReporterExpectation` (bounded replica reporter and its mean brackets).


## Promoted: local-interaction replica collision extremality

Theorems A and B were already in `HTGeometry/ReplicaCollisionExtremality`.  New this round:

- **E** `(8)`--`(9)` — `HTGeometry/SpectralFormFactorMoments`: `replicaPairCount`, `sffMoment`, the
  identity `sffMoment D m = D^m * fidelityReplicaPermutationFloor (uniform) m`, and
  `normalizedSpectralFormFactorMean_tendsto` (the long-time moment of the normalized spectral form
  factor of a maximally projective spectrum is `a_{D,m}`).
- **F** `(10)`--`(12)` — `HTGeometry/MethodOfMomentsReal` (new reusable engine: factorial moment
  bound → bilateral exponential window → tightness → Prokhorov → moment passage to weak limits →
  `tendsto_of_tendsto_moments`) plus `HTGeometry/SpectralFormFactorExponentialLimit`
  (`integral_torusSFF_pow`, `sffLaw`, `unitExpLaw`, `tendsto_sffLaw_unitExpLaw`).  The determinacy
  input is the corpus's `HTGeometry.measure_eq_of_moments_eq_of_bilateral_exponential_window`.
- **D** `(7)` — `HTGeometry/ProjectivePhaseHaarStatistic`: the anchoring map pushes product Haar to
  product Haar (`map_projectiveTorusMap_haar`) and the sampled phase law to the relative phase law,
  the survival amplitude modulus is diagonal-invariant, and
  `tendsto_timeAverage_fidelityStatistic` is the card's boxed independent-phase time law.
- **C** `(6)` — `HTGeometry/GenericLocalCollisionExtremality`: membership in the canonical
  maximal-rank locus *is* maximal projective rationality
  (`maximallyProjective_of_mem_realAffineHermitianMaximalSet`), so
  `exists_quditPath_generic_collisionFloor` and `exists_quditPath_generic_survivalFidelityFloor`
  give the dense/residual/full-measure statement for every positive weight and every replica order.

C2 is done too: `BlockAffineLineAvoidance` (one-knob lines through a coordinate splitting; the
merge at line parameter one is a measure-preserving equivalence, so the bad set is null),
`OneKnobProjectiveActivation` and `OneKnobOnsiteActivation` (the same Encodable obstruction
enumeration as the corpus's genericity theorem, fed to the line-avoidance lemma), and
`SeparableSpectrumRankBound` (`anchoredTemporalRank_le_of_separable`, `separable_rank_lt`).  The
card is in `3-formalized`.

Reusable beyond this card: `MethodOfMomentsReal` (method of moments on ℝ, including tightness and
Prokhorov), `BlockAffineLineAvoidance`, `SeparableSpectrumRankBound`,
`ProjectivePhaseHaarStatistic` (anchoring pushes Haar to Haar).

## Promoted: static ensembles obey a parameter--time--coverage barrier

Theorem A is done: `HTGeometry/ParameterCoverageBarrier` has `coveringNumber`,
`card_le_of_separated` (a `δ`-separated subset of a Euclidean `R`-ball has
`card · (δ/2)^m ≤ (R+δ/2)^m`, by disjoint balls), `exists_separated_net` (a maximal separated
subset exists and is a net, by `Nat.sSup_mem` on the bounded cardinality set), and
`exists_cover_card_le` — the card's `(1)`, with the `L = 0` and `K = ∅` cases handled separately.

Theorem C `(8)` is then Duhamel plus Cauchy–Schwarz plus Theorem A and B; the corollary `(13)` is
arithmetic.  Both are short once B is available.

Theorem B `(4)` is **done**: `HTGeometry/ProjectiveBallVolume` proves
`volume_projectiveBallCone` — for every unit centre `φ` and every `0 < r < 1`,
`volume {x | ‖x‖² ≤ 1 ∧ ‖x‖² − |⟪φ,x⟫|² ≤ r²‖x‖²} = r^{2n} · volume {x | ‖x‖² ≤ 1}` in
`Fin (n+1) → ℂ` — and `one_le_card_mul_pow`, the card's `(5)`.  The route that was carried out:

1. Work in `Fin D → ℂ` with the pi Lebesgue measure (an additive Haar measure on a `2D`-dimensional
   real space) and write every set with explicit sums: `sqNorm x = ∑ i, ‖x i‖^2`, the unit ball
   `{x | sqNorm x ≤ 1}`, and the cone `{x | sqNorm x - ‖∑ i, conj (φ i) * x i‖^2 ≤ r^2 * sqNorm x}`.
   The projective-ball Haar probability is the normalized cone-in-ball volume — this is exactly
   mathlib's `Measure.toSphere` normalization (`toSphere_apply'`), so no sphere measure is needed.
2. Unitary invariance: a matrix with `Uᴴ * U = 1` has `|det_ℂ U| = 1`, so by
   `LinearMap.det_restrictScalars` (`det_ℝ = Algebra.norm ℝ (det_ℂ) = |det_ℂ|²`) its real
   determinant is one, and `Measure.addHaar_preimage_linearMap` gives volume invariance.  Any unit
   `φ` is the first column of such a `U`, which reduces `(4)` to the centre `e₀`.
3. At `e₀` the cone is `{x | ‖x 0‖^2 ≥ s · sqNorm x}` with `s = 1 - r^2`.  Split off coordinate `0`
   with `volume_preserving_piFinSuccAbove`, use `Measure.addHaar_smul` for the volume of the
   `(D-1)`-dimensional ball of radius `min (c‖x 0‖) √(1 - ‖x 0‖²)` (`c = √((1-s)/s)`), then
   `Complex.integral_comp_polarCoord_symm` in the remaining plane.  The two elementary integrals
   `∫_0^{√s} c^{2D-2} a^{2D-1}` and `∫_{√s}^1 (1-a²)^{D-1} a` sum to `(1-s)^{D-1}/(2D)`, giving the
   ratio `(1-s)^{D-1} = r^{2D-2}`.
4. `(5)` follows without any sphere measure: a cover of the sphere by `q` balls of radius `r` gives
   a cover of the unit ball by the corresponding cones, so `1 ≤ q · r^{2D-2}`.

### Complete

All six mathematical boxed statements are Lean-certified and the card is in `3-formalized`:
`(1)` `exists_cover_card_le`, `(2)` `le_lipschitz_of_covering`, `(4)` `volume_projectiveBallCone`,
`(5)` `one_le_card_mul_pow`, `(8)` `coverage_time_lower_bound`, `(13)` `coverage_time_exponential`.
The Duhamel step `(9)` reuses the corpus's `QuantumAlg.norm_unitaryEvolution_mulVec_sub_le`; the
coefficient Cauchy--Schwarz `(10)` is `norm_generatorCombination_sub_le`.

Reusable beyond this card: `ParameterCoverageBarrier` (separated-net volume bound, covering
numbers, the root-form Lipschitz lower bound) and `ProjectiveBallVolume` (uniform measure of a
projective ball at every centre, unitary invariance of the pi Lebesgue measure, plane polar
reduction of a radial lintegral).

## In flight: quenched causal replica-action law

New reusable engine, axiom-clean:

- `HTGeometry/GibbsVariationalPrinciple` — the Donsker–Varadhan/Gibbs duality on any probability
  space, which mathlib does not have.  `llr_tilted_right` shifts the log-likelihood ratio against a
  tilted measure by the potential and the log partition function; `neg_log_integral_exp_le_gibbsAction`
  is the lower bound (via `InformationTheory.integral_llr_add_sub_measure_univ_nonneg`);
  `gibbsAction_tilted` and `isLeast_gibbsAction` give the exact infimum, attained at the tilted law.
- `HTGeometry/QuenchedReplicaAction` — `quenchedReplicaMass ρ F r = ∫ F^r`, its Laplace-transform
  form `(3)`, monotonicity `(15)`, the discount bound `(6)`/`(18c)`
  (`measureReal_le_quenchedReplicaMass`), the rare-carrier lower bound `(17)`
  (`quenchedReplicaMass_ge_of_carrier`), and the card's Theorem B `(8)`/`(9)`
  (`isLeast_quenchedReplicaAction`).

The card's parent is already formalized (`RHTower/CircuitCausalAccessibility`:
`causalAccessibility`, `preparationAction`, `pow_le_causalAccessibility`), so `(6)` instantiates
directly.  Remaining for the card: the product-incidence identity `(5)` (Fubini for `ρ ⊗ π_z^{⊗r}`
against the causal success event), the soft-reporter form `(7)`, the event-projection form `(10)`,
the certificate criterion `(12)`/`(14)`, and the `L^p`-limit statements `(16)`/`(18b)`
(`lim Z_r^{1/r} = ‖F‖_∞`), which need an `essSup` layer.

## Promoted: quenched causal replica-action law (2026-08-15)

`quenched-causal-replica-action-law` moved to `3-formalized`.  All proved statements of the card,
`(2)`--`(23)`, are closed unconditionally in Lean 4 with axiom set
`[propext, Classical.choice, Quot.sound]`; `(24)`--`(25)` are the card's open core and carry no
formal obligation.

New modules:

- `HTGeometry/GibbsVariationalPrinciple.lean` — Gibbs/Donsker--Varadhan duality (extended with
  `rnDeriv_tilted_quenched`, `integral_llr_tilted_quenched` in `QuenchedReplicaAction`).
- `HTGeometry/ConditionalInformationProjection.lean` — least relative entropy over laws carried by
  an event equals the negative logarithm of the event mass, attained by the conditioned law.
- `HTGeometry/PowerMeanEssSupLimit.lean` — power means increase with the exponent and converge to
  the essential supremum on a probability space.
- `HTGeometry/QuenchedReplicaLimits.lean` — log-convexity, normalized replica action, its
  monotonicity and limit, rare-carrier amortization, schedule ceiling, certificate criterion.
- `RHTower/CircuitTraceLaw.lean` — the Boltzmann law of circuit heaps as a probability measure.
- `RHTower/QuenchedCausalReplicaIncidence.lean` — Fubini product-incidence identity `(5)`, the
  complete-circuit bound `(6)`, its certificate-exponent form `(18c)`, and the soft-reporter
  form `(7)` with its `r/δ` Lipschitz constant.
- `RHTower/QuenchedCausalRecurrenceExtraction.lean` — Theorem D, `(20)`--`(23)`.

Reused from mathlib rather than rebuilt: `Measure.tilted`, `llr`, `llr_tilted_right`,
`integral_llr_tilted_right`, `rnDeriv_tilted_left_self`, `InformationTheory.klDiv` nonnegativity,
`ProbabilityTheory.cond`, `Measure.pi_pi`, `Measure.prod_apply`,
`integral_mul_le_Lp_mul_Lq_of_nonneg`, `essSup`/`essInf`.

42 cards remain in `2-fully-proven` (top level).

## In flight: fixed-time phase-graph Sobolev blindness law (2026-08-15)

Target: `docs/drafts/pipeline/2-fully-proven/fixed-time-phase-graph-sobolev-blindness-law.md`.

Formalization design (unit torus model; the card's `2π` period is a normalization, and
normalized Haar makes the period irrelevant):

- phase space `UnitAddTorus (Fin D)` with `volume` (needs the three `local instance`s
  `MeasureSpace`/`IsAddHaarMeasure`/`IsProbabilityMeasure` on `UnitAddCircle`, as in
  `HTGeometry/TorusTranslateDifference.lean`);
- lift to `Fin D → ℝ` via `torusProj`, integrals via `integral_torus_eq_integral_box`;
- `∂^α_φ` defined on the lift by iterated `fun x => fderiv ℝ G x (Pi.single i 1)`;
- the counterexample family is a **Fejér-type trigonometric polynomial**, not a compactly
  supported bump: `h_N(t) = (N+1)^{-2} |∑_{m≤N} e^{2πimt}|²` has Fourier coefficients
  `b_m = (1-|m|/(N+1))/(N+1)` on `|m| ≤ N`, satisfies `h_N(0)=1`, `0 ≤ h_N ≤ 1`, is a
  trigonometric polynomial (so smooth and periodic for free, no periodization needed), and
  `∑_m m^{2k} b_m² ≤ (2N+1)N^{2k}/(N+1)² ≍ N^{2k-1} = ε^{1-2k}` with `ε = 1/(N+1)`;
- `g_N(φ) = ∏_i h_N(φ_i)`, `F_N(ω,φ) = g_N(φ - Φ(ω))`; all torus integrals of `|∂^α|²` are
  Parseval sums over the (finite) coefficient support, and translation by `Φ(ω)` only multiplies
  each coefficient by a unit modulus, so `E_comp` and every Sobolev quantity are `Φ`-independent.

Remaining: Theorem A `(5)`--`(7)`, Corollary A.1 `(12)`, Theorem B `(13)`--`(14)`,
Corollary B.1 `(16)`.  Theorem C `(21)`--`(25)` should reuse
`HTGeometry/ParameterCoverageBarrier.lean` (`exists_cover_card_le`, `exists_image_net_card_le`)
and `HTGeometry/StaticEnsembleCoverageBarrier.lean` (`norm_generatorCombination_sub_le`,
`log_orbit_net_card_quadratic`) — check those first.

## Promoted: fixed-time phase-graph Sobolev blindness law (2026-08-15)

`fixed-time-phase-graph-sobolev-blindness-law` moved to `3-formalized`.  Theorems A, B, C and all
corollaries are closed unconditionally in Lean 4 with axiom set
`[propext, Classical.choice, Quot.sound]`.

Design note (supersedes the in-flight entry above): the counterexample family is realized as a
**trigonometric detector** — `phaseDetector N a x = ‖∑_{J ∈ [0,N]^d} e(⟨J, x-a⟩)‖² / ((N+1)^d)²` —
rather than a scaled compactly supported bump.  Being a trigonometric polynomial it is periodic and
analytic with no periodization step, and all completed quantities are Parseval sums over difference
frequencies.  Every needed bound follows from *crude counting*: a difference frequency together with
three of the four box indices determines the fourth, so the number of coincident pairs is at most
`((N+1)^d)^3`, which gives `∫‖∂^α F‖² ≤ (2πN)^{2|α|}/(N+1)^d` — exactly `ε^{d-2|α|}` with
`ε = 1/(N+1)`.  No binomial asymptotics, no Fejér positivity identity, no bump scaling lemma.

New modules: `HTGeometry/TorusPhaseTrigCalculus.lean`, `HTGeometry/PhaseGraphDetector.lean`,
`HTGeometry/PhaseGraphSobolevBlindness.lean`.

Theorem C `(19)`--`(25)` needed no new work: `HTGeometry/ParameterCoverageBarrier.lean` and
`HTGeometry/StaticEnsembleCoverageBarrier.lean` (built earlier for
`static-ensemble-coverage-time-barrier-law`) already contain `exists_orbit_net_card_le`,
`norm_generatorCombination_sub_le`, `traceDist_evolvedSeed_le`, `log_orbit_net_card_le` and
`log_orbit_net_card_quadratic`.

41 cards remain in `2-fully-proven` (top level).

## Promoted: instant exact-complexity calibration singularity law (2026-08-15)

`instant-exact-complexity-calibration-singularity-law` moved to `3-formalized`.  Every statement of
the card is closed unconditionally in Lean 4 with axiom set
`[propext, Classical.choice, Quot.sound]`.

New module: `HTGeometry/InstantCalibrationSingularity.lean` — the quotient form of the certificate
condition number `(4)`, the exact-penalty form `(9)` via the empty gate word, the Duhamel
displacement `(5)`/`(10)` (`unitaryEvolution 0 t = 1` plus the corpus two-generator bound), the
instant-jump instantiation `(7)`, and the uniform-divergence statement.

Most of `(4)`/`(8)` was already in `HTGeometry/ExactPenaltyCircuitBellman.lean`
(`le_lipschitzConstant_of_certificate`,
`le_mul_lipschitzConstant_of_certificate_of_linear_approach`) — check that module first for any
Bellman/circuit-certificate card.

Note on `(6)`: the exponential exact-complexity bound is the parent card
`algebraic-two-local-instant-exact-complexity.md` and is *not* used in any proof here; `(7)` is
stated at the value `(2^n-1)/16` so the parent plugs in verbatim once formalized.

Stage 2 now holds 41 cards: 40 of the original 43 minus the three promoted, plus
`baker-general-logarithms-inhomogeneous-extension.md`, added concurrently by another agent.

## In flight: local-Clifford return-excised phase-incidence law (2026-08-15)

Target: `docs/drafts/pipeline/2-fully-proven/local-clifford-return-excised-phase-incidence-law.md`.

**Already built and axiom-clean** (`HTGeometry/TorusReplicaMomentBound.lean`, wired):

- `occupationSet d r`, `occupationWeight r α = r!/∏(α_j)!`, `occupationFreq α = (α_j : ℤ)` and its
  injectivity;
- `replicaPairing p r w x` — the card's `(11)`, the pairing of `Φ_L(ζ)^{⊗r}` with a replica tensor
  in the occupation basis, realized as a `trigLift` over `occupationSet`;
- `integral_box_normSq_replicaPairing` — the card's exact identity `(12)`, obtained from
  `integral_box_normSq_trigLift_of_injOn` (new in `TorusPhaseTrigCalculus`: Parseval at pairwise
  distinct frequencies);
- `integral_box_normSq_replicaPairing_le` — the card's `(13)`, `∫|⟨Φ_L^{⊗r},w⟩|² ≤ r! τ^r ‖w‖²`;
- `occupationCollision`, `heavySector`, `lightWeights`, `sum_heavySector_le` — the card's `(6)`,
  `(9)` heavy-sector mass bound.

Working with the *occupation basis* (multi-indices α with `Σα_j = r`) rather than tuples
`Fin r → D` is what makes this cheap: the `r!/α!` normalization appears as a coefficient, so the
bound needs only `α! ≥ 1`, and no count of tuples with a given occupation (hence no
multinomial-cardinality lemma, no permutation argument).

**Remaining for the card:**

1. `(7)`/`(10)` — `‖Φ_A‖² ≤ a/4` from `sum_heavySector_le` with `τ = 4C_H/a`, and the transfer
   `|⟨Φ_H,z⟩|² ≥ a ⟹ |⟨Φ_L,z⟩|² ≥ a/4` by the triangle inequality.
2. `(14)`--`(19)` — the projection/design assembly.  **Do not rebuild the optimal design:**
   `HTGeometry/ReturnExcisedOptimalDesignCoareaLaw.lean` already has
   `exists_finiteOptimalDesign_pointwise` (the D/G-optimal design law `(16)`),
   `exists_replicaTarget_optimalDesign_pointwise`, and
   `measure_completeTargetCapture_le_optimalDesignMoments` (a return-excised capture bound of
   exactly the shape of `(5)`).
3. Section "Ordinary bounded-degree static-local ensemble" `(20)`--`(24)` — Gaussian ensemble,
   product-Clifford transitivity, `E_H C_H(Ω) ≤ (2/3)^n`, a.e. simple spectrum and maximal
   projective rational spectral rank.  This is the heavy half.

`HTGeometry/TorusReplicaMomentBound.lean` is expected to serve the other replica cards
(`all-replica-*`, `cubic-phase-seeded-*`, `stabilizer-seeded-*`,
`fixed-shell-angular-dephasing-*`) as well.

### Update: `(13)` closed in the corpus fidelity form (2026-08-15)

`HTGeometry/TorusReplicaMomentBound.lean` now also contains, all axiom-clean:

- `charLift_pow`, `charLift_prod_index` (new in `TorusPhaseTrigCalculus`);
- `phaseOrbit p x j = √(p j) · e(x_j)` — the card's `Φ_H` / `Φ_L`;
- `occupationSet_eq_piAntidiag`, `multinomial_le_factorial_of_mem`;
- `finiteComplexInner_phaseOrbit`, `inner_phaseOrbit_pow` — the multinomial expansion of
  `⟨Φ(x), z⟩^r` as a character combination over occupation multi-indices (mathlib's
  `Finset.sum_pow_eq_sum_piAntidiag`);
- **`integral_box_fidelity_pow_le`** — the card's `(13)` in exactly the shape that
  `HTGeometry/ReturnExcisedOptimalDesignCoareaLaw.lean` consumes:

  `∫_{box} finitePureStateFidelity (phaseOrbit p x) z ^ r ≤ r! · τ^r`

  whenever `0 ≤ p j ≤ τ` for all `j` and `∑ ‖z j‖² ≤ 1`.

So the abstract theorem `(5)` now needs only the heavy-sector transfer `(7)`/`(10)` and the
assembly with `measure_completeTargetCapture_le_optimalDesignMoments`.

### Update: the abstract theorem `(5)` is closed with the *sharp* carrier constant (2026-08-15)

Two new modules, both axiom-clean and wired:

- `HTGeometry/SubspaceOptimalDesign.lean`
  - `exists_optimalDesign_coord` — the corpus coordinate design law at every positive dimension;
  - `exists_optimalDesign_of_span_top` — the same law in an arbitrary finite-dimensional complex
    inner-product space, transported along `(stdOrthonormalBasis ℂ E).repr`;
  - `exists_optimalDesign_of_span_eq` — ambient form for a family spanning a submodule, with the
    *submodule* dimension as the factor;
  - `incidenceCarrier S g A = span {P_S (g x) : x ∈ A}`, `incidenceCarrier_le`,
    `starProjection_of_le`, `starProjection_incidenceCarrier_eq` (the card's `(14)`),
    `inner_incidenceCarrier_target` (the card's `(15)`),
    `span_starProjection_incidenceCarrier`.
- `HTGeometry/ReturnExcisedPhaseIncidenceLaw.lean`
  - regularity of the phase-orbit fidelity (continuity, unit bound, integrability on the box);
  - `measureReal_capture_le_return_add_replicaMoment` — `(5)` with the ambient constant `h_r(Z)`;
  - **`phaseIncidenceCarrier`** and **`measureReal_capture_le_return_add_carrierMoment`** — the
    card's boxed `(5)` with the sharp constant `ι^L_{r,R}(Z) = finrank(phaseIncidenceCarrier …)`,
    together with `phaseIncidenceCarrier_le` for `(8a)`.

So `(6)`--`(19)` of `local-clifford-return-excised-phase-incidence-law` are all Lean-certified.
**Remaining for that card:** only section "Ordinary bounded-degree static-local ensemble",
`(20)`--`(24)`: the Gaussian coefficient ensemble, product-Clifford transitivity,
`E_H C_H(Ω) ≤ (2/3)^n`, and almost-sure simple spectrum with maximal projective rational spectral
rank.

### Update: the local-Clifford collision estimate `(24)`--`(25)` is closed (2026-08-15)

New module `HTGeometry/StabilizerTwoDesign.lean` (wired, axiom-clean):

- `stabAmp s` — the six single-qubit stabilizer amplitudes in terms of `s = 1/√2`;
- **`sum_stabAmp_four`** — the card's `(24)`, the single-qubit two-design identity
  `∑_t ψ_t(x)ψ_t(u)conj(ψ_t(y))conj(ψ_t(v)) = δ_{xy}δ_{uv} + δ_{xv}δ_{uy}`,
  proved by the sixteen index cases with `s^4 = 1/4` and `I^2 = -1`;
- `prodStabAmp`, `mixOn`, `mixSwap`, `mixOn_involutive`, `mixSwap_involutive`;
- `sum_prodStabAmp_kernel` — the `n`-qubit fourth-moment kernel as a product over qubits
  (`Finset.prod_univ_sum`);
- `prod_delta_eq` — the delta product collapses to the indicator of `q = mixSwap A p`;
- `norm_mix_term_le` — each subset term is at most `(∑‖e‖²)²`, by Cauchy--Schwarz on pairs
  **plus the mixing involution** (no splitting of the index set into `A` and its complement, which
  is what makes this cheap);
- **`sum_prodStab_fourth_le`** — the card's `(25)`:
  `∑_{σ ∈ (Fin 6)^n} |⟨e, φ_σ⟩|⁴ ≤ 2^n (∑_b ‖e b‖²)²`, i.e. the normalized average is `≤ 3^{-n}`;
- `sum_collision_le` — summing over an orthonormal family: `∑_σ ∑_j |⟨e_j,φ_σ⟩|⁴ ≤ |D| · 2^n`,
  which at `|D| = 2^n` is the card's `4^n`, i.e. average collision `≤ (2/3)^n`.

**Still remaining for `local-clifford-return-excised-phase-incidence-law`:** `(23)` (invariance of
the Gaussian coefficient law under product-Clifford conjugation, hence equality of
`E_H C_H(φ)` across the `6^n` product stabilizer inputs), `(26)` and `(21)` (Markov), `(27)` (the
Krylov determinant genericity and the nearest-neighbour spectral-maximality theorem), and the
physical-time and complete-circuit consequences `(28)`--`(33)`.

## In flight: weak-cut complexity onset/capacity separation law (2026-08-15)

Target: `docs/drafts/pipeline/2-fully-proven/weak-cut-complexity-onset-capacity-separation-law.md`.

**Theorem A is closed** — new module `HTGeometry/WeakCutOnsetDelay.lean` (wired, axiom-clean):

- `approxComplexity_le_of_near` — approximation transfer: a state within `δ₁` of a state
  synthesizable to `δ₂` by `s` gates has `approxComplexity ≤ s` at every resolution `≥ δ₁ + δ₂`;
- `dist_evolvedState_sub_le` — the card's `(7)`, Duhamel separation of two Schrödinger orbits of
  the same unit seed at rate `‖H − K‖`;
- `approxComplexity_evolvedState_le_synthesis` — the card's boxed `(4)`;
- `lt_abs_time_of_lt_approxComplexity` — the card's boxed `(6)`, the onset lower bound
  `T_full ≥ (ε − η_A − η_B)/‖V‖`.

As in the card, the split-system synthesis cap `S_k(η)` enters as a hypothesis (`hsyn`): the card
itself says "only finiteness of `S_k(η)` is needed".  What is *not* yet formalized from Theorem A's
proof is the decoupled factorization `(8)`
`e^{-itH₀}(χ_A⊗χ_B) = (e^{-itH_A}χ_A)⊗(e^{-itH_B}χ_B)` and the disjoint-circuit concatenation that
produces `hsyn` with `S = S_A + S_B` and `η = η_A + η_B`; those need the bipartite tensor model
(`finiteLocalMatrix` / `qubitLocalTensor` in the corpus) and `NormedSpace.exp_add_of_commute`.

**Remaining:** Theorem B `(9)`--`(12)` (the Steinhaus/cubic-phase fourth-moment bound
`E ∑_j |⟨e_j, χ_A⊗χ_B⟩|⁴ ≤ 4/D`) and Theorem C `(13)`--`(14)` (conull loci, positive-measure seed
selection, equidistribution, plateau).

Note for Theorem B: the required core is
`∫_{box} ‖∑_y c_y e(x_y)‖⁴ ≤ 2 (∑_y ‖c_y‖²)²`, which is Parseval over the frequencies
`Pi.single y 1 + Pi.single y' 1` — use `ofReal_integral_box_normSq_trigLift` from
`HTGeometry/TorusPhaseTrigCalculus.lean`, exactly as in `TorusReplicaMomentBound`.  Independent
uniform phases are realized as `charLift (Pi.single y 1)` on the torus box, so no new probability
space is needed.

### Update: the Steinhaus fourth-moment core of Theorem B is closed (2026-08-15)

New module `HTGeometry/SteinhausFourthMoment.lean` (wired, axiom-clean):

- `pairFreq p = Pi.single p.1 1 + Pi.single p.2 1` and `pairFreq_eq_iff` — a pair frequency
  determines the *unordered* pair, so every frequency is carried by at most two ordered pairs;
- **`integral_box_phase_fourth_le`** — the Steinhaus fourth moment
  `∫_{box} ‖∑_y c_y e(x_y)‖⁴ ≤ 2 (∑_y ‖c_y‖²)²`, which is the card's `(11)` with `q(a)` factored
  out.

Independent uniform coordinate phases are realized as `charLift (Pi.single y 1)` on the torus box,
so this needs no separate probability space; the proof is `ofReal_integral_box_normSq_trigLift`
applied to the pair-frequency expansion of the square.

Remaining for Theorem B: the bipartite reduction `(10)`, the second pairing `(12)`
(`E_a q(a)² ≤ 2/d_A²`, which is the same lemma applied on the `A` factor to the row norms of `e`),
the assembly to `(9)` `E ∑_j |⟨e_j, χ_A⊗χ_B⟩|⁴ ≤ 4/D`, and the transfer from Steinhaus phases to
four-wise-independent cubic-phase seeds.

### Update: bipartite product phase seeds and the torus spectral gap (2026-08-15)

Three new modules, all wired into `GaloisForLFunctions/HTGeometry.lean`, all axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`):

`HTGeometry/SpectralCollisionCovariance.lean`

- `spectralCollision e ψ = ∑_j |⟨e_j, ψ⟩|⁴` — the card object `C_H(ψ)` written against an arbitrary
  family rather than an eigenbasis;
- `finiteComplexInner_conjTranspose_mulVec` and **`spectralCollision_conjTranspose_mulVec`** —
  the unitary covariance `C_{U†HU}(ψ) = C_H(Uψ)` used by step `(23)` of
  `local-clifford-return-excised-phase-incidence-law`;
- `sum_spectralCollision_prodStab_le` — `(24)`–`(26)` in collision language:
  `∑_{σ ∈ (Fin 6)^n} C_e(φ_σ) ≤ |D| 2^n`.

`HTGeometry/BipartitePhaseSeedCollision.lean` — **Theorem B `(9)` of
`weak-cut-complexity-onset-capacity-separation-law` is closed**:

- `integral_box_normSq_trigLift_le_mul` — the general Parseval bound: if every frequency of a
  character combination is carried by at most `N` terms then the mean square is at most
  `N ∑ ‖a_p‖²`.  (This subsumes the pair count of `SteinhausFourthMoment`.)
- `prodPairFreq`, `pairFreq_inl_of_prodPairFreq`, `pairFreq_inr_of_prodPairFreq`,
  `card_filter_prodPairFreq_le` — the squared bipartite pairing has frequency
  `⟨x⟩+⟨x'⟩+⟨y⟩+⟨y'⟩`, which determines both factor pairs as *unordered* pairs, so at most four
  terms share it;
- `phaseVec`, `prodPhaseSeed`, `sum_normSq_prodPhaseSeed`;
- `integral_box_inner_phaseVec_fourth_le`, `integral_box_inner_prodPhaseSeed_fourth_le` and
  **`integral_box_sum_inner_prodPhaseSeed_fourth_le`**:
  `E_{h_A,h_B} ∑_j |⟨e_j, χ_A ⊗ χ_B⟩|⁴ ≤ 4|ι|/D²`, which at `|ι| = D` is the card's boxed `4/D`.

The paper proof factors this through `(10)`–`(12)` (a conditional `B`-pairing followed by an
`A`-pairing).  The Lean proof does the single four-fold pairing count directly on the product index,
so `(10)`–`(12)` are not separate declarations: no Fubini split of the two phase families is needed.

`HTGeometry/TorusTrigPoincare.lean` — the spectral gap of the unit torus:

- `freqBlock` and `sum_ite_freq_eq_sum_freqBlock` — every frequency-diagonal quadratic form
  regroups as a nonnegative weighted sum of squared fibre coefficients;
- `integral_box_normSq_trigLift_eq_sum_freqBlock`, `integral_box_trigLift_eq_freqBlock_zero`;
- `freqNormSq`, `one_le_freqNormSq` — a nonzero integer frequency has length at least one;
- `integral_box_normSq_pderiv_trigLift` and
  **`variance_trigLift_le_sum_integral_normSq_pderiv`** — the Poincaré inequality
  `Var f ≤ (2π)^{-2} ∑_j ∫ ‖∂_j f‖²`, which is `(12)` of
  `cubic-phase-seeded-static-local-full-scale-plateau-law`.

`HTGeometry/PhaseSeedCollisionMoments.lean` — Theorem B of the cubic-phase card, mean part:

- `uniformPhaseWeights`, `uniformPhaseSeed` — the equal-amplitude independent-phase seed as the
  phase orbit of the uniform spectral weight;
- `integral_box_fidelity_uniformPhaseSeed_pow_le` — the normalized replica moment
  `E |⟨seed, z⟩|^{2r} ≤ r!/D^r`, whose cases `r = 2, 3` are the card's `(11)` and `(14)`
  (`integral_box_fidelity_uniformPhaseSeed_sq_le`, `..._cube_le`);
- **`integral_box_phaseCollision_le`** — `E_ζ C_e(χ_ζ) ≤ 2|ι|/D²`, i.e. the mean half of the
  card's boxed `(8)` at `|ι| = D`.

Still remaining for the cubic-phase card: the variance half of `(8)` (needs `(13)`, the derivative
bound `∑_a |∂_a f|² ≤ 16 ∑_j |y_j|⁶`, and unitarity), Theorem A (Reed–Muller `RM(3,n)^⊥` minimum
weight sixteen, hence fifteen-wise independence), the finite-to-continuous moment transfer, and
Theorem C, which composes the two stage-2 parents.

### Update: the variance half of the basis-uniform collision concentration (2026-08-15)

New module `HTGeometry/PhaseSeedCollisionVariance.lean` (wired, axiom-clean).  This closes the
second half of `(8)` of `cubic-phase-seeded-static-local-full-scale-plateau-law`, i.e. the Poincaré
chain `(12)`--`(14)` of that card, in unnormalized form.

- `pderiv_mul_of_hasFDerivAt`, `pderiv_finsetSum_of_hasFDerivAt` — product and sum rules for the
  coordinate derivative on the phase box;
- `phaseAmp`, `phaseAmpConj` — the pairing `y_j = ⟨seed, e_j⟩` and its conjugate, each a character
  combination, with `pderiv_phaseAmp`, `pderiv_phaseAmpConj`;
- `quarticSum`, `quarticFreq`, `quarticCoeff`, **`quarticSum_eq_trigLift`** — the collision
  `f = ∑_j |y_j|⁴` *is* a character combination, so the torus spectral gap applies to it;
- **`pderiv_quarticSum`** — the card's `(13)` in exact form:
  `∂_b f = 4πi (v_b − conj v_b)` with `v_b = ζ_b ∑_j |y_j|² y_j conj(e_j b)`;
- `sum_normSq_dual` — orthonormality turns `∑_b |v_b|²` into `∑_j |y_j|⁶`, the card's unitarity
  step;
- `sum_normSq_pderiv_quarticSum_le` — `∑_b |∂_b f|² ≤ 64π² ∑_j |y_j|⁶`;
- **`integral_box_variance_collision_le`** — `Var f ≤ 96 |ι|`, which after the `D⁻²` seed
  normalization is the card's `Var C ≤ 96/D³` at `|ι| = D`.

The sixth moment `(14)` enters as `integral_box_fidelity_pow_le` at `r = 3`, i.e. `E|y_j|⁶ ≤ 3!`.

Also repaired this session: nine of the torus modules opened with *anonymous* `local instance`
declarations for the `UnitAddCircle` measure space, which Lean auto-names identically whenever the
imported environments agree.  Any file importing two of them failed with "environment already
contains …", so the `HTGeometry` umbrella could not build even though every module passed
`lake env lean` and its own `lake build`.  All of them now carry explicit per-module instance
names, and a scratch file importing all fifteen session modules at once compiles.

### Update: the measurable spectral collision and its ensemble law (2026-08-15)

Two new modules, wired and axiom-clean.  Together they remove the obstruction that had blocked
`(21)`/`(26)` of `local-clifford-return-excised-phase-incidence-law`: an eigenbasis is not a
measurable function of the matrix, so `Pr_H{C_H(Ω) > …}` was not even a statement about a
measurable set.

`HTGeometry/SpectralCollisionFunctional.lean`

- `IsOrthoEigenBasis H e lam` — orthonormal eigenbasis with real eigenvalues, together with
  **`exists_isOrthoEigenBasis`**: every Hermitian matrix has one, so the eigenbasis input is never
  a restriction;
- `stateMoment H ψ r = ⟨ψ, Hʳψ⟩` and `stateMoment_eq` — the moment is `∑_j p_j λ_jʳ`;
- `regCollisionC`, **`regCollisionC_eq`** — the binomially expanded gap regularization equals
  `∑_{j,k} p_j p_k (1 − (λ_j−λ_k)²/c)^m`, so it is simultaneously a polynomial in the matrix
  entries and a spectral gap weight;
- `capC H = 1 + 4‖H‖_F²`, `sq_gap_lt_capC` — a continuous cap dominating every squared gap;
- `cappedRegCollision`, **`continuous_cappedRegCollision`**,
  `sum_eigenWeight_sq_le_cappedRegCollision` (it dominates the collision at every order) and
  **`tendsto_cappedRegCollision`** (it converges to the collision at a simple spectrum).

`HTGeometry/CollisionEnsembleLaw.lean`

- `sum_eigenWeight_eq` (Parseval), `spectralCollision_le_one`, `cappedRegCollision_le_one`;
- **`isOrthoEigenBasis_conj`** — unitary conjugation transports an eigenbasis and preserves the
  eigenvalues;
- **`spectralCollision_eq_of_isOrthoEigenBasis`** — at a simple spectrum the collision does not
  depend on the eigenbasis, because both eigenbases compute the same limit;
- **`spectralCollision_conj_eq`** — the card's `C_{U†HU}(ψ) = C_H(Uψ)` in eigenbasis form;
- `measurable_cappedRegCollision_comp`, **`aemeasurable_spectralCollision`** — for a family with
  entrywise measurable matrix and almost surely simple spectrum, the collision is a.e. measurable;
- `integrable_spectralCollision`;
- **`measureReal_spectralCollision_ge_le`** — the card's `(21)` in abstract form:
  `Pr{C ≥ L c₀} ≤ 1/L` whenever the mean collision is at most `c₀`;
- **`integral_spectralCollision_conj_eq`** — the card's `(23)` in abstract form: if a
  measure-preserving reparametrization carries the family onto its conjugate by `U`, the mean
  collision at `ψ` equals the mean collision at `Uψ`.

**Remaining for `local-clifford-return-excised-phase-incidence-law`:** instantiate
`integral_spectralCollision_conj_eq` at the fixed-weight Pauli Gaussian ensemble — the signed
permutation of Pauli labels induced by a product Clifford, and the invariance of the product
Gaussian law under it — then combine with `sum_spectralCollision_prodStab_le` to get `(26)` and
with `measureReal_spectralCollision_ge_le` to get `(21)`; `(27)` is already carried by the corpus
(`twoLocal_projectivelyIndependent_ae`, `pauliTraceless_projectivelyIndependent_ae`); `(28)` needs
the completed-time transfer, and `(29)`--`(33)` are arithmetic bookkeeping on top of `(22)`.

### Promotion update: source-test partition universality (2026-08-15)

| Card | New Lean work | Modules |
|---|---|---|
| `source-test-partition-universality` | none (re-audited); exact quotient recognizer with deterministic, exhaustive, and observationally exact presentation | `HTGeometry/SourceTestPartitionUniversality` (re-audited) |

### Update: sitewise product action and decoupled evolution (2026-08-15)

`HTGeometry/LocalProductStateAction.lean` (wired, axiom-clean)

- `localProductState w x = ∏_s w s (x s)`;
- **`finiteLocalMatrix_mulVec_localProductState`** — a matrix that factors over the qubits acts on
  a product state one qubit at a time (the distributive law `Finset.prod_univ_sum`);
- `sum_normSq_localProductState` — the squared length of a product state factors.

This is the vector-side companion of the corpus's `finiteLocalMatrix` algebra
(`FinitePauliConjugationLaw`), needed to identify a product Clifford image of `|0…0⟩` with a
product stabilizer state.

`HTGeometry/DecoupledEvolutionFactorization.lean` (wired, axiom-clean) — **this closes the last
mechanism of Theorem A of `weak-cut-complexity-onset-capacity-separation-law`, equation `(8)`**:

- `kroneckerRightHom`, `kroneckerLeftHom` — tensoring with the identity is a ring homomorphism,
  with `kroneckerRightLinear`/`kroneckerLeftLinear` giving continuity in finite dimension;
- `exp_kronecker_one`, `exp_one_kronecker` — a continuous ring homomorphism commutes with the
  exponential;
- `commute_kronecker_one_one_kronecker`, **`exp_kroneckerSum`** —
  `exp(A ⊗ 1 + 1 ⊗ B) = exp A ⊗ exp B`;
- **`unitaryEvolution_kroneckerSum`** and
  **`unitaryEvolution_kroneckerSum_mulVec_tensorVec`** — the card's `(8)`,
  `e^{-itH₀}(χ_A ⊗ χ_B) = (e^{-itH_A}χ_A) ⊗ (e^{-itH_B}χ_B)`.

**State of `weak-cut-complexity-onset-capacity-separation-law`:** Theorem A is closed
(`(3)`,`(4)`,`(6)`,`(7)`,`(8)`); Theorem B `(9)` is closed.  Theorem C composes the two stage-2
parents `cubic-phase-seeded-…` and (through them) `local-clifford-…`, so it waits on those.
Theorems D and E still need the Pauli Hilbert–Schmidt/operator-norm comparison `(19)`,`(21)`, the
contiguous-cut union sandwich `(23)` (structurally unconditional once the norms are in), and the
beta projection law `(17)`--`(18)` — for which the card explicitly allows an explicit sphere-tube
lower bound instead.

**Corpus assets located for the remaining local-Clifford construction:**
`TwoReplicaGlobalCliffordHallSymmetryReduction.finiteProductCliffordGate` with
`finiteProductCliffordGate_unitary` and **`finiteProductCliffordGate_conj_finitePauliMatrix`**
(conjugation sends a Pauli word to a scalar times another Pauli word *of the same weight*, which is
exactly the label permutation preserving the two-local support);
`FinitePauliConjugationLaw.finiteLocalMatrix`, `finitePauliConjugationSign`,
`finitePauliConjugationSign_sq`; the vendored `QuantumAlg.…QubitTwoDesign` (`BinaryOctahedral`,
card 48, quaternion model) and `QuantumAlg.…ProductClifford` (`productQubitClifford`,
`productQubitClifford_unitary`, `productQubitClifford_twirl_singleSite`), the latter already
indexed by `Fin 2` like `StabilizerTwoDesign.prodStabAmp`.

### Promotion update: finite squarefree Euler complement rigidity (2026-08-15)

| Card | New Lean work | Modules |
|---|---|---|
| `finite-squarefree-euler-complement-rigidity` | literal complex FE sampled at all negative integers; distinct-squarefree Vandermonde coefficient recovery; exact local-square/epsilon classification; literal FE converse; zero-line theorem | `RHTower/FiniteSquarefreeEulerFunctionalEquation` (new), `RHTower/FiniteSquarefreeEulerComplementRigidity` (reused core) |

Moved `2-fully-proven/not_new_scientific_knowledge/finite-squarefree-euler-complement-rigidity.md`
to `3-formalized/not_new_scientific_knowledge/` with companion
`finite-squarefree-euler-complement-rigidity-formalized.md`. Direct source check and focused leaf
build passed; capstone axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.
The `RHTower` umbrella import is wired; no umbrella build was run. The inbound-link scan found no
external reference to the old Stage-2 path (this ledger is its sole historical mention).

### Update: Hilbert–Schmidt size of a Pauli combination (2026-08-15)

`HTGeometry/PauliHilbertSchmidtNorm.lean` (wired, axiom-clean) — the first half of `(21)` of
`weak-cut-complexity-onset-capacity-separation-law`:

- `ofReal_frobSq_eq_trace` — the squared Hilbert–Schmidt size is `tr(M* M)`;
- **`frobSq_pauliCombination`** — `‖∑_P J_P P‖_HS² = 2^{|σ|} ∑_P |J_P|²`, using the corpus
  orthogonality `trace_star_finitePauliMatrix_mul`.  On a two-qubit edge (`|σ| = 2`) this is the
  card's `‖V_e‖_HS = 2ρ_e`.

Still open for `(21)`: the operator-norm sandwich `ρ_e ≤ ‖V_e‖₂ ≤ 3ρ_e`, which needs
`‖P‖₂ ≤ 1` for a Pauli word (unitary, via `finitePauliMatrix_mul_self`) for the upper bound and
`‖M‖_HS² ≤ (dim) ‖M‖₂²` for the lower bound; then `(22)`--`(23)` are the union sandwich.

### Promotion update: event topological-debt conservation (2026-08-15)

| Card | New Lean work | Modules |
|---|---|---|
| `event-topological-debt-conservation` | none (re-audited); exact arbitrary-additive-group conservation, same-parent rigidity, finite telescope, and closed-history zero debt | `HTGeometry/EventTopologicalDebt` (re-audited) |

Moved `2-fully-proven/not_new_scientific_knowledge/event-topological-debt-conservation.md` to
`3-formalized/not_new_scientific_knowledge/` with its Lean certificate. Direct source check and
focused leaf build passed; capstone axiom audit contains only `propext`, `Classical.choice`, and
`Quot.sound`. The `HTGeometry` import was already wired; no umbrella build was run. Two inbound
card links were repointed, and no stale direct Stage-2 link remains.

### Update: the Pauli operator-norm sandwich (2026-08-15)

`HTGeometry/PauliOperatorNormSandwich.lean` (wired, axiom-clean) — **this closes `(19)` and `(21)`
of `weak-cut-complexity-onset-capacity-separation-law`**:

- `sum_normSq_column_le_opNorm_sq`, **`frobSq_le_card_mul_opNorm_sq`** — `‖M‖_HS² ≤ dim ‖M‖₂²`;
- `finitePauliMatrix_mem_unitary`, **`norm_finitePauliMatrix`** — every Pauli word is unitary and
  has operator norm one;
- **`opNorm_pauliCombination_le`** and **`opNorm_pauliCombination_le_sqrt_card`** — the card's
  `(19)`: `‖V_e‖₂ ≤ ∑|J| ≤ √|S| ρ_e`, which at the nine two-site orientations is `3ρ_e`;
- **`le_opNorm_pauliCombination`** — the card's lower half `ρ_e ≤ ‖V_e‖₂`, from
  `frobSq_pauliCombination` (`‖V_e‖_HS = 2ρ_e` at a two-qubit edge) and the dimension bound.

Remaining for Theorems D/E of that card: the contiguous-cut union sandwich `(22)`--`(23)`, which is
now purely a probability statement over the edges (a single-edge lower bound plus a union bound),
and the beta projection law `(17)`--`(18)`, for which the card explicitly permits an explicit
sphere-tube lower bound in place of the exact beta distribution function.

### Promotion update: canonical event-slice weak-order collapse (2026-08-15)

| Card | New Lean work | Modules |
|---|---|---|
| `canonical-event-slice-weak-order-collapse` | finite maximal-antichain extension and exact finite iff; equivalence, canonical-class, and representative-independent class-order consequences | `HTGeometry/CanonicalEventSlice` (extended and re-audited) |

Moved `2-fully-proven/not_new_scientific_knowledge/canonical-event-slice-weak-order-collapse.md`
to `3-formalized/not_new_scientific_knowledge/` with its Lean certificate. Direct source check and
focused leaf build passed; the expanded capstone audit contains only `propext`, `Classical.choice`,
and `Quot.sound` (the equivalence theorem is axiom-free). The existing `HTGeometry` umbrella import
remained in place; no umbrella build was run. The parent paper and formalization links were repointed.

### Update: the contiguous-cut sandwich and the delay floor mechanism (2026-08-15)

`HTGeometry/CutConductanceUnionSandwich.lean` (wired) — **the card's `(22)`--`(23)`**:

- `cutConductance nrm θ = min_e ‖V_e(θ)‖` with `cutConductance_le` and
  `exists_le_of_cutConductance_le`;
- `subset_setOf_cutConductance_le`, `setOf_cutConductance_le_subset` — one small block forces a
  small conductance, and a small conductance forces some small block;
- **`measure_cutConductance_sandwich`** — `μ{ρ_{e₀} ≤ x/3} ≤ μ{g_path ≤ x} ≤ ∑_e μ{ρ_e ≤ x}`, with
  no independence between edges, exactly as the card states;
- `blockRadius`, `blockMatrix`, `blockRadius_le_norm_blockMatrix`, `norm_blockMatrix_le` and
  **`measure_cutConductance_pauliBlocks_sandwich`** — the same sandwich for the nine-orientation
  two-site Pauli block, where the factor three is `√9`.

`HTGeometry/WeakCutDelayFloor.lean` (wired) —
**`approxComplexity_le_of_blockRadius_le`**: if the edge coefficient length is at most
`(ε − η)/(3L)` then the interacting orbit stays inside the split-system synthesis cap for every
`|t| ≤ L`.  This is the exact mechanism of `(20)`: the delay event contains the small-block event,
so `Pr{T_full > L} ≥ Pr{ρ_{e₀} ≤ (ε−η)/(3L)}`.

**State of `weak-cut-complexity-onset-capacity-separation-law`:** Theorem A closed; Theorem B `(9)`
closed; Theorem E `(21)`--`(23)` closed; Theorem D closed except the *evaluation* of
`Pr{ρ_e ≤ x}` — the reduction `(19)`--`(20)` is done, and only the beta projection law `(17)`--`(18)`
(or the sphere-tube lower bound the card permits instead) remains.  Theorem C still composes the
two stage-2 parents.

### Promotion update: global actuality-wall cocycle flatness (2026-08-15)

| Card | New Lean work | Modules |
|---|---|---|
| `global-actuality-wall-cocycle-flatness` | literal wall-indistinguishability Setoid quotient, injective quotient-profile embedding, and basepoint translation | `HTGeometry/ActualityWallFlatness` (extended and re-audited) |

Moved `2-fully-proven/not_new_scientific_knowledge/global-actuality-wall-cocycle-flatness.md`
to `3-formalized/not_new_scientific_knowledge/` with its Lean certificate. Direct source check and
focused leaf build passed; capstone axioms are limited to `propext` and `Quot.sound` (the global
closed-walk flatness theorem is axiom-free). The existing `HTGeometry` import was retained; no
umbrella build was run. The parent paper and formalization links were repointed.

### Update: equation `(23)` is closed at the concrete Pauli Gaussian ensemble (2026-08-15)

Three new modules, wired, built, axiom-clean.

`HTGeometry/GaussianSignedPermutationInvariance.lean`

- `centredProductGaussian ι v = Measure.pi fun _ => gaussianReal 0 v`, a probability measure;
- `gaussianReal_map_neg` — a centred Gaussian is invariant under sign reversal;
- `measurePreserving_signFlip`, `measurePreserving_permMap` and
  **`measurePreserving_signedPerm`** — every signed permutation of coordinates preserves the
  centred product Gaussian.

`HTGeometry/ProductCliffordLabelAction.lean`

- `qubitCliffordRelabel`, `qubitCliffordPhase` — the sitewise Pauli relabelling and phase chosen
  once from `exists_booleanQubitClifford_conj_boolPauliOption`;
- `productCliffordRelabel`, `productCliffordPhase`, **`productCliffordRelabel_none_iff`** (the
  relabelling preserves the support of every label, sitewise — strictly stronger than the weight
  preservation the corpus previously exposed);
- **`finiteProductCliffordGate_conj_finitePauliMatrix_relabel`** — the conjugation identity with the
  relabelling as a *function* of the label rather than an existential;
- **`productCliffordPhase_sq`**, `productCliffordPhase_eq_one_or_neg_one` — the phase is a sign,
  because conjugation of an involution is an involution;
- **`productCliffordRelabel_injective`** (via `finitePauliMatrix_linearIndependent`) and
  `productCliffordRelabelEquiv`, the relabelling as a permutation of labels.

`HTGeometry/PauliEnsembleCliffordCovariance.lean`

- `SupportInvariantWeight` — weights depending only on the support, as in the card's `σ_S`;
- `pauliEnsemble w J = ∑_P (w_P J_P) P` and `cliffordCoefficientMap`;
- **`pauliEnsemble_conj`** — conjugating the ensemble by a product Clifford is exactly applying
  the induced signed permutation to the coefficients;
- **`measurePreserving_cliffordCoefficientMap`** — that signed permutation preserves the centred
  product Gaussian;
- `measurable_pauliEnsemble_entry`;
- **`integral_spectralCollision_pauliEnsemble_clifford_eq`** — the card's `(23)`:
  `E_H C_H(C_g† Ω) = E_H C_H(Ω)` for every product Clifford `g`, unconditionally.

**What `(26)` still needs:** the pointwise average bound over the Clifford orbit of `|0…0⟩`.  The
corpus already proves `sum_spectralCollision_prodStab_le` — `∑_{σ ∈ (Fin 6)^n} C_e(φ_σ) ≤ |D| 2^n`,
i.e. average `≤ (2/3)^n` — for the *product stabilizer amplitudes* `prodStabAmp`, indexed by
`Fin n → Fin 2`.  The gap is the identification of the Clifford orbit `{C_g† |0…0⟩}` with those
amplitudes: an index bridge `Fin 2 ≃ Bool` plus, for each of the six single-qubit stabilizer
states, one `BinaryOctahedral` element carrying `|0⟩` to it up to phase.  `LocalProductStateAction`
supplies the sitewise action needed for that identification; the alternative route is the corpus's
two-replica product-Clifford twirl (`TwoReplicaGlobalCliffordTwirlRange`).

### Update: the six stabilizer states are an explicit Clifford orbit (2026-08-15)

`HTGeometry/StabilizerCliffordOrbit.lean` (wired, built, axiom-clean):

- `boolZeroState`, `boolStabAmp t b = stabAmp rt2inv t (if b then 1 else 0)` — the six single-qubit
  stabilizer amplitudes over `Bool`, at the amplitude `rt2inv` for which `s² = 1/2` and `s̄ = s`,
  exactly the hypotheses of `sum_stabAmp_four`;
- `mulVec_boolZeroState` — acting on the computational zero reads off the first column;
- `stabClifford : Fin 6 → BinaryOctahedral := ![1, Vₓ², V_y⁻¹, V_y, Vₓ, Vₓ⁻¹]` built from
  `cliffordQuarterTurnCode`, with `booleanQubitClifford_quarterTurn_inv_matrix` giving
  `V⁻¹ = 2^{-1/2}(1 − iP)`;
- `stabClifford_mulVec_zero` … `stabClifford_mulVec_five` and
  **`booleanQubitClifford_stabClifford_mulVec`**: for every `t` there is a unit phase `c` with
  `C_{stabClifford t} |0⟩ = c · φ_t`.

This is the last *mathematical* input for `(26)`; what remains is bookkeeping:

1. the product statement `C_{g_σ}|0…0⟩ = (∏ c) · φ_σ`, from
   `finiteLocalMatrix_mulVec_localProductState` (already proved) plus
   `finiteProductCliffordGate = finiteLocalMatrix ∘ booleanQubitClifford`;
2. phase invariance of `spectralCollision` under a unit scalar;
3. the index transport of `sum_spectralCollision_prodStab_le` from `Fin n → Fin 2` to
   `σ → Bool` along `b ↦ if b then 1 else 0`;
4. averaging `integral_spectralCollision_pauliEnsemble_clifford_eq` over the `6ⁿ` choices of `σ`
   and applying `measureReal_spectralCollision_ge_le`, giving `(26)` and then `(21)`.

### Update: equations `(21)`, `(25)`, `(26)` of the local-Clifford card are closed (2026-08-15)

Three further modules, wired, built, axiom-clean.

`HTGeometry/ProductStabilizerCliffordOrbit.lean`

- `zeroProductState`, `prodBoolStabAmp`, `localProductState_smul`;
- **`finiteProductCliffordGate_stabClifford_mulVec`** — the product stabilizer states are exactly
  the product-Clifford images of the all-zero state, each up to a unit phase;
- `spectralCollision_smul` (phase invariance), `spectralCollision_comp_equiv` and
  `sum_normSq_comp_equiv` (index-bijection invariance);
- `boolFin2Equiv`, `configEquiv`, `prodBoolStabAmp_eq` — the `Bool`/`Fin 2` bridge.

`HTGeometry/CliffordOrbitCollisionBound.lean`

- `normSq_rt2inv`, `sum_normSq_boolStabAmp`, `sum_normSq_prodBoolStabAmp`;
- **`sum_spectralCollision_cliffordOrbit_le`** — the card's `(25)` on the orbit:
  `∑_{τ ∈ (Fin 6)ⁿ} C_e(C_τ|0…0⟩) ≤ |D| 2ⁿ`.

`HTGeometry/CliffordEnsembleCollisionMean.lean`

- `sum_normSq_zeroProductState`, `sum_normSq_cliffordOrbitState`;
- **`integral_spectralCollision_zeroProductState_le`** — the card's boxed **`(26)`**:
  `E_H C_H(Ω) ≤ (2/3)ⁿ` for the centred Pauli Gaussian ensemble with support-invariant weights,
  unconditionally;
- **`measureReal_spectralCollision_zeroProductState_ge_le`** — the card's boxed **`(21)`**:
  `Pr_H{C_H(Ω) ≥ L(2/3)ⁿ} ≤ 1/L`.

**State of `local-clifford-return-excised-phase-incidence-law`:** `(1)`–`(19)` closed (with the
sharp constant), `(21)`, `(23)`, `(24)`, `(25)`, `(26)` closed.  Remaining: `(22)` (arithmetic
composition of `(5)` with `(21)`), `(27)` (discharge the almost-sure simple-spectrum hypothesis
`hae` from the corpus genericity `pauliTraceless_projectivelyIndependent_ae` /
`twoLocal_projectivelyIndependent_ae`, plus Krylov cyclicity), `(28)` (completed-time transfer),
and `(29)`–`(33)` (finite-alphabet circuit counting).

### Promotion update: dyadic-prime Dirichlet high-line sign rigidity (2026-08-15)

| Card | New Lean work | Modules |
|---|---|---|
| `dyadic-prime-dirichlet-high-line-sign-rigidity` | raw-impedance tail witnesses/no-gos and a universal phase-selection capstone for every first nonzero real Dirichlet coefficient | `HTGeometry/DirichletHalfPlaneSignRigidity` (extended), `RHTower/CCMSharpPrimeWindowPassiveNoGo` (re-audited) |

Moved `2-fully-proven/not_new_scientific_knowledge/dyadic-prime-dirichlet-high-line-sign-rigidity.md`
to `3-formalized/not_new_scientific_knowledge/` with its Lean certificate.  Direct generic source
check and focused Route-I leaf build passed after the phase extension.  The exact generic capstone
`realLSeriesRawImpedance_not_fixedSign_of_firstNonzero` and the literal dyadic endpoint depend
only on `propext`, `Classical.choice`, and `Quot.sound`.  Both existing umbrella imports remained
wired; no umbrella build was run.  No stale inbound Stage-2 link remains.

### Promotion update: dyadic-prime completed passive transfer to horizontal Xi growth (2026-08-15)

| Card | New Lean work | Modules |
|---|---|---|
| `dyadic-prime-completed-passive-transfer-to-horizontal-xi-growth` | none (re-audited); literal source normalization, completed-Xi coordinate identification, RH equivalence, horizontal-bound strictness, and real Möbius closure | `RHTower/CCMSharpPrimeWindowCompletedPassiveTransfer`, `CCMSharpPrimeWindowMobiusPassiveNoGo` (re-audited) |

Moved `2-fully-proven/not_new_scientific_knowledge/dyadic-prime-completed-passive-transfer-to-horizontal-xi-growth.md`
to `3-formalized/not_new_scientific_knowledge/` with its Lean certificate.  Direct source check
and focused final completed-transfer leaf build passed.  Every audited endpoint depends only on
`propext`, `Classical.choice`, and `Quot.sound`; no forbidden declaration occurs in either leaf.
The existing `RHTower` imports were retained, no umbrella build was run, and the failed-route
inbound link was repointed.

### Update: equation `(22)` and the eigenbasis existence for the ensemble (2026-08-15)

`HTGeometry/ReturnExcisedCollisionBoundedIncidence.lean` (wired, built, axiom-clean) — the card's
boxed **`(22)`**:

- **`measureReal_capture_le_return_add_replicaMoment_of_collision_le`** — the return-excised
  complete-target bound `(5)` with any upper bound substituted for the spectral collision, since
  the estimate is monotone in it.  At `c₀ = L(2/3)ⁿ` (from `(21)`) this is exactly `(22)`.

Added to `HTGeometry/CliffordEnsembleCollisionMean.lean`:

- `isHermitian_pauliEnsemble` and **`exists_isOrthoEigenBasis_pauliEnsemble`** — every member of
  the weighted Pauli ensemble is Hermitian and therefore carries an orthonormal eigenbasis, so the
  existence half of the `hae` hypothesis is discharged for every coefficient vector.

**What `(27)` still needs:** the *almost-sure injectivity* of the eigenvalues for the Gaussian
coefficient law.  The corpus proves exactly this for its own parametrization —
`PauliTwoLocalEmbedding.pauliTraceless_projectivelyIndependent_ae (n) (hq : 2 ≤ q) (hμ : μ ≪ volume)`
gives `∀ᵐ p ∂μ, Function.Injective (isHermitian_pauliTracelessFinEval p).eigenvalues ∧
MaximallyProjectiveEnergy …` — so the remaining work is the parametrization bridge: identify
`pauliEnsemble w J` with `pauliTracelessFinEval` at the reindexed coefficients (for `w` supported
on the nonidentity labels of weight at most `q`) and check that the pushforward of
`centredProductGaussian` under that affine reindexing is absolutely continuous, which
`PiMeasureAbsoluteContinuity.productGaussian_absolutelyContinuous` supplies.
