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

| `burnol-divided-shift-evaluation-separation-law` | none (verified only) | `RHTower/BurnolDividedShiftEvaluationSeparation` |
| `burnol-holonomy-cauchy-sector-separation` | none (verified only) | `RHTower/BurnolHolonomyCauchySectorSeparation` |
| `burnol-all-prime-completion-singular-potential-entrance-wall` | all of `(AW0)`--`(AW17)` | `RHTower/BurnolAllPrimeCompletionWall`, `RHTower/BurnolPrimeLogSummability` (both new) |
| `burnol-all-prime-window-hilbert-cartier-jet-wall` | all of `(HJ1)`--`(HJ29)` | `RHTower/BurnolAllPrimeWindowEnergy`, `RHTower/BurnolReciprocalStokesSewing` (both new) |
| `burnol-poisson-subordinate-smooth-cartier-entrance-wall` | all of `(PS1)`--`(PS16)`, incl. the Glasser integral | `RHTower/BurnolPoissonSubordinateWall`, `RHTower/BurnolGlasserIntegral` (both new) |
| `burnol-first-wall-cartier-residue-cancellation-law` | *(in progress)* `(1)`, `(2)`, `(4)`, `(8)`--`(11 fwd)`, `(13)`--`(23 fwd)`, `(24)`--`(28)`, `(29 fwd, pointwise)` | `RHTower/BurnolFirstWallZeroDividedSource`, `RHTower/BurnolFirstWallSourceDecay`, `RHTower/BurnolFirstWallSourceMass`, `RHTower/BurnolFirstWallExteriorMass`, `RHTower/BurnolFirstWallCrossingCorrelation`, `RHTower/BurnolReflectedRawSource`, `RHTower/BurnolReflectedDividedShift` (all new) |
| `burnol-gamma-bockstein-first-wall-extraction-law` | all of `(1)`--`(22)` | `RHTower/BurnolBocksteinLimit` (new), `RHTower/BurnolFirstWallCrossingCorrelation`, `RHTower/BurnolReflectedPotential`, `RHTower/BurnolGammaStein*`, `RHTower/BurnolDyadicCommutatorStaircase` |
| `burnol-cofinite-cartier-wall-trace-horizon` | all of `(CH1)`--`(CH23)` | `RHTower/BurnolCofiniteHorizonGerm` (new), `RHTower/BurnolPrimeCartierWallTrace` |
| `burnol-prime-two-causal-cartier-collar-law` | all of `(3)`--`(25)` | `RHTower/BurnolGammaSteinCollarKernel`, `RHTower/BurnolGammaSteinMoments`, `RHTower/BurnolCollarKernelSeries`, `RHTower/BurnolPrimeTwoCollarSymbol` (all new) |

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
- `one-replica-local-pauli-planar-cavity-decay` — operator-valued semicircle theorem.
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
- `one-replica-local-pauli-planar-cavity-decay` — operator-valued semicircle theorem.
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
