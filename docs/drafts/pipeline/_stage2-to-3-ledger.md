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
| `disconnected-local-spectral-factorization-genericity` | none (already complete in the hypergraph form) | `HTGeometry/DisconnectedProjectiveGapModuleLaw`, `HypergraphComponentFactorization`, `HypergraphProjectiveSpectralFactorization`, `BlockSumSpectralGenericity` |

| `burnol-divided-shift-evaluation-separation-law` | none (verified only) | `RHTower/BurnolDividedShiftEvaluationSeparation` |
| `burnol-holonomy-cauchy-sector-separation` | none (verified only) | `RHTower/BurnolHolonomyCauchySectorSeparation` |
| `burnol-all-prime-completion-singular-potential-entrance-wall` | all of `(AW0)`--`(AW17)` | `RHTower/BurnolAllPrimeCompletionWall`, `RHTower/BurnolPrimeLogSummability` (both new) |
| `burnol-all-prime-window-hilbert-cartier-jet-wall` | all of `(HJ1)`--`(HJ29)` | `RHTower/BurnolAllPrimeWindowEnergy`, `RHTower/BurnolReciprocalStokesSewing` (both new) |
| `burnol-poisson-subordinate-smooth-cartier-entrance-wall` | all of `(PS1)`--`(PS16)`, incl. the Glasser integral | `RHTower/BurnolPoissonSubordinateWall`, `RHTower/BurnolGlasserIntegral` (both new) |

## New reusable infrastructure built during the sweep

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

`two-replica-singlet-pauli-hall-expansion` — remaining: reverse inclusion of `(12)`, global tensor
form of `(11)`, and the assembly `(14)`–`(17)` into
`HTGeometry.resolvedFiberAssembly_subspace_finrank` (interface already exists and is exactly
shaped for it).

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
- `two-replica-singlet-pauli-hall-expansion` — three named maps into
  `resolvedFiberAssembly_subspace_finrank`.
- `weak-interaction-singular-quantum-time-expansion` — `(7)`'s finite-family Hausdorff assembly,
  plus Theorem C/C2 of the card above.

## Known deep external dependencies (attack last, expect long builds)

- `route-e-cofactor-amplified-e3-token-supply`, `route-e-forbidden-support-e3-stability` —
  Matomäki–Teräväinen all-interval `E₃` theorem.  Not in mathlib, not in the corpus.
- `mass-bessel-cofinal-radiation-divergence`, `mass-bessel-infinite-radiation-jet-obstruction` —
  uniform sectorial large-argument asymptotics for `K₁` (the card itself prescribes replacing `K₁`
  by its Fourier integral `∫ e^{-ixξ} e^{-t√(ξ²+a²)} dξ` and proving deep-time Laplace asymptotics).
  Corpus owns a Schlaefli-integral Bessel layer (`HTGeometry/BesselOrder*.lean`).
- `one-replica-local-pauli-planar-cavity-decay` — operator-valued semicircle theorem.
- `algebraic-two-local-instant-exact-complexity` — rational Hilbert specialization and
  transcendence-degree layers above `RHTower/FiniteLindemannWeierstrass.lean`.

## Remaining

Everything still listed by `ls docs/drafts/pipeline/2-fully-proven/*.md`.
