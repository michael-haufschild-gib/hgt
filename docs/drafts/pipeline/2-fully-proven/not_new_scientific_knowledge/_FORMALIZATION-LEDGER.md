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
3. **Hadamard factorization for finite-order entire functions** (zero-free ⇒ `exp(polynomial)`):
   needed by `involutive-reflection-quadratic-rigidity`.
4. **von Neumann algebra generation** (`W*(S)` for a set of operators, and
   `W*(D, H_x) = B(ℓ²)`): needed by `additive-heat-diagonal-generates-full-operator-algebra`.
   mathlib has `VonNeumannAlgebra` but no generated-algebra API.
5. **Derived inverse limits** (`R lim` of a diagram of zero objects): needed by
   `acyclic-finite-fibers-derived-limit-zero`.
6. **Complex-dynamics layer** (Böttcher coordinate, equilibrium measure of a Cantor Julia set,
   winding-number integration): needed by the three `bottcher-*` monodromy cards.

## New reusable infrastructure added by this sweep

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

- entire-function **order** (`EntireFiniteOrder` exists in `RHTower/SelbergClass/`;
  `xi_growth_order_le_one` is proved) — needed by the `finite-*-rh-nonselection` family
  (`finite-seam-jet-rh-nonselection`, `finite-linear-probe-rh-nonselection`, …).
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
